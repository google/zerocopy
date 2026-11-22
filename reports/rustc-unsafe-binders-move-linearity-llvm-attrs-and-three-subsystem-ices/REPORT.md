# `rustc` `unsafe_binders`: Move-Only Linearity (`!Copy`), `8 B` `Option` Null Niche, Four-Tier LLVM Attribute Stripping, Compound-Binder Attribute Leakage, and Three Live Compiler ICEs

## Summary

`rustc`'s unstable `unsafe_binders` feature (`#![feature(unsafe_binders)]`, tracking issue `#130516`) introduces a higher-ranked lifetime-erasing type constructor `TyKind::UnsafeBinder(UnsafeBinderInner<I>)` (`unsafe<'a> T`) together with two dedicated MIR constructs: `Rvalue::WrapUnsafeBinder(Operand<'tcx>, Ty<'tcx>)` (surfaced as `core::unsafe_binder::wrap_binder!`) and `ProjectionElem::UnwrapUnsafeBinder(T)` (surfaced as `core::unsafe_binder::unwrap_binder!`). Primary-source inspection across `rust-lang/rust` revisions `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`, LLVM `22.1.6`), `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`, LLVM `23.1.5`), and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`main` HEAD, `2026-11-22`), combined with live `rustc`/LLVM/Miri execution (`support/probe_unsafe_binders_and_ices.py`) and a zero-`sorry`, `Classical.choice`-free Lean `v4.34.1` formalization (`support/UnsafeBinderExistentialRegionSoundness.lean`), establishes seven load-bearing architectural facts:

1. **Bidirectional `E0133` `unsafe` Gating:** Both wrapping (`wrap_binder!`) and unwrapping (`unwrap_binder!`, in both value and place contexts) emit `UnsafeOpKind::UnsafeBinderCast` in `compiler/rustc_mir_build/src/check_unsafety.rs:611-615`, rejecting bare calls outside `unsafe` with `error[E0133]`.
2. **Move-Only Linearity (`!Copy`, `!Clone`) and `BikeshedGuaranteedNoDrop` Nesting Rejection:** Both the legacy trait solver (`compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:1173-1175`) and the next-generation trait solver (`compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs:258`) withhold `Copy` and `Clone` from `TyKind::UnsafeBinder` even when the wrapped type is `&'a u64: Copy`, yielding `E0277` on `T: Copy`/`T: Clone` bounds and `E0382` on duplicate moves, while propagating `Sized` (`structural_traits.rs:162`) and auto traits `Send`/`Sync` (`structural_traits.rs:99`). Because `unsafe<'a> T` enforces `BikeshedGuaranteedNoDrop` on `T` (`trait_goals.rs:738-822`) and `BikeshedGuaranteedNoDrop` reduces `TyKind::UnsafeBinder` to `Copy` (`trait_goals.rs:797-809`), direct nesting `unsafe<'a> unsafe<'b> &'a &'b u64` is rejected with `E0277`, whereas `unsafe<'a> ManuallyDrop<unsafe<'b> &'a &'b u64>` compiles cleanly.
3. **Layout Transparency and `8`-Byte `Option` Null-Niche Retention:** `compiler/rustc_ty_utils/src/layout.rs:861-864` computes the layout of `ty::UnsafeBinder(bound_ty)` by erasing bound regions and copying the inner `LayoutData` verbatim (`BackendRepr::Scalar(Scalar::Initialized { value: Pointer(..), valid_range: 1..=usize::MAX })` and `largest_niche`). Consequently, on 64-bit targets `Option<unsafe<'a> &'a u64>` and `Option<unsafe<'a> &'a mut u64>` both retain the null-pointer niche (`OPT_SHARED = 8`, `OPT_MUT = 8`), matching `Option<&u64> = 8` and `Option<MaybeDangling<&u64>> = 8`, and strictly smaller than `Option<MaybeUninit<&u64>> = 16`.
4. **Four-Tier Thin-Pointer LLVM Attribute Lattice (`ptr noundef nonnull` Without `align 8`):** For thin references (`unsafe<'a> &'a u64`, `unsafe<'a> &'a mut u64`), `arg_attrs_for_rust_scalar` (`compiler/rustc_ty_utils/src/abi.rs:318-355`) sets `noundef` and `nonnull` from the copied scalar layout, while `ty_and_layout_pointee_info_at` (`compiler/rustc_middle/src/ty/layout.rs:1054-1221`) returns `None`. This strips **`align 8`** in addition to `noalias`, `nofree`, `readonly`, `captures(...)`, and `dereferenceable(8)` — yielding `ptr noundef nonnull` (even at `-O0`, `align 8` is omitted), strictly weaker than `MaybeDangling<&u64>` (`ptr noundef nonnull align 8`) and strictly stronger than `MaybeUninit<&u64>` (`ptr`).
5. **Live Compound/Wide `UnsafeBinder` Pointee-Attribute Leak Bug:** Thin `unsafe<'a> &'a u64` gets `None` from `ty_and_layout_pointee_info_at` *solely as an accidental consequence of `FieldsShape::Primitive` having `fields.count() == 0`*. Because `ty_and_layout_pointee_info_at` has no `ty::UnsafeBinder(_) => None` match arm and `is_like_maybe_dangling()` (`ty/layout.rs:1205`) ignores `TyKind::UnsafeBinder`, any compound or wide unsafe binder with `fields.count() >= 1` — empirically verified on `unsafe<'a> &'a [u64]`, `unsafe<'a> &'a mut [u64]`, `unsafe<'a> (&'a u64, u64)`, `unsafe<'a> (&'a mut u64, u64)`, `unsafe<'a> Wrap<'a>`, `unsafe<'a> Pair<'a>`, and `Option<unsafe<'a> Wrap<'a>>` — enters the field-recursion loop (`ty/layout.rs:1179-1201`), invokes `field_ty_or_layout` (`ty/layout.rs:891-894`), **strips the `UnsafeBinder`**, and **re-emits `noalias`, `readonly`, `align 8`, and `dereferenceable(8)` / `dereferenceable_or_null(8)` onto unsafe-binder parameters**. This bug remains unpatched on `rust-lang/rust` `main` HEAD (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`).
6. **Three Live Subsystem ICEs (`rc = 101`) Across All Three Inspected Revisions:**
   - **ICE #1 (`v0` symbol mangling):** `compiler/rustc_symbol_mangling/src/v0.rs:679:37` (`unimplemented!()` in `3ef0c22cd` and `342d74463`; `v0.rs:591:37` `todo!()` in `14210df0e`), reachable inside `#![forbid(unsafe_code)]` via `core::mem::size_of::<unsafe<'a> &'a u64>()` under default `v0` mangling, bypassed by `-Z unstable-options -C symbol-mangling-version=legacy`.
   - **ICE #2 (CTFE `const` and default Miri validity):** `compiler/rustc_const_eval/src/interpret/validity.rs:987:36` (`unimplemented!("FIXME(unsafe_binder)")` in `3ef0c22cd` and `342d74463`; `validity.rs:994:36` `todo!("FIXME(unsafe_binder)")` in `14210df0e`), panicking on `const` unsafe binders and on default Miri under both Stacked Borrows and Tree Borrows; bypassed in Miri only with `-Zmiri-disable-validation -Zmiri-tree-borrows`.
   - **ICE #3 (`generic_const_exprs` abstract const builder):** `compiler/rustc_ty_utils/src/consts.rs:57:13` (`unimplemented!("FIXME(unsafe_binders)")` in `3ef0c22cd` and `342d74463`; `todo!("FIXME(unsafe_binders)")` in `14210df0e`), panicking on `WrapUnsafeBinder`, `PlaceUnwrapUnsafeBinder`, and `ValueUnwrapUnsafeBinder` in `recurse_build` before unsafety checking runs.
7. **Anneal Trusted Boundary & Mechanized Soundness:** `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) explicitly routes `TyKind::UnsafeBinder`, `Rvalue::WrapUnsafeBinder`, and `ProjectionElem::UnwrapUnsafeBinder` fail-closed to `.unsupported` in `trusted/lean/Trusted/MirAst.lean:285,308-310,462,469-471,578,612-618`, while its vendored `lean-miri` (`vendor/lean-miri/Miri/Interpreter/ValidityVisitor.lean:304`) faithfully mirrors ICE #2 via `throw (.unsupported "upstream unsafe-binder validity is unimplemented")`. Our Lean `v4.34.1` module `support/UnsafeBinderExistentialRegionSoundness.lean` kernel-verifies the 4-tier attribute lattice and LLVM 23 soundness (`unsafeBinder_param_attrs_sound`), existential region-pack/unpack operational soundness (`wrap_unwrap_live_region_witness_sound`), total prefix-free De-Bruijn `v0` mangling injectivity (`v0_mangle_with_unsafe_binder_injective`), and four constructive sharpness counterexamples (`ce1`–`ce4`) with `0` `sorry`, `0` `Classical.choice`, `0` `Quot.sound`, and `0` `Lean.ofReduceBool`.

## Applicability

This report characterizes the exact behavior of `#![feature(unsafe_binders)]` across five durable, pinned subjects whose relationships are explicitly separated below:

| Subject | Repository & Immutable Commit | Role in This Report | Evidence Acquired |
| :--- | :--- | :--- | :--- |
| `rustc 1.98.0-nightly` + LLVM `22.1.6` + Miri `0.1.0` | `rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`) | Primary live execution subject (`x86_64-unknown-linux-gnu`) and baseline source revision | Live execution (`support/probe_unsafe_binders_and_ices.py`, `2026-11-22`) + direct source inspection (`v0.rs`, `validity.rs`, `consts.rs`) |
| `rustc 1.102.0-nightly` + LLVM `23.1.5` | `rust-lang/rust` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`) | Target LLVM 23 nightly toolchain and primary upstream source audit revision | Preserved execution record (`support/rustc_1_102_0_nightly_llvm23_baseline.json`, `2026-11-21`) + full direct source inspection across 14 compiler and `libcore` files (`2026-11-22`) |
| `rust-lang/rust` `main` HEAD | `rust-lang/rust` `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`2026-11-22`) | Forward-persistence check verifying whether any of the three ICEs or `ty_and_layout_pointee_info_at` changed after `1.102.0-nightly` | Direct source inspection (`v0.rs`, `validity.rs`, `consts.rs`, `ty/layout.rs`, `2026-11-22`) |
| Anneal TCB & vendored `lean-miri` | `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`) | Downstream formal verification boundary consuming `rustc` MIR | Direct source inspection of `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`, `trusted/rustc-capture/src/driver.rs`, and `vendor/lean-miri/Miri/Interpreter/*` (`2026-11-22`) |
| Lean `v4.34.1` kernel | `leanprover/lean4` `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Proof kernel verifying the standalone formalization `support/UnsafeBinderExistentialRegionSoundness.lean` | Live kernel check (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, `2026-11-22`) |

### Shared vs. Revision-Specific Behavior

- **Shared across `1.98.0-nightly` (`14210df0e`), `1.102.0-nightly` (`3ef0c22cd`), and `main` HEAD (`342d74463`):**
  - Surface macro syntax (`wrap_binder!`, `unwrap_binder!`), `TyKind::UnsafeBinder`, `Rvalue::WrapUnsafeBinder`, `ProjectionElem::UnwrapUnsafeBinder`, and bidirectional `E0133` gating.
  - Deliberate omission of `Copy` and `Clone` (`E0277` / `E0382`), propagation of `Sized`/`Send`/`Sync`, and `BikeshedGuaranteedNoDrop` rejection of directly nested `unsafe<'a> unsafe<'b> ...`.
  - Transparent `LayoutData` forwarding yielding `8`-byte `Option<unsafe<'a> &'a u64>` and `Option<unsafe<'a> &'a mut u64>` on 64-bit targets (`x86_64-unknown-linux-gnu`).
  - Thin `unsafe<'a> &'a u64` lowering to `ptr noundef nonnull` without `align 8`, `noalias`, `nofree`, `readonly`, or `dereferenceable(8)`.
  - Absence of a `ty::UnsafeBinder` arm in `ty_and_layout_pointee_info_at` coupled with binder erasure in `field_ty_or_layout`, causing compound/wide unsafe binders (`fields.count() >= 1`) to leak inner reference attributes into LLVM IR.
  - All three compiler ICEs (`v0.rs`, `validity.rs`, `consts.rs`) and both bypasses (`-Z unstable-options -C symbol-mangling-version=legacy` for ICE #1; `-Zmiri-disable-validation -Zmiri-tree-borrows` for Miri ICE #2).
- **Revision-specific differences explicitly observed:**
  - **ICE line numbers and panic macros:** Between `14210df0e` (`1.98.0-nightly`) and `3ef0c22cd` (`1.102.0-nightly`), `todo!()` (`"not yet implemented"`) was replaced by `unimplemented!()` (`"not implemented"`) at all three ICE sites, and line numbers shifted from `v0.rs:591:37` to `v0.rs:679:37` and from `validity.rs:994:36` to `validity.rs:987:36` (`consts.rs:57:13` remained on line `57`, column `13`). All three sites on `main` HEAD (`342d74463`) are line-identical to `3ef0c22cd`.
  - **LLVM `22.1.6` (`1.98.0-nightly`) vs. LLVM `23.1.5` (`1.102.0-nightly`) on `&u64` baseline `pass_plain_ref`:** `compiler/rustc_codegen_llvm/src/abi.rs:83-94` gates `dereferenceable(N)` on `llvm_version >= (23, 0, 0) || regular.contains(ArgAttribute::NoFree)` due to `llvm/llvm-project#204795` decoupling `dereferenceable` from `nofree` in LLVM 23. In post-`-O` IR, `1.102.0-nightly` / LLVM `23.1.5` emits `nofree` explicitly on `pass_plain_ref` (`ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(8) %r`), whereas `1.98.0-nightly` / LLVM `22.1.6` emits `ptr noalias noundef readonly returned align 8 captures(ret: address, read_provenance) dereferenceable(8) %r` (and under `-O -C no-prepopulate-passes`, `ptr noalias noundef readonly align 8 captures(address, read_provenance) dereferenceable(8) %r`). On thin `unsafe<'a> &'a u64`, both LLVM 22 and LLVM 23 emit `ptr noundef nonnull` without `align 8`.
  - **Default next-generation trait solver on `generic_const_exprs`:** In `1.102.0-nightly` (`3ef0c22cd`), `-Znext-solver=globally` is enabled by default for testing, so enabling `generic_const_exprs` emits a warning reverting to `-Znext-solver=coherence` before hitting `consts.rs:57:13`; `1.98.0-nightly` (`14210df0e`) does not emit that revert warning and hits `consts.rs:57:13` directly.

### Target, Edition, and Scope Constraints

- All empirical measurements were collected on `x86_64-unknown-linux-gnu` (`64`-bit pointers, `align_of::<u64>() == 8`, `size_of::<u64>() == 8`) using Rust `--edition=2024`. Size figures (`8 B` vs. `16 B`) scale with pointer width (`4 B` vs. `8 B` on 32-bit targets); `align 8` and `dereferenceable(8)` scale with target alignment and size of the pointee type.
- The Lean `v4.34.1` formalization is a standalone self-contained model (`IMPORTS: []` of `joshlf/anneal`); it proves mathematical properties of the extracted abstract models and does not mechanically link against `rustc`'s Rust source or `Trusted.MirSemantics`.

## Findings

### 1. Surface Macros, Type Representation, and MIR Lowering

`Basis: source + execution`

At the standard-library boundary (`rust-lang/rust` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `library/core/src/unsafe_binder.rs:1-17`), `unsafe_binders` exposes two compiler-internal declarative macros gated by `#[unstable(feature = "unsafe_binders", issue = "130516")]` and `#[allow_internal_unstable(internal_syntax)]`:

```rust
// library/core/src/unsafe_binder.rs:3-17 (3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1)
#[allow_internal_unstable(internal_syntax)]
#[unstable(feature = "unsafe_binders", issue = "130516")]
#[diagnostic::opaque]
pub macro unwrap_binder($expr:expr $( ; $ty:ty )?) {
    k#unwrap_binder($expr $( , $ty )?)
}

#[allow_internal_unstable(internal_syntax)]
#[unstable(feature = "unsafe_binders", issue = "130516")]
#[diagnostic::opaque]
pub macro wrap_binder($expr:expr $( ; $ty:ty )?) {
    k#wrap_binder($expr $( , $ty )?)
}
```

In the compiler's type IR (`compiler/rustc_type_ir/src/ty_kind.rs:245-250`, `3ef0c22cd`), an unsafe binder is a first-class higher-ranked `TyKind` variant carrying bound lifetimes (`UnsafeBinderInner<I>` wraps `ty::Binder<I, I::Ty>`):

```rust
// compiler/rustc_type_ir/src/ty_kind.rs:245-250
/// An unsafe binder type.
///
/// A higher-ranked type used to represent a type which has had some of its
/// lifetimes erased. This can be used to represent types in positions where
/// a lifetime is literally inexpressible, such as self-referential types.
UnsafeBinder(UnsafeBinderInner<I>),
```

Asymmetry at the MIR layer is structurally important (`compiler/rustc_middle/src/mir/syntax.rs:1260-1262, 1468-1469` at `3ef0c22cd`):

- **Packing is an `Rvalue`:** `Rvalue::WrapUnsafeBinder(Operand<'tcx>, Ty<'tcx>)` (line `1469`) consumes/copies an operand and constructs a value of the binder type.
- **Unpacking is a `ProjectionElem`:** `ProjectionElem::UnwrapUnsafeBinder(T)` (line `1262`) projects a *place* without necessarily moving out of the binder (*"A transmute from an unsafe binder to the type that it wraps. This is a projection of a place, so it doesn't necessarily constitute a move out of the binder."*).

Empirical MIR emission (`rustc --edition=2024 --crate-type=lib --emit=mir -Z unstable-options -C symbol-mangling-version=legacy` on `14210df0e`, `support/probe_rustc_1_98_0_nightly_output.json`) confirms both constructs directly in `wrap_and_unwrap_roundtrip`:

```rust
fn wrap_and_unwrap_roundtrip(_1: &u64) -> u64 {
    debug x => _1;
    let mut _0: u64;
    let _2: unsafe<'a> &'a u64;
    let mut _3: &u64;
    bb0: {
        _2 = wrap_binder!(copy _1; unsafe<'a> &'a u64);
        _3 = no_retag copy unwrap_binder!(_2; &u64);
        _0 = copy (*_3);
        return;
    }
}
```

Note two subtle MIR details visible in `bb0`: (1) `unwrap_binder!(_2; &u64)` produces a place of type `&u64` (which *is* `Copy`), so `_3 = no_retag copy unwrap_binder!(_2; &u64)` copies the projected `&u64` out of `_2` without moving `_2`; and (2) the copy is emitted with `WithRetag::No` (`no_retag`).

### 2. Bidirectional `E0133` Unsafety Gating, Move-Only Linearity (`!Copy` / `!Clone`), and `BikeshedGuaranteedNoDrop`

`Basis: source + execution`

#### 2.1 Bidirectional `E0133` Unsafety Gating

In THIR unsafety checking (`compiler/rustc_mir_build/src/check_unsafety.rs:611-615, 663, 825-833, 1033-1042` at `3ef0c22cd`), all three THIR binder-cast expression forms — wrapping, value-unwrapping, and place-unwrapping — are gated symmetrically by `UnsafeOpKind::UnsafeBinderCast`:

```rust
// compiler/rustc_mir_build/src/check_unsafety.rs:611-615
ExprKind::PlaceUnwrapUnsafeBinder { .. }
| ExprKind::ValueUnwrapUnsafeBinder { .. }
| ExprKind::WrapUnsafeBinder { .. } => {
    self.requires_unsafe(expr.span, UnsafeBinderCast);
}
```

Live execution on both `1.98.0-nightly` (`14210df0e`) and `1.102.0-nightly` (`3ef0c22cd`) confirms `rc = 1` with identical diagnostic code and message for both directions:

- `wrap_binder!(r)` outside `unsafe`: `error[E0133]: unsafe binder cast is unsafe and requires unsafe block information that may be required to uphold safety guarantees of a type`
- `*unwrap_binder!(b)` outside `unsafe`: `error[E0133]: unsafe binder cast is unsafe and requires unsafe block information that may be required to uphold safety guarantees of a type`

Why must *both* directions be `unsafe`? `unwrap_binder!` creates a typed reference `&'r T` (or `&'r mut T`) for an arbitrary caller-chosen lifetime `'r` whose validity the borrow checker cannot prove (Section 7, `ce1_safe_unwrap_without_live_witness_uaf`). Conversely, `wrap_binder!` erases lifetime constraints from borrow-checking visibility, creating a value whose later unwrap obligations depend on invariants established at wrap time (such as self-referential pinning or lifetime coupling).

#### 2.2 Move-Only Linearity (`!Copy`, `!Clone`) vs. `Sized`, `Send`, `Sync`

Even when the inner type implements `Copy` and `Clone` (such as `&'a u64`), `rustc` deliberately withholds both `Copy` and `Clone` from `TyKind::UnsafeBinder` in **both** trait solvers (`3ef0c22cd`):

- **Legacy solver** (`compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:1173-1175`):
  ```rust
  // FIXME(unsafe_binder): Should we conditionally
  // (i.e. universally) implement copy/clone?
  ty::UnsafeBinder(_) => {}
  ```
- **Next-generation solver** (`compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs:99, 162, 258`):
  ```rust
  // Line 99  — auto traits (Send, Sync, Unpin, Freeze): unpack inner type
  ty::UnsafeBinder(bound_ty) => Ok(bound_ty.map_bound(|ty| vec![ty])),
  // Line 162 — sizedness traits (Sized, MetaSized, PointeeSized): unpack inner type
  ty::UnsafeBinder(bound_ty) => Ok(bound_ty.map_bound(|ty| vec![ty])),
  // Line 258 — Copy / Clone: explicitly no built-in impl
  ty::UnsafeBinder(_) => Err(NoSolution),
  ```

Empirical trait and move tests (`support/probe_unsafe_binders_and_ices.py`, verified on `14210df0e` and `3ef0c22cd`) confirm the exact trait matrix:

| Probe | Type & Operation | Exit Code | Diagnostic / Result |
| :--- | :--- | ---: | :--- |
| `shared_ref_unsafe_binder_not_copy_e0277` | `need_copy::<unsafe<'a> &'a u64>()` | `1` | `error[E0277]: the trait bound unsafe<'a> &'a u64: Copy is not satisfied` |
| `shared_ref_unsafe_binder_not_clone_e0277` | `need_clone::<unsafe<'a> &'a u64>()` | `1` | `error[E0277]: the trait bound unsafe<'a> &'a u64: Clone is not satisfied` |
| `shared_ref_unsafe_binder_move_e0382` | `fn dup(b: unsafe<'a> &'a u64) -> (..., ...) { (b, b) }` | `1` | `error[E0382]: use of moved value: b` |
| `mut_ref_unsafe_binder_not_copy_e0382` | `fn dup(b: unsafe<'a> &'a mut u32) -> (..., ...) { (b, b) }` | `1` | `error[E0382]: use of moved value: b` |
| `auto_traits_sized_send_sync_on_unsafe_binder` | `need_sized_send_sync::<unsafe<'a> &'a u64>()` | `0` | Compiles cleanly (`Sized`, `Send`, `Sync` all hold) |

Note the subtle interaction with MIR projection noted in Finding 1: while `b: unsafe<'a> &'a u64` itself is strictly move-only (cannot be duplicated as a value), `unsafe { *unwrap_binder!(b) }` projects through `b` as a place without consuming `b`, so the linearity applies to safe value-level moves of the binder handle (and to any `unsafe` code that moves `b` into a callee).

#### 2.3 `BikeshedGuaranteedNoDrop` Well-Formedness and Direct Nesting Rejection

Well-formedness of `unsafe<'a> T` requires `T: BikeshedGuaranteedNoDrop`, preventing a binder from carrying an implicit `Drop` glue whose erased lifetime could already have expired. In the next-generation solver (`compiler/rustc_next_trait_solver/src/solve/trait_goals.rs:738-822` at `3ef0c22cd`):

- `ty::Ref(..)` (both `&T` and `&mut T`) satisfies `BikeshedGuaranteedNoDrop` unconditionally (line `751`).
- `ManuallyDrop<T>` satisfies `BikeshedGuaranteedNoDrop` unconditionally (line `753`).
- Tuples and arrays satisfy `BikeshedGuaranteedNoDrop` structurally on element types (lines `756-769`).
- **All other types — including ADTs and `ty::UnsafeBinder(_)` itself (line `797`) — reduce `BikeshedGuaranteedNoDrop` to `Copy` (lines `774-810`).**

Because `ty::UnsafeBinder(_)` is `!Copy` (`structural_traits.rs:258`), two non-obvious consequences follow immediately (both empirically confirmed in `support/probe_rustc_1_98_0_nightly_output.json`):

1. Non-`Copy` structs (even without `Drop` impls, e.g., `struct NonCopy(u64)`) are rejected inside `unsafe<'a> NonCopy` with `E0277: NonCopy: Copy is not satisfied`, whereas `unsafe<'a> &'a mut NonCopy` and `unsafe<'a> (&'a mut u64, u64)` are accepted.
2. **Direct binder nesting** `unsafe<'a> unsafe<'b> &'a &'b u64` is rejected with `error[E0277]: the trait bound for<'a> unsafe<'b> &'a &'b u64: Copy is not satisfied`, whereas wrapping the inner binder in `ManuallyDrop` (`unsafe<'a> ManuallyDrop<unsafe<'b> &'a &'b u64>`) compiles cleanly (`rc = 0`).

### 3. Layout Transparency and `8`-Byte `Option` Null-Niche Retention

`Basis: source + execution`

Layout calculation for `TyKind::UnsafeBinder` in `compiler/rustc_ty_utils/src/layout.rs:861-864` (`3ef0c22cd`) delegates directly to the region-erased inner type:

```rust
// compiler/rustc_ty_utils/src/layout.rs:861-864
ty::UnsafeBinder(bound_ty) => {
    let ty = tcx.instantiate_bound_regions_with_erased(bound_ty.into());
    cx.layout_of(ty)?.layout
}
```

Because `cx.layout_of(ty)?.layout` copies the entire `LayoutData` struct unchanged:

1. `unsafe<'a> &'a u64` and `unsafe<'a> &'a mut u64` inherit `size = 8`, `align = 8`, `fields = FieldsShape::Primitive`, `variants = Variants::Single { index: 0 }`, `backend_repr = BackendRepr::Scalar(Scalar::Initialized { value: Pointer(AddressSpace::ZERO), valid_range: 1..=usize::MAX })`, and `largest_niche = Some(Niche { offset: 0, value: Pointer(AddressSpace::ZERO), valid_range: 1..=usize::MAX })`.
2. Wrapping in `Option<...>` triggers Rust's standard null-pointer niche optimization (`Variants::Multiple { tag_encoding: TagEncoding::Niche { niche_start: 0, .. }, .. }`).

Live execution of `support/probe_unsafe_binders_and_ices.py` across all four wrapper tiers on `x86_64-unknown-linux-gnu` produces:

| Wrapper Type `W` | `size_of::<Option<W>>()` (bytes) | Scalar `is_uninit_valid()` | Scalar `valid_range` Excludes `0` | Empirical Source |
| :--- | ---: | :--- | :--- | :--- |
| `&u64` | `8` | `false` | `true` | `1.98.0-nightly` native & Miri (`OPT_REF=8`) |
| `MaybeDangling<&u64>` | `8` | `false` | `true` | `1.98.0-nightly` native & Miri (`OPT_MD=8`) |
| `unsafe<'a> &'a u64` | `8` | `false` | `true` | `1.98.0-nightly` & `1.102.0-nightly` (`OPT_SHARED=8`) |
| `unsafe<'a> &'a mut u64` | `8` | `false` | `true` | `1.98.0-nightly` & `1.102.0-nightly` (`OPT_MUT=8`) |
| `MaybeUninit<&u64>` | `16` | `true` | `false` | `1.98.0-nightly` native & Miri (`OPT_UNINIT=16`) |

In LLVM IR (`-O -C no-prepopulate-passes`), `opt_unsafe_binder_is_some(o: Option<unsafe<'a> &'a u64>) -> bool` lowers to:

```llvm
define noundef zeroext i1 @opt_unsafe_binder_is_some(ptr noundef %o) unnamed_addr #0
```

confirming single-register 8-byte pointer passing (`null` encodes `None`, non-null encodes `Some`) with neither `align 8` nor `dereferenceable_or_null(8)`.

### 4. Four-Tier Wrapper LLVM Attribute Lattice and the Compound-Binder Pointee-Attribute Leak Bug

`Basis: source + execution + derived`

#### 4.1 Exact ABI Pipeline in `rustc` (`3ef0c22cd`)

LLVM parameter attributes for Rust scalar pointers are assembled in three stages:

1. **Scalar validity attributes** (`compiler/rustc_ty_utils/src/abi.rs:318-355`, `arg_attrs_for_rust_scalar`):
   ```rust
   // compiler/rustc_ty_utils/src/abi.rs:328-349
   if !scalar.is_uninit_valid() {
       attrs.set(ArgAttribute::NoUndef);
   }
   let Scalar::Initialized { value: Pointer(_), valid_range } = scalar else { return attrs };
   if !valid_range.contains(0) {
       attrs.set(ArgAttribute::NonNull);
   }
   if let Some(pointee) = layout.pointee_info_at(&cx, offset) {
       if pointee.align > Align::ONE {
           attrs.pointee_align =
               Some(pointee.align.min(cx.tcx().sess.target.max_reliable_alignment()));
       }
       attrs.pointee_size = pointee.size;
       if let Some(kind) = pointee.safe { /* noalias, readonly, nofree, writable ... */ }
   }
   ```
2. **Pointee metadata extraction** (`compiler/rustc_middle/src/ty/layout.rs:1054-1221`, `ty_and_layout_pointee_info_at`):
   - `ty::RawPtr(_, _) | ty::FnPtr(..)` at offset `0` returns `Some(PointeeInfo { safe: None, size: Size::ZERO, align: Align::ONE })` (lines `1068-1070`).
   - `ty::Ref(_, ty, mt)` at offset `0` returns `Some(PointeeInfo { safe: Some(kind), size, align: layout.align })` (lines `1071-1108`), setting `size = layout.size` for `&Freeze` / `&mut Unpin`.
   - `ty::Adt(..)` (`Box`) returns `Some(PointeeInfo { safe: Some(Box { .. }), size, align: layout.align })` (lines `1110-1127`).
   - **`_` fallback (lines `1129-1220`)**: handles single-variant structs/tuples/newtypes and null-niche 2-variant enums by iterating `for i in 0..variant.fields.count()`, invoking `variant.field(cx, i)`, and recursing `field.pointee_info_at(cx, offset - field_start)`.
   - **`MaybeDangling` patch (lines `1205-1217`)**:
     ```rust
     if this.ty.is_like_maybe_dangling()
         && let Some(info) = result
     {
         result = Some(PointeeInfo {
             safe: None,
             size: Size::ZERO,
             // Preserve the alignment assertion! That is required even inside `MaybeDangling`.
             align: info.align,
         });
     }
     ```
3. **LLVM emission** (`compiler/rustc_codegen_llvm/src/abi.rs:66-115`):
   - `pointee_align` emits `align N` **unconditionally, even at `-C opt-level=0`** (lines `71-73`).
   - Under optimization (`OptLevel != No`), `pointee_size != 0` emits `dereferenceable(N)` (and clears `NonNull`, which `dereferenceable(N)` implies) whenever `llvm_version >= (23, 0, 0) || regular.contains(ArgAttribute::NoFree)` (lines `82-94`), followed by `NoAlias`, `NonNull`, `ReadOnly`, `NoUndef`, `Writable`, `NoFree` (lines `95-98`).

#### 4.2 Strict Four-Tier Attribute Lattice for Thin Pointers (`&u64`)

For thin `unsafe<'a> &'a u64`, `layout.fields` is `FieldsShape::Primitive`, so `variant.fields.count() == 0`. The fallback loop `0..0` in `ty_and_layout_pointee_info_at` performs zero iterations and returns `None`. Consequently `attrs.pointee_align` stays `None` (no `align 8` even at `-O0`), `attrs.pointee_size` stays `0`, and `pointee.safe` is never visited, while `arg_attrs_for_rust_scalar` still emits `noundef` and `nonnull` from the copied scalar range `1..=usize::MAX`.

This yields a strict four-tier lattice (ordered by increasing value permissiveness / decreasing LLVM parameter attribute strength):

$$\&\text{u64} \;<\; \text{MaybeDangling}\langle\&\text{u64}\rangle \;<\; \text{unsafe}\langle\text{'a}\rangle\;\&\text{'a u64} \;<\; \text{MaybeUninit}\langle\&\text{u64}\rangle$$

| Tier | Rust Type | `-O0` IR Param (`1.98.0`) | `-O -C no-prepopulate-passes` IR Param (`1.98.0`, pure ABI) | `-O` IR Param (`1.98.0`, LLVM `22.1.6`) | `-O` IR Param (`1.102.0`, LLVM `23.1.5`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 3 (strongest) | `&u64` (`pass_plain_ref`) | `ptr align 8 %r` | `ptr noalias noundef readonly align 8 captures(address, read_provenance) dereferenceable(8) %r` | `ptr noalias noundef readonly returned align 8 captures(ret: address, read_provenance) dereferenceable(8) %r` | `ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(8) %r` |
| 2 | `MaybeDangling<&u64>` | `ptr align 8 %r` | `ptr noundef nonnull align 8 %r` | `ptr noundef nonnull readnone returned align 8 captures(ret: address, provenance) %r` | *(same ABI source at `3ef0c22cd`)* |
| 1 | `unsafe<'a> &'a u64` (`unused`) | `ptr %_b` | `ptr noundef nonnull %_b` | `ptr noundef nonnull readnone captures(none) %_b` | `ptr noundef nonnull %_b` |
| 1 | `unsafe<'a> &'a u64` (`shared`, deref) | `ptr %0` | `ptr noundef nonnull %0` | `ptr noundef nonnull readonly captures(none) %0` | `ptr noundef nonnull %0` |
| 1 | `unsafe<'a> &'a mut u64` (`unused`) | `ptr %_b` | `ptr noundef nonnull %_b` | `ptr noundef nonnull readnone captures(none) %_b` | *(same ABI source at `3ef0c22cd`)* |
| 0 (weakest) | `MaybeUninit<&u64>` | `ptr %_m` | `ptr %_m` | `ptr readnone captures(none) %_m` | *(same ABI source at `3ef0c22cd`)* |

Note why `pass_unsafe_binder_unused` and `pass_unsafe_binder_shared` show `readnone`/`readonly`/`captures(none)` at `-O` on LLVM `22.1.6` while `-O -C no-prepopulate-passes` shows purely `ptr noundef nonnull`: `readnone`, `readonly`, `returned`, and `captures(none)` are **post-hoc LLVM `FunctionAttrs` inferences** from the callee body, whereas `noundef`, `nonnull`, `align 8`, `noalias`, `nofree`, and `dereferenceable(8)` are **caller-enforced `rustc` ABI entry preconditions**. Crucially, omitting `align 8` makes `transmute::<usize, unsafe<'a> &'a u64>(1)` passed to `pass_unsafe_binder_unused` (without unwrapping) free of LLVM `align 8` entry UB — verified natively at `-O` (`MISALIGNED_UNUSED=7`, `rc = 0`) and under Miri `-Zmiri-disable-validation -Zmiri-tree-borrows` (`MISALIGNED_UNUSED=7`, `rc = 0`), and mechanized in `ce2_align8_attr_on_misaligned_transmuted_binder_ub`.

#### 4.3 Discovery: Live Compound/Wide `UnsafeBinder` Pointee-Attribute Leak Bug

Inspection of `compiler/rustc_middle/src/ty/layout.rs:891-894` (`field_ty_or_layout`) alongside `ty_and_layout_pointee_info_at` (`1054-1221`) revealed an unintended soundness defect present verbatim in `14210df0e`, `3ef0c22cd`, and `main` HEAD `342d74463`:

```rust
// compiler/rustc_middle/src/ty/layout.rs:891-894 (3ef0c22cd; line 925 on 342d74463)
ty::UnsafeBinder(bound_ty) => {
    let ty = tcx.instantiate_bound_regions_with_erased(bound_ty.into());
    field_ty_or_layout(TyAndLayout { ty, ..this }, cx, i)
}
```

When an `UnsafeBinder` wraps *any* type whose layout has `fields.count() >= 1` — including a wide reference (`unsafe<'a> &'a [u64]`, `unsafe<'a> &'a mut [u64]`), a tuple (`unsafe<'a> (&'a u64, u64)`), a struct (`unsafe<'a> Pair<'a>`), or even a `#[repr(transparent)]` newtype (`unsafe<'a> Wrap<'a>`) — `ty_and_layout_pointee_info_at` enters the `_` arm (`1129`), loops `for i in 0..variant.fields.count()`, calls `variant.field(cx, i)` which **strips `UnsafeBinder` via `field_ty_or_layout`**, and recurses `field.pointee_info_at(...)` on the raw unwrapped `&'erased u64` / `&'erased mut u64`! Because `is_like_maybe_dangling()` at line `1205` only checks ADTs carrying `#[rustc_maybe_dangling]`, the inner `PointeeInfo` is returned **unstripped**.

Live `-O -C no-prepopulate-passes --emit=llvm-ir` execution (`support/probe_rustc_1_98_0_nightly_output.json`) confirms full attribute leakage across all seven compound/wide binder signatures:

```llvm
define noundef i64 @pass_thin_binder(ptr noundef nonnull %_b) unnamed_addr #0
define noundef i64 @pass_wide_slice_binder(ptr noalias noundef nonnull readonly align 8 captures(address, read_provenance) %_b.0, i64 noundef %_b.1) unnamed_addr #0
define noundef i64 @pass_mut_slice_binder(ptr noalias noundef nonnull align 8 %_b.0, i64 noundef %_b.1) unnamed_addr #0
define noundef i64 @pass_tuple_binder(ptr noalias noundef readonly align 8 captures(address, read_provenance) dereferenceable(8) %_b.0, i64 noundef %_b.1) unnamed_addr #0
define noundef i64 @pass_mut_tuple_binder(ptr noalias noundef align 8 dereferenceable(8) %_b.0, i64 noundef %_b.1) unnamed_addr #0
define noundef i64 @pass_struct_binder(ptr noalias noundef readonly align 8 captures(address, read_provenance) dereferenceable(8) %_b.0, i64 noundef %_b.1) unnamed_addr #0
define noundef i64 @pass_newtype_binder(ptr noalias noundef readonly align 8 captures(address, read_provenance) dereferenceable(8) %_b) unnamed_addr #0
define noundef zeroext i1 @pass_opt_newtype_binder(ptr noalias noundef readonly align 8 captures(address, read_provenance) dereferenceable_or_null(8) %o) unnamed_addr #0
```

Passing a dangling `unsafe<'a> Wrap<'a>` or `unsafe<'a> (&'a u64, u64)` (or a `Some` dangling `Option<unsafe<'a> Wrap<'a>>`) into a function that never unwraps it therefore violates LLVM's `dereferenceable(8)` / `noalias` / `readonly` / `align 8` entry contract (formalized in `ce4_compound_binder_pointee_attr_leak_ub`). The clean upstream fix is an explicit `ty::UnsafeBinder(_) => None` arm at the top of `ty_and_layout_pointee_info_at` (`compiler/rustc_middle/src/ty/layout.rs:1067`) — or, if `UnsafeBinder` is ever specified to preserve alignment like `MaybeDangling`, explicit recursive stripping mirroring lines `1205-1217`.

### 5. Three Live Subsystem Compiler ICEs (`v0.rs`, `validity.rs`, `consts.rs`)

`Basis: source + execution`

Across all three inspected revisions (`14210df0e`, `3ef0c22cd`, `342d74463`), three independent compiler subsystems terminate with an internal compiler error (`rc = 101`) when encountering `unsafe_binders`:

| ICE | Subsystem | `1.98.0-nightly` (`14210df0e`) | `1.102.0-nightly` (`3ef0c22cd`) | `main` HEAD (`342d74463`) | Minimal Trigger | Verified Bypass |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **ICE #1** | Default `v0` symbol mangler | `v0.rs:591:37` `todo!()` | `v0.rs:679:37` `unimplemented!()` | `v0.rs:679:37` `unimplemented!()` | `#![forbid(unsafe_code)]` calling `size_of::<unsafe<'a> &'a u64>()` | `-Z unstable-options -C symbol-mangling-version=legacy` (`rc = 0`) |
| **ICE #2** | CTFE `const` & Miri validity visitor | `validity.rs:994:36` `todo!("FIXME(unsafe_binder)")` | `validity.rs:987:36` `unimplemented!("FIXME(unsafe_binder)")` | `validity.rs:987:36` `unimplemented!("FIXME(unsafe_binder)")` | `const B: unsafe<'a> &'a u64 = unsafe { wrap_binder!(&X) };` OR any Miri execution of `unsafe<'a> &'a u64` | Miri only: `-Zmiri-disable-validation -Zmiri-tree-borrows` (`rc = 0`); no CTFE `const` bypass |
| **ICE #3** | `generic_const_exprs` abstract const builder | `consts.rs:57:13` `todo!("FIXME(unsafe_binders)")` | `consts.rs:57:13` `unimplemented!("FIXME(unsafe_binders)")` | `consts.rs:57:13` `unimplemented!("FIXME(unsafe_binders)")` | `wrap_binder!` / `unwrap_binder!` inside a generic const expression (`where [(); id::<N>(wrap_binder!(...))]:`) | None under `generic_const_exprs` |

#### 5.1 ICE #1: Default `v0` Symbol Mangling (`v0.rs:679:37`) vs. `legacy` Mangling

In `compiler/rustc_symbol_mangling/src/v0.rs:678-679` (`3ef0c22cd` and `342d74463`), `V0SymbolMangler::print_type` stops with an unimplemented arm:

```rust
// compiler/rustc_symbol_mangling/src/v0.rs:678-679
// FIXME(unsafe_binder):
ty::UnsafeBinder(..) => unimplemented!(),
```

Because default `v0` mangling structurally prints every generic type argument of every monomorphized function (`print_def_path` -> `print_type`), merely instantiating `core::mem::size_of::<unsafe<'a> &'a u64>()` in a `#![forbid(unsafe_code)]` crate (zero `unsafe` blocks!) triggers `rc = 101` at `v0.rs:679:37` (or `v0.rs:591:37` on `14210df0e`).

By contrast, `compiler/rustc_symbol_mangling/src/legacy.rs:64-88, 251-265` succeeds (`rc = 0`) for two reasons: (1) for ordinary monomorphized functions like `size_of`, `legacy` mangling omits generic type arguments from the printed path and hashes the erased `instance_ty` into the 16-hex-digit `17h<hash>E` suffix via `get_symbol_hash`; and (2) when `legacy` does print types (e.g., drop glue or trait impls), `LegacySymbolMangler` delegates to `PrettyPrinter`, which implements `ty::UnsafeBinder`.

#### 5.2 ICE #2: CTFE & Default Miri Validity (`validity.rs:987:36`) and Dangling-Binder Miri Behavior

In `compiler/rustc_const_eval/src/interpret/validity.rs:987` (`3ef0c22cd` and `342d74463`), `ValidityVisitor::visit_primitive` panics immediately upon validating any value of type `ty::UnsafeBinder`:

```rust
// compiler/rustc_const_eval/src/interpret/validity.rs:987
ty::UnsafeBinder(_) => unimplemented!("FIXME(unsafe_binder)"),
```

Because CTFE (`const` evaluation) and Miri share `rustc_const_eval`'s validity machine:

1. Defining `const B: unsafe<'a> &'a u64 = unsafe { wrap_binder!(&X) };` panics during `rustc` compilation (`rc = 101`).
2. Running *any* program that constructs or passes an `unsafe<'a> &'a u64` under default Miri — whether Stacked Borrows (default) or Tree Borrows (`-Zmiri-tree-borrows`) — panics at `validity.rs` (`rc = 101`) *before* aliasing checks can reject or accept a dangling binder.
3. Passing `-Zmiri-disable-validation -Zmiri-tree-borrows` skips `ValidityVisitor`, yielding four sharply discriminating Miri outcomes (all empirically executed in `support/probe_rustc_1_98_0_nightly_output.json`):
   - **Live wrap/unwrap round-trip (`Part A`):** `rc = 0`, stdout `OPT_REF=8 OPT_MD=8 OPT_SHARED=8 OPT_MUT=8 OPT_UNINIT=16 OUT=42 SLOT=42` (identical to `1.102.0-nightly` `OPT_SHARED=8 OPT_MUT=8 OUT=42 SLOT=42`).
   - **Dangling binder passed without unwrapping (`dangling_binder_miri_tb_disable_validation`):** `Box::new(42)` is wrapped, dropped, and passed to `sink_unused(_b: unsafe<'a> &'a u64)` -> **`rc = 0`, stdout `DANGLING_UNUSED=7`** (no immediate UB on passing an un-unwrapped dangling binder when validation is disabled).
   - **Dangling binder unwrapped and dereferenced (`dangling_binder_unwrap_ub_miri_tb_disable_validation`):** `*unwrap_binder!(b)` after `drop(bx)` -> **`rc = 1`, `error: Undefined Behavior: memory access failed: alloc... has been freed, so this pointer is dangling`**.
   - **Misaligned non-null transmuted binder passed without unwrapping (`misaligned_binder_unused_miri_tb_disable_validation`):** `transmute::<usize, unsafe<'a> &'a u64>(1)` passed to `sink_unused` -> **`rc = 0`, stdout `MISALIGNED_UNUSED=7`**.

#### 5.3 ICE #3: `generic_const_exprs` Abstract Const Building (`consts.rs:57:13`)

In `compiler/rustc_ty_utils/src/consts.rs:54-58` (`3ef0c22cd`, `342d74463`, and `14210df0e`), `recurse_build` panics unconditionally on all three THIR unsafe-binder expression kinds:

```rust
// compiler/rustc_ty_utils/src/consts.rs:54-58
&ExprKind::PlaceUnwrapUnsafeBinder { .. }
| &ExprKind::ValueUnwrapUnsafeBinder { .. }
| &ExprKind::WrapUnsafeBinder { .. } => {
    unimplemented!("FIXME(unsafe_binders)")
}
```

Because `build_abstract_const` runs during generic well-formedness / predicate construction *before* THIR unsafety checking (`check_unsafety.rs`), a `where [(); id::<N>(wrap_binder!(&[0u8; N]))]:` bound crashes at `consts.rs:57:13` (`rc = 101`) even without an enclosing `unsafe` block. Note that wrapping `wrap_binder!` inside a block `{ ... }` fails earlier with `error: overly complex generic constant (blocks are not supported in generic constants)` (`rc = 1`), never reaching line `57`.

### 6. Anneal Trusted Boundary (`joshlf/anneal@c131b320e`) and Vendored `lean-miri` Audit

`Basis: source + derived`

Direct inspection of `joshlf/anneal` at commit `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`) shows a clean, deliberate fail-closed posture across the trusted verification kernel and a faithful mirror of upstream `rustc` inside vendored `lean-miri`:

1. **`trusted/lean/Trusted/MirAst.lean` (Pass-1 Trusted AST Boundary):**
   - `MirTy` (`lines 285, 308-310`): explicitly quotes `UnsafeBinder(UnsafeBinderInner<I>)` from `rustc_type_ir::TyKind` and maps it to `MirTy.unsupported`.
   - `ProjectionElem` (`lines 462, 469-471`): explicitly quotes `UnwrapUnsafeBinder(T)` from `rustc_middle::mir::ProjectionElem` and maps it to `ProjectionElem.unsupported`.
   - `Rvalue` (`lines 578, 612-618`): explicitly quotes `WrapUnsafeBinder(Operand<'tcx>, Ty<'tcx>)` from `rustc_middle::mir::Rvalue` and maps it to `Rvalue.unsupported`.
2. **`trusted/lean/Trusted/MirSemantics.lean` (Operational Semantics):**
   - Any `.unsupported` type, projection, or rvalue faults fail-closed with `FaultKind.unsupported` (lines `328-334, 400, 797-820, 1247-1313`), preventing unsound verification claims over unsafe binders.
   - `Operand.move` unconditionally deinitializes moved non-ZST local slots (`deinitMovedPlace = true`, lines `69, 141, 921-960`), which aligns directly with the move-only (`!Copy`) linearity of `unsafe<'a> &'a T` and `unsafe<'a> &'a mut T` if Anneal later admits `UnsafeBinder`.
3. **`vendor/lean-miri/Miri/Interpreter/*` (Pass-2 Reference Interpreter):**
   - `ValidityVisitor.lean:24, 304`: explicitly mirrors ICE #2 fail-closed:
     ```lean
     | .unsafeBinder => throw (.unsupported "upstream unsafe-binder validity is unimplemented")
     ```
   - `Rvalue.lean:114-116`: lowers `.WrapUnsafeBinder operand _` via `copyOpAllowTransmute`.
   - `PlaceDynamic.lean:139-143` and `Projection.lean:245`: lower `.UnwrapUnsafeBinder ty` via size-checked layout transmute (`base.layout.layout.size != layout.layout.size` check, then zero-offset layout retyping).
   - `LayoutCompat.lean:33, 51, 88, 126`: implements `hasTrivialAbi` and `unfoldTransparent` on `.unsafeBinder` by unfolding via `eraseUnsafeBinder` (`CompilerFacts.lean:233`, `"unsafe_binder_erased"`).
4. **Architectural Obligations for a Verified Rust Compiler Admitting `unsafe_binders`:**
   - **ABI / LLVM codegen:** Must insert an explicit `ty::UnsafeBinder(_) => None` guard (or recursive pointee-attribute stripping) in `ty_and_layout_pointee_info_at` so compound/wide binders do not leak `noalias`/`readonly`/`align`/`dereferenceable` onto parameters.
   - **Validity & CTFE:** Must define a non-panicking validity contract matching thin `ptr noundef nonnull` (scalar initialized + non-null niche without dereferenceability or alignment) before enabling CTFE or Miri validation.
   - **Proof obligations (`Trusted.MirSemantics` / VC transport):** Must retain `E0133` caller-discharged live-region witnesses at `ProjectionElem::UnwrapUnsafeBinder` and enforce `deinitMovedPlace = true` on move-only binder locals.
   - **Symbol mangling:** Must extend `V0SymbolMangler::print_type` with a prefix-free binder tag (disjoint from existing RFC 2603 type tags) to eliminate the `#![forbid(unsafe_code)]` ICE.

### 7. Kernel-Checked Lean `v4.34.1` Formalization (`support/UnsafeBinderExistentialRegionSoundness.lean`)

`Basis: source + execution + derived`

The standalone Lean `v4.34.1` module `support/UnsafeBinderExistentialRegionSoundness.lean` (`1,016` LOC, `47,850` B) kernel-checks cleanly under `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`) with **`0` `sorry`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `Lean.ofReduceBool`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, and `0` `._unsafe_rec`**. Every recursive function over a recursive inductive (`lookupAlloc`, `V0Ty.decEq`, `encNat`, `mangleExt`, `mangleStockV0`, `hasNoUnsafeBinder`) is marked `noncomputable def`, and structural `DecidableEq` on `V0Ty` is implemented manually without `deriving`.

| Theorem (`UnsafeBinderSoundness.*`) | Formal Statement Summary | Kernel Axioms | Empirical / Source Anchor |
| :--- | :--- | :--- | :--- |
| `wrapper_attr_lattice_strict` | For `alignBytes > 1, sizeBytes > 0`, strict attribute-strength chain `MaybeUninit < UnsafeBinder < MaybeDangling < PlainRef` | `[]` (none) | `ty/layout.rs:1054-1221`, `ty_utils/abi.rs:318-355`, Part B LLVM IR |
| `tier_value_inclusion` | Permitted runtime pointer sets satisfy `&T ⊆ MaybeDangling<&T> ⊆ UnsafeBinder<&T> ⊆ MaybeUninit<&T>` | `[]` (none) | 4-tier wrapper validity hierarchy |
| `attr_valid_monotone` | `attrLe a b → AttrsValidAtEntry b p → AttrsValidAtEntry a p` | `[]` (none) | LLVM entry-UB weakening law |
| `unsafeBinder_param_attrs_sound` | `TierValueValid A S .unsafeBinder p → AttrsValidAtEntry (emitWrapperAttrs A S .unsafeBinder) p` | `[]` (none) | Soundness of `ptr noundef nonnull` (no `align 8`, `noalias`, `dereferenceable`) |
| `all_four_tiers_param_attrs_sound` | Uniform ABI entry-UB soundness across all four `WrapperTier` constructors | `[]` (none) | Full 4-tier LLVM 23 lowering |
| `option_unsafeBinder_null_niche_discriminates` | `encodeOptUnsafeBinder none = 0`, `encodeOptUnsafeBinder (some v) ≠ 0`, and `none ≠ some v` in one pointer word | `[]` (none) | `OPT_SHARED = 8`, `OPT_MUT = 8`, `ty_utils/layout.rs:861-864` |
| `wrap_preserves_initial_witness` | `TypedRefValid env h r → LiveRegionWitness env h (wrapBinder r)` | `[]` (none) | Packing a live `&'r u64` establishes an initial existential witness |
| `wrap_unwrap_live_region_witness_sound` | Given `TypedRefValid env₁ h₁ r`, `HeapWf env₂ h₂`, and caller-supplied `LiveRegionWitness env₂ h₂ (wrapBinder r)`, `unwrapAndDeref h₂ (wrapBinder r) = .ok e.val` | `[propext]` | Operational soundness of `WrapUnsafeBinder` + `UnwrapUnsafeBinder` (`E0133`) |
| `move_only_binder_single_consumption` | `moveOutSlot s = some (v, s') → s' = .uninit ∧ moveOutSlot s' = none` | `[]` (none) | `!Copy` (`E0277`/`E0382`) & `Trusted.MirSemantics` `deinitMovedPlace = true` |
| `mangleExt_extends_stock` | For all `t` with `hasNoUnsafeBinder t`, `mangleStockV0 t = some (mangleExt t)` | `[propext]` | Backward compatibility with stock `v0` mangler (`v0.rs:521-689`) |
| `mangleExt_prefix_free` | `mangleExt t₁ ++ r₁ = mangleExt t₂ ++ r₂ → t₁ = t₂ ∧ r₁ = r₂` (using fresh `'J'` + `'G'` + `_`-terminated count, preserving `'L'` non-collision) | `[propext]` | Prefix-free RFC 2603 `v0` grammar extension |
| `v0_mangle_with_unsafe_binder_injective` | `mangleExt t₁ = mangleExt t₂ → t₁ = t₂` across `bool`, `u64`, `unit`, `&`/`&mut` (erased & De-Bruijn bound), raw ptrs, slices, `fnPtr`, and `unsafeBinder` | `[propext]` | Total, injective `v0` fix for ICE #1 (`v0.rs:679`) |
| `ce1_safe_unwrap_without_live_witness_uaf` | Concrete freed heap where valid `wrapBinder r` without `LiveRegionWitness` evaluates to `.useAfterFree` | `[propext]` | Sharpness of `E0133` & Miri UAF (`dangling_binder_unwrap_ub`) |
| `ce2_align8_attr_on_misaligned_transmuted_binder_ub` | Concrete `addr = 1` satisfies `unsafeBinder` (`ptr noundef nonnull`) yet violates `maybeDangling` (`align 8`) | `[]` (none) | Sharpness of stripping `align 8` & `MISALIGNED_UNUSED=7` |
| `ce3_partial_v0_mangler_panics_on_unsafe_binder` | On `unsafe<'a> &'a u64`, `mangleStockV0 = none` while `mangleExt` separates it from `&u64` and `unsafe<'a> &'a mut u64` | `[propext]` | Formal witness of ICE #1 (`v0.rs:679`) |
| `ce4_compound_binder_pointee_attr_leak_ub` | Concrete aligned dangling `addr = 8, liveBytes = 0` satisfies `unsafeBinder` yet violates leaked `plainRef` (`dereferenceable(8)`) | `[]` (none) | Formal witness of Finding 4.3 compound-binder attribute-leak bug |

## Boundaries

The following scope limits and negative-space classifications qualify all claims above:

- **known not to apply — Thin-pointer `align 8` stripping does not extend to compound or wide `UnsafeBinder` types:** Finding 4.3 proves by source inspection (`ty/layout.rs:891-894, 1054-1221`) and live LLVM IR emission that `unsafe<'a> &'a [u64]`, `unsafe<'a> &'a mut [u64]`, `unsafe<'a> (&'a u64, u64)`, `unsafe<'a> (&'a mut u64, u64)`, `unsafe<'a> Wrap<'a>`, `unsafe<'a> Pair<'a>`, and `Option<unsafe<'a> Wrap<'a>>` do *not* strip `align 8`, `noalias`, `readonly`, or `dereferenceable(8)`; they erroneously re-emit inner reference attributes. Do not assume `ptr noundef nonnull` holds for non-primitive `UnsafeBinder` layouts on current `rustc`.
- **known not to apply — Direct binder nesting is not valid without `ManuallyDrop`:** Because `unsafe<'a> T` requires `T: BikeshedGuaranteedNoDrop` and `TyKind::UnsafeBinder` is `!Copy`, `unsafe<'a> unsafe<'b> &'a &'b u64` is rejected with `E0277`. Multi-level De-Bruijn binder nesting requires an intervening `ManuallyDrop` (or reference indirection).
- **unsupported — CTFE `const`, default Miri validation, `v0` symbol mangling, and `generic_const_exprs` on `unsafe_binders`:** All four paths are explicitly unimplemented (`unimplemented!()` / `todo!()`) in `rustc` up through `main` HEAD (`342d74463`). In particular, Miri cannot simultaneously run value validation *and* execute `unsafe_binders`; disabling validation via `-Zmiri-disable-validation` disables *all* validity checks globally across the program, so passing Miri under `-Zmiri-disable-validation` does not certify general scalar/niche validity (e.g., it would not catch a transmuted null `unsafe<'a> &'a u64` either).
- **unsupported — Anneal `Trusted.MirSemantics` and `vendor/lean-miri` validity:** `joshlf/anneal@c131b320e` explicitly rejects `TyKind::UnsafeBinder`, `Rvalue::WrapUnsafeBinder`, and `ProjectionElem::UnwrapUnsafeBinder` as `.unsupported`. No Anneal proof obligation can currently discharge a Rust body containing `unsafe_binders`.
- **unknown — Final normative validity invariant of `unsafe<'a> &'a T` in the Rust Abstract Machine:** Upstream `rustc` has not finalized whether `unsafe<'a> &'a T` is normatively intended to forbid misaligned non-null pointers (like `MaybeDangling<&T>`) or only null/uninit pointers (matching current thin-pointer LLVM lowering `ptr noundef nonnull`), nor whether `Copy`/`Clone` will eventually be conditionally implemented (`candidate_assembly.rs:1173` carries an open `FIXME(unsafe_binder)`). The current `validity.rs:987` `unimplemented!("FIXME(unsafe_binder)")` leaves the interpreter contract unsettled.
- **not examined — Non-`x86_64` targets, `32`-bit pointer widths, Cranelift/GCC backends, `#[repr(packed)]` fields, and `dyn Trait` / coroutine-capture interactions:** All empirical probes ran on `x86_64-unknown-linux-gnu` with the LLVM backend (`rustc_codegen_llvm`). Behavior under `rustc_codegen_cranelift`, `rustc_codegen_gcc`, `arm`/`riscv32` pointer widths, `unsafe<'a> &'a dyn Trait` wide-pointer vtable attributes, or `async` coroutine state-machine captures of `unsafe<'a> &'a T` was not examined.
- **not examined — Live local execution of `rustc 1.102.0-nightly` on the compound-binder probe (`Finding 4.3`):** Live execution of the seven compound-binder LLVM IR cases (`pass_wide_slice_binder`, `pass_newtype_binder`, etc.) ran on `rustc 1.98.0-nightly` (`14210df0e`, LLVM `22.1.6`) on `2026-11-22`; persistence of the exact same bug on `1.102.0-nightly` (`3ef0c22cd`) and `main` HEAD (`342d74463`) is established by direct primary-source inspection of `ty_and_layout_pointee_info_at` and `field_ty_or_layout` (`source + derived`), not by re-executing `1.102.0-nightly` on those seven new cases.

## Evidence

### Primary Upstream Source Citations (Verified Live)

All line numbers below were verified directly against immutable commits on GitHub:

1. **`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`):**
   - `library/core/src/unsafe_binder.rs:1-17` — `wrap_binder!` and `unwrap_binder!` macros (`#[unstable(feature = "unsafe_binders", issue = "130516")]`).
   - `library/core/src/mem/maybe_dangling.rs:1-120` — `#[rustc_maybe_dangling]` wrapper definition contrasted with `UnsafeBinder`.
   - `compiler/rustc_type_ir/src/ty_kind.rs:245-250, 409` — `TyKind::UnsafeBinder(UnsafeBinderInner<I>)`.
   - `compiler/rustc_middle/src/mir/syntax.rs:1260-1262, 1468-1469` — `ProjectionElem::UnwrapUnsafeBinder(T)` and `Rvalue::WrapUnsafeBinder(Operand<'tcx>, Ty<'tcx>)`.
   - `compiler/rustc_mir_build/src/check_unsafety.rs:369-371, 611-615, 663, 825-833, 1033-1042` — `UnsafeOpKind::UnsafeBinderCast` gating `WrapUnsafeBinder`, `PlaceUnwrapUnsafeBinder`, and `ValueUnwrapUnsafeBinder`.
   - `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:712, 893, 1173-1175` — legacy solver auto-trait propagation and deliberate empty `Copy`/`Clone` arm (`FIXME(unsafe_binder)`).
   - `compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs:99, 162, 258` — next-gen solver `Ok(...)` for auto traits and sizedness traits, `Err(NoSolution)` for `Copy`/`Clone`.
   - `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs:738-822` — `consider_builtin_bikeshed_guaranteed_no_drop_candidate` reducing `ty::UnsafeBinder(_)` (line `797`) to `Copy`.
   - `compiler/rustc_ty_utils/src/layout.rs:861-864` — `ty::UnsafeBinder(bound_ty)` copying `cx.layout_of(erased_ty)?.layout`.
   - `compiler/rustc_middle/src/ty/layout.rs:891-894, 1054-1221` — `field_ty_or_layout` erasing `UnsafeBinder`, `ty_and_layout_pointee_info_at` lacking a `ty::UnsafeBinder` arm, and `is_like_maybe_dangling()` preserving `align` at `1205-1217`.
   - `compiler/rustc_ty_utils/src/abi.rs:318-355` — `arg_attrs_for_rust_scalar` setting `NoUndef`, `NonNull`, and querying `pointee_info_at`.
   - `compiler/rustc_target/src/callconv/mod.rs:166-181` — `ArgAttributes` (`regular`, `arg_ext`, `pointee_size`, `pointee_align`).
   - `compiler/rustc_codegen_llvm/src/abi.rs:39-115` — unconditional `align` emission (`71-73`), LLVM 23 vs. pre-23 `dereferenceable`/`nofree` rule (`83-94`).
   - `compiler/rustc_symbol_mangling/src/v0.rs:216-267, 313-339, 500-696` — De-Bruijn `BinderLevel`, `wrap_binder`, prefix-free type grammar, and **ICE #1** at `679:37` (`ty::UnsafeBinder(..) => unimplemented!()`).
   - `compiler/rustc_symbol_mangling/src/legacy.rs:64-88, 240-265` — hash-based legacy mangling explaining why `-C symbol-mangling-version=legacy` bypasses ICE #1.
   - `compiler/rustc_const_eval/src/interpret/validity.rs:987` — **ICE #2** (`ty::UnsafeBinder(_) => unimplemented!("FIXME(unsafe_binder)")`).
   - `compiler/rustc_ty_utils/src/consts.rs:54-58, 311-316` — **ICE #3** (`unimplemented!("FIXME(unsafe_binders)")` in `recurse_build`).
2. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`):**
   - `compiler/rustc_symbol_mangling/src/v0.rs:591:37` (`todo!()`), `compiler/rustc_const_eval/src/interpret/validity.rs:994:36` (`todo!("FIXME(unsafe_binder)")`), `compiler/rustc_ty_utils/src/consts.rs:57:13` (`todo!("FIXME(unsafe_binders)")`).
3. **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`main` HEAD, `2026-11-22`):**
   - `v0.rs:679:37`, `validity.rs:987:36`, `consts.rs:57:13` unchanged from `3ef0c22cd`; `ty/layout.rs:925` (`field_ty_or_layout`) and `ty/layout.rs:1091-1255` (`ty_and_layout_pointee_info_at`) retain identical binder-erasing field recursion and lack of `ty::UnsafeBinder` stripping.
4. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`):**
   - `trusted/lean/Trusted/MirAst.lean:285, 308-310, 462, 469-471, 578, 612-618` — fail-closed `.unsupported` mapping for `UnsafeBinder`, `UnwrapUnsafeBinder`, `WrapUnsafeBinder`.
   - `trusted/lean/Trusted/MirSemantics.lean:51, 69, 103, 141, 328-334, 921-960` — `FaultKind.unsupported` and `deinitMovedPlace = true`.
   - `vendor/lean-miri/Miri/Interpreter/{ValidityVisitor.lean:24,304, Rvalue.lean:114-116, PlaceDynamic.lean:139-143, Projection.lean:245, LayoutCompat.lean:33,51,88,126}`.

### Package-Owned Support Artifacts

All evidence scripts, recorded execution outputs, and mechanized Lean proofs are preserved inside this report package:

- `support/probe_unsafe_binders_and_ices.py` — Standalone Python 3.10+ empirical harness exercising Parts A, B (including `-O0`, `-O -C no-prepopulate-passes`, `-O`, `--emit=mir`, compound/wide binder attribute leakage, dangling Miri, and misaligned transmuted binder), and C (safety gates, `!Copy`/`!Clone`/auto-traits/nesting, and all three ICEs).
- `support/probe_rustc_1_98_0_nightly_output.json` — Live execution output recorded on `2026-11-22` using `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / LLVM `22.1.6` / `miri 0.1.0 (14210df0e2 2026-05-31)` on `x86_64-unknown-linux-gnu`.
- `support/rustc_1_102_0_nightly_llvm23_baseline.json` — Preserved execution record collected on `2026-11-21` using `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` / LLVM `23.1.5` on `x86_64-unknown-linux-gnu`, recording exact `v0.rs:679:37`, `validity.rs:987:36`, `consts.rs:57:13` panics and LLVM 23.1.5 `define` lines (`ptr noundef nonnull` vs. `ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(8)`).
- `support/UnsafeBinderExistentialRegionSoundness.lean` — Kernel-verified Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) formalization (`1,016` LOC) checked on `2026-11-22` with:
  ```console
  lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/UnsafeBinderExistentialRegionSoundness.lean
  ```
  Exit code `0`; `#print axioms` output confirmed zero `sorryAx`, zero `Classical.choice`, zero `Quot.sound`, zero `Lean.ofReduceBool` across all 12 main theorems and `V0Ty.decEq`.

## Revalidation

To cheaply test whether any finding has changed on a newer nightly `rustc`, `Miri`, `joshlf/anneal`, or Lean toolchain:

1. **Re-run the complete `rustc` + LLVM IR + Miri discriminator probe** (takes ~5 seconds with a prebuilt Miri sysroot):
   ```console
   python3 support/probe_unsafe_binders_and_ices.py --out /tmp/ubind_reval.json
   ```
   Check specifically:
   - Whether `part_c_safety_gates_linearity_and_three_ices.{forbid_unsafe_v0_mangling_size_of_ice, ctfe_const_unsafe_binder_ice, gce_wrap_unsafe_binder_ice}` still exit with `rc = 101` (or have transitioned to clean compilation / diagnostics).
   - Whether `part_b_llvm_ir_attrs_mir_and_dangling_miri.llvm_ir_opt_no_prepopulate` still strips `align 8` on `pass_unsafe_binder_unused` (`ptr noundef nonnull`) and whether the compound-binder leakage bug on `pass_newtype_binder` / `pass_wide_slice_binder` / `pass_tuple_binder` / `pass_opt_newtype_binder` has been fixed (i.e., `noalias`, `readonly`, `align 8`, `dereferenceable(8)` disappear).
   - Whether `part_c_safety_gates_linearity_and_three_ices.shared_ref_unsafe_binder_not_copy_e0277` still rejects `unsafe<'a> &'a u64: Copy` (if upstream resolves the `FIXME(unsafe_binder)` in `candidate_assembly.rs:1173` / `structural_traits.rs:258`).
   - Whether `part_a_live_execution_niche_and_miri.miri_default_validity` still panics in `validity.rs` or now validates `unsafe<'a> &'a u64` (and if so, whether `dangling_binder_miri_sb_default` / `misaligned_binder_unused` become UB or pass).
2. **Narrow source-diff check on `rust-lang/rust`** (no build required): diff five files between `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` and target HEAD:
   - `compiler/rustc_middle/src/ty/layout.rs` (`ty_and_layout_pointee_info_at`, `field_ty_or_layout`)
   - `compiler/rustc_symbol_mangling/src/v0.rs` (`print_type` `ty::UnsafeBinder` arm)
   - `compiler/rustc_const_eval/src/interpret/validity.rs` (`ty::UnsafeBinder` arm)
   - `compiler/rustc_ty_utils/src/consts.rs` (`recurse_build` `WrapUnsafeBinder` / `UnwrapUnsafeBinder` arm)
   - `compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs` (`ty::UnsafeBinder` arm for `Copy`/`Clone`)
3. **Re-verify the Lean formalization on any target Lean 4 toolchain:**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/UnsafeBinderExistentialRegionSoundness.lean
   ```
   Confirm exit code `0` and verify every `#print axioms` line reports only `does not depend on any axioms` or `[propext]`.
4. **Check Anneal TCB admission status:** grep `trusted/lean/Trusted/MirAst.lean` and `vendor/lean-miri/Miri/Interpreter/ValidityVisitor.lean` in newer `joshlf/anneal` commits for `UnsafeBinder`, `WrapUnsafeBinder`, and `UnwrapUnsafeBinder`; if any moves out of `.unsupported`, re-audit both `deinitMovedPlace` linearity and compound-binder ABI lowering before lifting the fail-closed boundary.
