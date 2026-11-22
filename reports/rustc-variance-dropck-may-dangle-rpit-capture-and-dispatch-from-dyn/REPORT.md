# `rustc` Subtyping Variance Lattice, Two-Axis `dropck` `#[may_dangle]` and `PhantomData<T>` Soundness, Edition 2024 `RPIT` Precise Lifetime Capturing, and `CoerceUnsized`/`DispatchFromDyn` ABI-Preserving Smart-Pointer Rules

## Summary

This report establishes primary-source, empirical (`rustc` + `Miri`), and kernel-checked Lean `v4.34.1` ground truth for four interconnected type-checking and borrow-checking boundaries in `rustc` (`rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` source audit; `rustc 1.98.0-nightly` / `miri 0.1.0` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` live execution) and maps each boundary onto the fail-closed MIR trust perimeter of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:

1. **Four-Element Subtyping Variance Lattice and Asymmetric Composition (`Variance`, `glb`, `xform`, `E0392`)**: `rustc` infers item generic variances by monotone fixed-point iteration over the 4-element lattice (`Bivariant` `*` at top, incomparable `Covariant` `+` and `Contravariant` `-`, `Invariant` `o` at bottom, with meet `glb` moving strictly toward tighter constraints in at most `2C` updates). While `xform` is associative, involutive on `Contravariant` (`Contravariant.xform(Contravariant) = Covariant`), and right-distributive over `glb`, our Lean mechanization surfaces two algebraic asymmetries inherent to the PLDI'11 `xform` table: `xform` is **non-commutative** (`Invariant.xform(Bivariant) = Invariant ≠ Bivariant = Bivariant.xform(Invariant)`) and **fails left-distributivity over `glb`** (`(Covariant.glb Contravariant).xform Bivariant = Invariant ≠ Bivariant`). Consequently, `rustc_hir_analysis::variance::constraints` treats parameterless leaf types as no-ops rather than composing `xform(ambient, Bivariant)`, and `wfcheck::check_variances_for_type_defn` rejects every remaining unconstrained `Bivariant` ADT parameter with `E0392` (while `variance::solve` promotes unused `FnDef` parameters to `Invariant` and forces all const parameters to `Invariant`).
2. **Two-Axis Soundness Boundary of `dropck`, `#[may_dangle]`, and `PhantomData<T>`**: `rustc`'s drop checker operates via two distinct constraint lists in `DropckConstraint { outlives, dtorck_types, overflows }`. Without `#[may_dangle]`, `TyCtxt::destructor_constraints` pushes every ADT generic parameter directly into `outlives`, forcing every region in `T` to stay live at the drop point (`E0597` even for `Copy` `T = &'a String`). Under `unsafe impl<#[may_dangle] T> Drop`, `pure_wrt_drop` removes `T` from `outlives`, splitting soundness into two orthogonal axes verified both by live `Miri` use-after-free (`UAF`) executions and by an `↔` iff theorem in Lean:
   - **Axis 1 (Destructor-Ownership Obligation)**: When `Drop` invokes `T`'s drop glue (e.g., `PrintOnDrop<'a>`), `PhantomData<T>` pushes `T` onto `dtorck_types` (triggering `E0597` on reverse-declaration-order scopes `let (_guard, s);`), whereas omitting `PhantomData<T>` or substituting `PhantomData<fn() -> T>`—despite `PhantomData<fn() -> T>` having the *exact same* `Covariant` variance as `PhantomData<T>`—short-circuits `trivial_dropck_outlives(ty::FnPtr)` to `true`, compiles cleanly (`rc = 0`), and triggers live `Miri` UAF (`rc = 1`).
   - **Axis 2 (`#[may_dangle]` Non-Access Obligation)**: When `Drop` directly inspects `T` (e.g., formatting or dereferencing `*mut T`), instantiating `T = &'a String` (`Copy`, `trivial_dropck_outlives(ty::Ref) = true`) bypasses even `PhantomData<T>` because `PhantomData<T>` enqueues `T` in `dtorck_types` rather than `outlives`. The program compiles cleanly (`rc = 0`) and triggers live `Miri` UAF (`rc = 1`).
3. **Edition 2021 vs. Edition 2024 `RPIT` (`impl Trait`) Lifetime Capture and `use<...>`**: In `rustc_hir_analysis::collect::resolve_bound_vars::opaque_captures_all_in_scope_lifetimes`, any explicit `hir::GenericBound::Use(..)` bound overrides edition defaults (`false` for implicit capture-all, capturing strictly what `use<...>` names in both Edition 2021 and Edition 2024). Without `use<...>`, `AsyncFn`, `TyAlias` (TAIT), and trait/impl `RPITIT` capture all in-scope lifetimes in both editions, whereas free-function and inherent-method `RPIT` transition at `opaque.span.at_least_rust_2024()` from *no* implicit capture of unmentioned lifetimes in Edition 2021 to *capturing all* in-scope lifetimes in Edition 2024 (`E0506` on mutating a borrowed local while the opaque token lives, opted out via `+ use<>`).
4. **`CoerceUnsized` vs. `DispatchFromDyn` ABI-Preserving Smart-Pointer Rules**: Both built-in traits whitelist `PhantomData` fields before inspecting field changes, and both reject multiple changed fields with `E0375` (including custom generic ZSTs such as `MyZst<T>` that vary across `T -> U`). However, `CoerceUnsized` permits arbitrary unchanged fields (including non-ZST `u64` payloads), lifetime shrinking, mutability weakening, and `#[repr(C)]`, whereas `DispatchFromDyn` enforces strict raw-pointer ABI transparency: it rejects `#[repr(C)]` and `#[repr(packed)]`, rejects extra non-ZST fields (`E0378`), rejects over-aligned ZSTs such as `#[repr(align(16))] struct Align16Zst;` (`E0378`), and rejects unchanged ZSTs that mention type or const generics (`E0378`, preventing soundness holes via ZST transmutation). Only `PhantomData` and 1-byte-aligned non-generic ZSTs (`layout.is_1zst() && !ty_a.has_non_region_param()`) may accompany the single coerced pointer field.
5. **Anneal Trusted-Boundary Integration**: At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` erases regions inside `.ref`, and fails closed (`.unsupported`) on `StatementKind::AscribeUserType(..., ty::Variance)`, `TerminatorKind::Drop`, `Rvalue::Cast` (`PointerCoercion::Unsize`), `TyKind::Dynamic`, `TyKind::FnPtr`, non-fieldless-enum ADTs, and `ProjectionElem::OpaqueCast`. Any verified Rust compiler or MIR-extension pass admitting generic containers with `Drop`, `impl Trait` opaques, or `dyn Trait` dispatch receivers must inherit these exact `rustc` typeck/borrowck invariants as explicit soundness preconditions.

## Applicability

This report examines four durable upstream subjects and how they relate to one another:

- **Primary source specification (`rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`)**: Direct inspection of the compiler crates `rustc_type_ir`, `rustc_hir_analysis`, `rustc_borrowck`, `rustc_middle`, `rustc_traits`, `rustc_trait_selection`, `rustc_ty_utils`, and `library/core` at upstream HEAD as of `2026-11-22`. All source line numbers in **Findings** and **Evidence** refer to this exact commit unless explicitly noted.
- **Empirical execution toolchain (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`)**: Live compilation, native execution, and `Miri` interpretation via `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (LLVM `22.1.6`, host and target `x86_64-unknown-linux-gnu`) and `miri 0.1.0 (14210df0e2 2026-05-31)` using `support/probe_variance_dropck_rpit_dyn.py` (full scrubbed output archived in `support/probe_variance_dropck_rpit_dyn_results.json`).
  - **Cross-revision continuity check (`14210df0e` vs. `342d74463`)**: Direct file-level comparison between the executed toolchain revision (`14210df0e`, `2026-05-31`) and audited upstream HEAD (`342d74463`, `2026-11-22`) confirms that all core mechanisms tested empirically (`Variance::xform`, `fn glb`, `adt_dtorck_constraint`, `trivial_dropck_outlives`, `opaque_captures_all_in_scope_lifetimes`, and `visit_implementation_of_dispatch_from_dyn` including `is_phantom_data`, `is_1zst()`, `!has_non_region_param()`, and `#[repr(C)]`/`#[repr(packed)]` rejection) are shared across both revisions. One concrete upstream addition appears between the two revisions: `compiler/rustc_hir_analysis/src/variance/terms.rs` at `342d74463` adds a third hardcoded lang-item variance entry, `covariant_unsafe_cell_type -> [ty::Covariant]`, alongside `phantom_data -> [ty::Covariant]` and `unsafe_cell_type -> [ty::Invariant]`, which was not yet present in `terms.rs` at `14210df0e`.
- **Anneal trusted boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)**: Direct inspection of `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/correspondence/Trusted/Correspondence.lean`, `trusted/audit/TrustedBoundary.lean`, and `trusted/rustc-capture/src/driver.rs` establishes which of these four `rustc` mechanisms are currently erased or rejected fail-closed by Anneal's MIR semantics and what invariants future extensions must preserve. Note that `trusted/rustc-capture/src/driver.rs:25` pins `1.98.0-nightly (f8a08b688 2026-05-30)`, adjacent to our executed `1.98.0-nightly (14210df0e 2026-05-31)`.
- **Mechanized proof checker (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)**: All algebraic, drop-schedule, RPIT-capture, and smart-pointer ABI theorems in `support/VarianceDropckAndDispatchFromDynSoundness.lean` are kernel-checked under Lean `v4.34.1` with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` and audited via `#print axioms` to depend strictly on `[]` or `[propext]` (zero `Classical.choice`, zero `Quot.sound`, zero `sorryAx`, zero `Lean.ofReduceBool`).

**Feature flags and edition scope**:
- Part A (Variance & `E0392`) uses stable Rust (`--edition=2024`) for all 12 type constructors, all 5 lifetime-variance checks, and both `E0392` rejections; the compiler-internal `#[rustc_dump_variances]` dump uses `#![feature(rustc_attrs)]`.
- Part B (`dropck` & `#[may_dangle]`) uses `#![feature(dropck_eyepatch)]` for the `unsafe impl<#[may_dangle] T> Drop` cases (the same unstable compiler mechanism used by `alloc::boxed::Box`, `alloc::vec::Vec`, and `core::ptr::Unique` in the standard library) and stable Rust for the non-`#[may_dangle]` `E0597` control.
- Part C (`RPIT` capture) uses stable Rust under both `--edition=2021` and `--edition=2024` (precise capturing `use<...>` is stable in both editions).
- Part D (`CoerceUnsized` & `DispatchFromDyn`) uses `#![feature(unsize, coerce_unsized, dispatch_from_dyn, arbitrary_self_types)]` to exercise the exact compiler coherence rules that govern `Box`, `Rc`, `Arc`, `Pin`, `&T`, `&mut T`, and `#[derive(CoercePointee)]` smart pointers.

## Findings

### 1. Four-Element Subtyping Variance Lattice, `xform` Algebra, and `E0392`

Basis: source + execution + derived (mechanized Lean proof)

#### 1.1 Compiler Lattice Representation and Fixed-Point Solver

In `compiler/rustc_type_ir/src/lib.rs:260-336`, `rustc` defines variance as a 4-element enum with 1-character `Debug` tokens used by `#[rustc_dump_variances]` (`compiler/rustc_hir_analysis/src/variance/dump.rs:8-24`):

```rust
pub enum Variance {
    Covariant,     // "+" : T<A> <: T<B> iff A <: B
    Invariant,     // "o" : T<A> <: T<B> iff B == A
    Contravariant, // "-" : T<A> <: T<B> iff B <: A
    Bivariant,     // "*" : T<A> <: T<B> unconditionally
}
```

The solver in `compiler/rustc_hir_analysis/src/variance/solve.rs:17-35` orders the lattice with `Bivariant` (`*`) at the top (least restrictive / most permissive subtyping), `Covariant` (`+`) and `Contravariant` (`-`) as incomparable middle elements, and `Invariant` (`o`) at the bottom (most restrictive):

```text
          Bivariant (*)        [least restrictive; identity of glb]
           /         \
   Contravariant (-)  Covariant (+)
           \         /
          Invariant (o)        [most restrictive; absorber of glb]
```

Equivalently, under the **constraint-strength** partial order (`Bivariant < {Covariant, Contravariant} < Invariant`), `glb` is the join moving monotonically upward in restrictiveness:

| `glb(v1, v2)` | `Bivariant (*)` | `Covariant (+)` | `Contravariant (-)` | `Invariant (o)` |
| :--- | :--- | :--- | :--- | :--- |
| **`Bivariant (*)`** | `Bivariant` | `Covariant` | `Contravariant` | `Invariant` |
| **`Covariant (+)`** | `Covariant` | `Covariant` | `Invariant` | `Invariant` |
| **`Contravariant (-)`** | `Contravariant` | `Invariant` | `Contravariant` | `Invariant` |
| **`Invariant (o)`** | `Invariant` | `Invariant` | `Invariant` | `Invariant` |

Context-to-position composition `a.xform(b)` (`compiler/rustc_type_ir/src/lib.rs:304-324`, implementing Figure 1 of Tate, Leung, and Lerner, PLDI'11, *"Taming the Wildcards: Combining Definition- and Use-Site Variance"*) computes the variance of a parameter occurring at inner variance `b` inside an ambient context of variance `a`:

| `a.xform(b)` | `b = Bivariant (*)` | `b = Covariant (+)` | `b = Contravariant (-)` | `b = Invariant (o)` |
| :--- | :--- | :--- | :--- | :--- |
| **`a = Bivariant (*)`** | `Bivariant` | `Bivariant` | `Bivariant` | `Bivariant` |
| **`a = Covariant (+)`** | `Bivariant` | `Covariant` | `Contravariant` | `Invariant` |
| **`a = Contravariant (-)`** | `Bivariant` | `Contravariant` | `Covariant` | `Invariant` |
| **`a = Invariant (o)`** | `Invariant` | `Invariant` | `Invariant` | `Invariant` |

**Mechanized algebraic properties and non-obvious asymmetries** (`support/VarianceDropckAndDispatchFromDynSoundness.lean:81-166`):
- **Monoid & involution laws**: `xform` is associative (`xform_assoc`), has two-sided identity `Covariant` (`xform_cov_left`, `xform_cov_right`), satisfies `Contravariant.xform(Contravariant) = Covariant` (`xform_contra_contra_eq_cov`) and full involution `Contravariant.xform(Contravariant.xform(v)) = v` (`xform_contra_involutive`), and `glb` forms a bounded semilattice (`glb_comm`, `glb_assoc`, `glb_idem`, `glb_biv_left`, `glb_inv_left`, `glb_least_upper_constraint`).
- **Right-distributivity holds, left-distributivity fails**: `xform a (glb b c) = glb (xform a b) (xform a c)` holds unconditionally (`xform_distrib_glb_right`), guaranteeing monotonicity of `SolveContext::evaluate` (`solve.rs:151-163`) and `O(2C)` termination because each inferred variable can descend the height-2 lattice at most twice (`solve.rs:75-103`). Conversely, **left-distributivity fails** (`xform_not_distrib_glb_left`):
  $$\mathrm{xform}(\mathrm{glb}(\mathrm{Cov}, \mathrm{Contra}), \mathrm{Biv}) = \mathrm{xform}(\mathrm{Inv}, \mathrm{Biv}) = \mathrm{Inv} \neq \mathrm{Biv} = \mathrm{glb}(\mathrm{xform}(\mathrm{Cov}, \mathrm{Biv}), \mathrm{xform}(\mathrm{Contra}, \mathrm{Biv}))$$
  and **`xform` is non-commutative** (`xform_not_comm`): `Invariant.xform(Bivariant) = Invariant`, whereas `Bivariant.xform(Invariant) = Bivariant`.
- **Direct compiler consequence**: Because `Invariant.xform(Bivariant) = Invariant`, an inference walk over `&'a mut u8` must *not* emit `xform(ambient, Bivariant)` for leaf types that do not mention a generic parameter. Indeed, `compiler/rustc_hir_analysis/src/variance/constraints.rs:215-224` executes a complete no-op on leaf types (`Bool`, `Char`, `Int`, `Uint`, `Float`, `Str`, `Never`, `Foreign`), emitting `add_constraint(current, data.index, variance)` strictly upon reaching `ty::Param` (`constraints.rs:303-305`) or `ty::ReEarlyParam` (`constraints.rs:445-447`). In Lean, `inferVariance_of_not_mentionsParam` and `inferVariance_ambient_factor` prove that ambient factoring `inferVariance ambient e = xform ambient (inferVariance .covariant e)` holds if and only if `mentionsParam e = true`, while parameterless expressions remain `Bivariant` regardless of `ambient`.

#### 1.2 Hardcoded Lang-Item Overrides and Constructor Rules

Before fixed-point iteration starts (`solve.rs:49-65`), `terms.rs:109-123` seeds and locks the variance of three compiler lang items (dropping all generated constraints on those slots so field inspection cannot overwrite them):

```rust
let all = [
    (lang_items.phantom_data(), vec![ty::Covariant]),
    (lang_items.unsafe_cell_type(), vec![ty::Invariant]),
    (lang_items.covariant_unsafe_cell_type(), vec![ty::Covariant]),
];
```

For all other constructors, `constraints.rs:208-490` generates constraints as follows:
- **`&'r T` (`ty::Ref(r, T, Not)`)** (`constraints.rs:230-233, 486-488`): region `'r` gets `variance`; pointee `T` gets `variance` (covariant in both `'r` and `T`).
- **`&'r mut T` (`ty::Ref(r, T, Mut)`)** (`constraints.rs:230-233, 481-484`): region `'r` gets `variance` (**covariant in `'r`**); pointee `T` gets `invariant(variance)` (**invariant in `T`**).
- **`*const T` / `*mut T` (`ty::RawPtr`)** (`constraints.rs:249-251, 474-490`): `*const T` passes `variance` (covariant); `*mut T` passes `invariant(variance)` (invariant).
- **`fn(Args...) -> Ret` (`ty::FnPtr` / `ty::FnDef`)** (`constraints.rs:307-309, 423-434`): each input parameter gets `contravariant(variance)`; return type gets `variance`. Nested `fn(fn(T))` therefore evaluates `Covariant.xform(Contravariant).xform(Contravariant) = Covariant`.
- **ADTs (`ty::Adt(def, args)`)** (`constraints.rs:259-261, 352-401`): for each argument `i`, composes `xform(variance, variance_decl[i])`. Note that generic `where`-clauses on structs/enums are deliberately ignored during variance inference (`constraints.rs:109-113`), though they *do* participate in `E0392` constrained-parameter checks (`wfcheck.rs:2100`).
- **Projections, opaque aliases, and trait objects (`ty::Alias`, `ty::Dynamic`)** (`constraints.rs:263-301`): `Projection`, `Inherent`, and `Opaque` alias args are forced `invariant(variance)` via `add_constraints_from_invariant_args`; `dyn Trait<Args> + 'r` is covariant in `'r` and invariant in principal trait args and projection bounds.
- **Post-solve overrides (`solve.rs:105-149`)**: Every const generic parameter (including parent const parameters) is unconditionally overwritten to `ty::Invariant` (`enforce_const_invariance`), and any `ty::Bivariant` parameter on a `FnDef` (functions are allowed to have unused generic parameters) is promoted to `ty::Invariant` (`solve.rs:135-144`).

#### 1.3 Empirical 12-Constructor Matrix, Lifetime Variance, `#[rustc_dump_variances]`, and `E0392`

Executing `support/probe_variance_dropck_rpit_dyn.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` verifies all 12 type-parameter constructors via two-sided coercion tests (`Wrap<&'static u8> -> Wrap<&'a u8>` for covariance and `Wrap<&'a u8> -> Wrap<&'static u8>` for contravariance), matching `twelve_constructor_variances` in Lean 12/12:

| # | Constructor (`Wrap<T>`) | `cov` (`'static -> 'a`) | `contra` (`'a -> 'static`) | Empirical Variance | `rustc` Rule / Lean `inferVariance` |
| :-: | :--- | :-: | :-: | :--- | :--- |
| 1 | `&'b T` | pass (`rc=0`) | fail (`rc=1`) | **Covariant (`+`)** | `constraints.rs:230-233, 486-488` |
| 2 | `&'b mut T` | fail (`rc=1`) | fail (`rc=1`) | **Invariant (`o`)** | `constraints.rs:230-233, 481-484` |
| 3 | `*const T` | pass (`rc=0`) | fail (`rc=1`) | **Covariant (`+`)** | `constraints.rs:249-251, 486-488` |
| 4 | `*mut T` | fail (`rc=1`) | fail (`rc=1`) | **Invariant (`o`)** | `constraints.rs:249-251, 481-484` |
| 5 | `fn(T)` | fail (`rc=1`) | pass (`rc=0`) | **Contravariant (`-`)** | `constraints.rs:429-432` |
| 6 | `fn() -> T` | pass (`rc=0`) | fail (`rc=1`) | **Covariant (`+`)** | `constraints.rs:433` |
| 7 | `fn(fn(T))` | pass (`rc=0`) | fail (`rc=1`) | **Covariant (`+`)** | `Contra.xform(Contra) = Cov` |
| 8 | `UnsafeCell<T>` | fail (`rc=1`) | fail (`rc=1`) | **Invariant (`o`)** | `terms.rs:113` (lang-item override) |
| 9 | `PhantomData<T>` | pass (`rc=0`) | fail (`rc=1`) | **Covariant (`+`)** | `terms.rs:112` (lang-item override) |
| 10 | `PhantomData<fn(T)>` | fail (`rc=1`) | pass (`rc=0`) | **Contravariant (`-`)** | `Cov.xform(Contra) = Contra` |
| 11 | `PhantomData<fn() -> T>` | pass (`rc=0`) | fail (`rc=1`) | **Covariant (`+`)** | `Cov.xform(Cov) = Cov` |
| 12 | `PhantomData<fn(T) -> T>` | fail (`rc=1`) | fail (`rc=1`) | **Invariant (`o`)** | `glb(Contra, Cov) = Inv` |

Five additional lifetime-parameter probes confirm the split between outer reference lifetime variance and inner pointee variance:
- `&'a u8` -> **Covariant** (`cov_ok=true, contra_ok=false`)
- `&'a mut u8` -> **Covariant in `'a`** (`cov_ok=true, contra_ok=false`), even though `&'a mut T` is invariant in `T`
- `fn(&'a u8)` -> **Contravariant in `'a`** (`cov_ok=false, contra_ok=true`)
- `fn(fn(&'a u8))` -> **Covariant in `'a`** (`cov_ok=true, contra_ok=false`)
- `&'static mut &'a u8` -> **Invariant in `'a`** (`cov_ok=false, contra_ok=false`), because `'a` occurs inside the mutable pointee position (`Invariant.xform(Covariant) = Invariant`)

Direct internal compiler variance dumping via `#[rustc_dump_variances]` (`variance/dump.rs:26-53`) on:

```rust
#[rustc_dump_variances]
pub struct Showcase<'a, 'b, A, B, C, D, E, F>(
    &'a A,
    &'b mut B,
    fn(C) -> D,
    fn(fn(E)),
    UnsafeCell<F>,
    PhantomData<fn(C) -> A>,
);
```

emits the exact compiler-internal variance vector:

```text
error: ['a: +, 'b: +, A: +, B: o, C: -, D: +, E: +, F: o]
```

**`E0392` enforcement on unconstrained bivariant ADT parameters**: In `compiler/rustc_hir_analysis/src/check/wfcheck.rs:2081-2172` (invoked for every struct, union, and enum by `check/check.rs:827, 924`), `check_variances_for_type_defn` seeds `constrained_parameters` with every parameter whose solved variance is `!= ty::Bivariant`, adds parameters constrained by `where`-clause trait/projection bounds via `identify_constrained_generic_params`, and calls `report_bivariance` (`E0392`) for every remaining unconstrained `Bivariant` parameter. Empirically, both `pub struct Unused<T>(u8);` and `pub struct UnusedLt<'a>(u8);` fail compilation (`compile_rc = 1`) with `error[E0392]: type parameter 'T' is never used` and `error[E0392]: lifetime parameter ''a' is never used`, respectively.

---

### 2. Two-Axis `dropck`, `#[may_dangle]`, and `PhantomData<T>` Soundness Boundary

Basis: source + execution + derived (mechanized Lean proof)

#### 2.1 How Borrowck Liveness and `dropck_outlives` Separate `outlives` from `dtorck_types`

Rust drops local variables within a lexical scope in **reverse declaration order**. During NLL borrow checking (`compiler/rustc_borrowck/src/type_check/liveness/trace.rs:400-455`), `LivenessComputation::compute` separates two distinct kinds of liveness for each local variable `local` of type `local_ty`:

1. **Use-liveness (`use_live_at`, lines `421-429`)**: At every CFG point where `local` may still be read or passed by a future ordinary use, `make_all_regions_live` marks **all** free regions appearing anywhere in `local_ty` as live.
2. **Drop-liveness (`drop_live_at`, lines `430-454`)**: At CFG points after `local`'s last ordinary use where `local` (or a subpart tracked by `MoveData`) remains initialized and will reach a `Drop` terminator (`compute_drop_live_points_for`, lines `534-563`), borrowck does *not* unconditionally require all regions in `local_ty` to stay live. Instead, `dropck_local` (`trace.rs:785-830`) invokes the `DropckOutlives { dropped_ty: local_ty }` query and marks live **only** the regions inside `dropck_result.kinds`.

The `DropckOutlives` query (`compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs:108-253`) maintains a worklist `ty_stack` and accumulates `DropckConstraint { outlives, dtorck_types, overflows }`:
- **`outlives`** (unconditional drop-liveness): Every generic argument placed in `outlives` is appended straight to `result.kinds` (`dropck_outlives.rs:180`), forcing all regions inside it to outlive the `Drop` terminator regardless of whether that type has a destructor.
- **`dtorck_types`** (recursive destructor-conditional expansion): Every type placed in `dtorck_types` is normalized and pushed onto `ty_stack` (`dropck_outlives.rs:195-248`) to be re-inspected by `dtorck_constraint_for_ty_inner` (`dropck_outlives.rs:258-427`), which immediately **short-circuits and adds nothing** whenever `trivial_dropck_outlives(tcx, ty)` returns `true` (`dropck_outlives.rs:271-273`).

Look at how the three compiler functions interact to create the exact two-axis boundary:

1. **`trivial_dropck_outlives`** (`compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs:28-95`):
   - Returns **`true`** (needs no regions live for drop) for `Bool`, `Int`, `Uint`, `Float`, `Char`, `Str`, `Never`, `FnDef`, **`FnPtr`**, **`RawPtr`**, **`Ref`**, `[T; 0]`, and `ManuallyDrop<T>`.
   - Returns **`false`** for all other ADTs—explicitly including **`PhantomData<T>`**, as documented inline (`dropck_outlives.rs:74-77`): *"PhantomData doesn't have a dtor, but it is considered to own its content, so it is non-trivial."*
2. **`adt_dtorck_constraint`** (`compiler/rustc_traits/src/dropck_outlives.rs:32-65`):
   - For `PhantomData<X>` (`lines 40-52`): returns `DropckConstraint { outlives: vec![], dtorck_types: vec![X], overflows: vec![] }` — crucially placing `X` into **`dtorck_types`**, **not** `outlives`!
   - For any other ADT (`lines 54-60`): walks every field through `dtorck_constraint_for_ty_inner` and appends `tcx.destructor_constraints(def)` directly into **`result.outlives`**.
3. **`TyCtxt::destructor_constraints`** (`compiler/rustc_middle/src/ty/util.rs:466-538`):
   - If the ADT has no `Drop` impl, returns `vec![]`.
   - If the ADT has a `Drop` impl, inspects each generic parameter on the `Drop` impl and includes only parameters where **`!pure_wrt_drop`** (`util.rs:515, 521, 527`). Marking a parameter `#[may_dangle]` (under `#![feature(dropck_eyepatch)]`, requiring an `unsafe impl` of `Drop`) sets `pure_wrt_drop = true`, removing that parameter from `destructor_constraints` (and hence from `outlives`).

#### 2.2 Empirical Two-Axis Matrix (`rustc` + Live `Miri` Execution)

The following table summarizes all seven live `rustc 1.98.0-nightly` + `miri 0.1.0` experiments in `support/probe_variance_dropck_rpit_dyn.py` (`support/probe_variance_dropck_rpit_dyn_results.json`), comparing reverse declaration order `let (_guard, s);` (where `s` drops *before* `_guard`) against safe declaration order `let (s, _guard);`:

| Case | Container Definition & `Drop` Impl | Instantiated `T` | Scope Order | `rustc` Result | `Miri` Result | Soundness Role |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Axis 1a** | `MyBox<T>(*mut T)`, `unsafe impl<#[may_dangle] T> Drop` (runs `T::drop`) | `PrintOnDrop<'a>` | `(_guard, s)` | **Compiles (`rc=0`)** | **UB UAF (`rc=1`)** at `PrintOnDrop::drop` | Missing `PhantomData<T>` hides `T::drop` ownership |
| **Axis 1b** | `MyBox<T>(*mut T, PhantomData<T>)`, `#[may_dangle] T` | `PrintOnDrop<'a>` | `(_guard, s)` | **Rejected `E0597` (`rc=1`)** | N/A (compile error) | `PhantomData<T>` enqueues `T` in `dtorck_types` -> catches `PrintOnDrop::drop` |
| **Axis 1c** | `MyBox<T>(*mut T, PhantomData<T>)`, `#[may_dangle] T` | `PrintOnDrop<'a>` | `(s, _guard)` | **Compiles (`rc=0`)** | **Pass (`rc=0`)**, `SAFE_DROP_LEN=14` | Positive control: `_guard` drops before `s` |
| **Axis 1d** | `MyBox<T>(*mut T, PhantomData<fn() -> T>)`, `#[may_dangle] T` | `PrintOnDrop<'a>` | `(_guard, s)` | **Compiles (`rc=0`)** | **UB UAF (`rc=1`)** at `PrintOnDrop::drop` | Identical `Covariant` variance to `PhantomData<T>`, but `FnPtr` is trivial for `dropck` |
| **Axis 2a** | `InspectBox<T: Display>(*mut T, PhantomData<T>)`, `#[may_dangle] T` (directly formats `*self.0`) | `&'a String` (`Copy`) | `(_guard, s)` | **Compiles (`rc=0`)** | **UB UAF (`rc=1`)** at `<&String as Display>::fmt` | Even WITH `PhantomData<T>`, `trivial_dropck_outlives(&String)=true` permits dangling `&'a String` |
| **Axis 2b** | `InspectBox<T: Display>(*mut T, PhantomData<T>)`, **plain `impl<T: Display> Drop`** (no `#[may_dangle]`) | `&'a String` (`Copy`) | `(_guard, s)` | **Rejected `E0597` (`rc=1`)** | N/A (compile error) | Without `#[may_dangle]`, `destructor_constraints` puts `T` in `outlives` directly |
| **Sound Control** | `SoundBox<T>(*mut T, PhantomData<T>)`, `#[may_dangle] T` (only deallocates `Box::from_raw`, never reads `T`) | `&'a String` (`Copy`) | `(_guard, s)` | **Compiles (`rc=0`)** | **Pass (`rc=0`)**, `SOUND_MAY_DANGLE_COPY_OK` | Sound use of `#[may_dangle]` + `PhantomData<T>` on trivially-droppable `T` |

**Key structural takeaways verified by the trace**:
- **Why Axis 1d (`PhantomData<fn() -> T>`) fails despite identical variance**: `PhantomData<T>` and `PhantomData<fn() -> T>` have identical `Covariant` variance (`Part A` rows 9 and 11), so variance-only markers are *not* interchangeable with ownership markers. Under `adt_dtorck_constraint`, `PhantomData<fn() -> T>` pushes `fn() -> PrintOnDrop<'a>` onto `dtorck_types`, which immediately hits `trivial_dropck_outlives(ty::FnPtr(..)) == true` (`dropck_outlives.rs:41`), dropping all constraints on `'a`. At runtime, `Miri` catches `Undefined Behavior: constructing invalid value of type &std::string::String: encountered a dangling reference (use-after-free)` inside `<PrintOnDrop<'_> as Drop>::drop`.
- **Why Axis 2a (`InspectBox` with `PhantomData<T>`) fails**: `PhantomData<T>` only protects destructors of `T` itself (via `dtorck_types`), *never* direct inspection of `T` by the container's own `Drop` body. When `T = &'a String`, `trivial_dropck_outlives(ty::Ref(..)) == true` (`dropck_outlives.rs:45`), so `dropck` emits zero outlives obligations for `'a`. Calling `format!("{}", Box::from_raw(self.0))` in `InspectBox::drop` immediately triggers `Miri` UAF in `<&std::string::String as core::fmt::Display>::fmt`.
- **Mechanized Two-Axis Equivalence Theorem (`support/VarianceDropckAndDispatchFromDynSoundness.lean:663-755`)**: Modeling reverse-declaration-order scope destruction (`execDropSchedule` over `declOrder.reverse`) and `rustc`'s `dropckAccepts` predicate, we prove the exact bidirectional characterization:

```lean
theorem dropck_may_dangle_uaf_free_iff_ownership_and_no_direct_read
    (c : ContainerSpec) (hmd : c.hasMayDangle = true) :
    ContainerUafFreeUnderDropck c ↔
      ((c.dropRunsTDtor = true → c.hasPhantomOwnsT = true) ∧
       c.dropDirectlyReadsT = false)
```

together with `dropck_without_may_dangle_always_uaf_free` (proving `hasMayDangle = false` enforces UAF-freedom unconditionally) and constructive counterexamples `ce1_phantom_fn_misses_dropck_ownership_uaf` and `ce2_direct_read_of_copy_ref_under_may_dangle_bypasses_phantom_t`. This establishes that `unsafe impl<#[may_dangle] T> Drop` carries **two independent proof obligations**: (1) an ownership declaration (`PhantomData<T>`) whenever `T`'s drop glue may execute, and (2) an implementation-level non-access invariant forbidding direct reads of `T` (outside calling `T`'s destructor).

---

### 3. Edition 2021 vs. Edition 2024 `RPIT` (`impl Trait`) Lifetime Capturing and `use<...>`

Basis: source + execution + derived (mechanized Lean proof)

#### 3.1 Exact Compiler Predicate in `resolve_bound_vars.rs`

In `compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs:322-331`, `rustc` decides whether an opaque return type (`impl Trait`) implicitly captures all in-scope lifetime parameters through a single 10-line match:

```rust
fn opaque_captures_all_in_scope_lifetimes<'tcx>(opaque: &'tcx hir::OpaqueTy<'tcx>) -> bool {
    match opaque.origin {
        // if the opaque has the `use<...>` syntax, the user is telling us that they only want
        // to account for those lifetimes, so do not try to be clever.
        _ if opaque.bounds.iter().any(|bound| matches!(bound, hir::GenericBound::Use(..))) => false,
        hir::OpaqueTyOrigin::AsyncFn { .. } | hir::OpaqueTyOrigin::TyAlias { .. } => true,
        _ if opaque.span.at_least_rust_2024() => true,
        hir::OpaqueTyOrigin::FnReturn { in_trait_or_impl, .. } => in_trait_or_impl.is_some(),
    }
}
```

When `opaque_captures_all_in_scope_lifetimes(opaque)` returns `true`, `BoundVarContext::visit_opaque_ty` (`resolve_bound_vars.rs:527-618`) walks every enclosing `Scope::Binder` and `Scope::Root` parent generic item, remapping every in-scope lifetime parameter (both early-bound and late-bound) into duplicate lifetime generics owned by the opaque `DefId` and recording them in `rbv.opaque_captured_lifetimes`. When an explicit `use<...>` bound is present, `opaque_captures_all_in_scope_lifetimes` returns `false`, and `visit_precise_capturing_arg` (`resolve_bound_vars.rs:659-699`) resolves only the explicitly listed lifetime, type, and const parameters (rejecting `'_`, `'static`, and `Self` type aliases inside `use<...>`).

Downstream, `variance_of_opaque` (`compiler/rustc_hir_analysis/src/variance/mod.rs:97-227`) initializes type and const generics of opaques to `ty::Invariant` and parent lifetimes to `ty::Bivariant` (except trait parameters on `RPITIT` under `ForceCaptureTraitArgs::Yes`), then promotes any lifetime mentioned in explicit item bounds (or duplicated into the opaque's own generics) to `ty::Invariant`. Finally, `compiler/rustc_hir_analysis/src/check/check.rs:644-679` validates every `use<...>` list against `tcx.variances_of(opaque_def_id)`, asserting that every captured parameter has `ty::Invariant` and diagnosing any uncaptured lifetime that was implicitly mentioned (`diagnostics::LifetimeNotCaptured`).

Notably, the Edition 2024 check tests **`opaque.span.at_least_rust_2024()`** (`resolve_bound_vars.rs:328`), meaning macro-generated `impl Trait` return types follow the edition of the `opaque.span` token rather than unconditionally inheriting the caller crate's edition.

#### 3.2 Empirical Edition 2021 vs. Edition 2024 Matrix (`rustc 1.98.0-nightly`)

Testing the canonical mutation-while-holding-opaque-token pattern (`let tok = make_opaque(&x); x += 1; drop(tok);`) across free functions, inherent methods, and trait methods (`RPITIT`) yields exact agreement with `opaque_captures_all_in_scope_lifetimes` and our Lean theorem `rpit_edition_2021_vs_2024_delta` (`support/VarianceDropckAndDispatchFromDynSoundness.lean:773-809`):

| Probe Case | Signature / Origin | Edition | `rustc` Result | Output / Diagnostic | Captures `'a` / `&self`? |
| :--- | :--- | :---: | :---: | :--- | :---: |
| `ed2021_rpit_free_does_not_capture_a` | `fn make_opaque<'a>(_x: &'a i32) -> impl Sized` | 2021 | **Compiles & runs (`rc=0`)** | `RPIT_NO_CAPTURE_X=2` | **No** |
| `ed2024_rpit_free_captures_a_by_default` | `fn make_opaque<'a>(_x: &'a i32) -> impl Sized` | 2024 | **Rejected `E0506` (`rc=1`)** | `cannot assign to 'x' because it is borrowed` + Rust 2024 capture note + `help: impl Sized + use<>` | **Yes** |
| `ed2024_rpit_use_empty_opts_out` | `fn make_opaque<'a>(_x: &'a i32) -> impl Sized + use<>` | 2024 | **Compiles & runs (`rc=0`)** | `RPIT_USE_EMPTY_X=2` | **No** (`use<>` override) |
| `ed2021_rpit_use_empty_ok` | `fn make_opaque<'a>(_x: &'a i32) -> impl Sized + use<>` | 2021 | **Compiles & runs (`rc=0`)** | `RPIT_USE_EMPTY_X=2` | **No** |
| `ed2024_rpit_use_a_captures_a` | `fn make_opaque<'a>(_x: &'a i32) -> impl Sized + use<'a>` | 2024 | **Rejected `E0506` (`rc=1`)** | `cannot assign to 'x' because it is borrowed` | **Yes** (`use<'a>`) |
| `ed2021_rpit_use_a_captures_a` | `fn make_opaque<'a>(_x: &'a i32) -> impl Sized + use<'a>` | 2021 | **Rejected `E0506` (`rc=1`)** | `cannot assign to 'x' because it is borrowed` | **Yes** (`use<'a>`) |
| `ed2021_inherent_method_rpit_does_not_capture_self` | `impl S { fn make(&self) -> impl Sized }` | 2021 | **Compiles & runs (`rc=0`)** | `INHERENT_METHOD_X=2` | **No** (`in_trait_or_impl = None`) |
| `ed2024_inherent_method_rpit_captures_self` | `impl S { fn make(&self) -> impl Sized }` | 2024 | **Rejected `E0506` (`rc=1`)** | `cannot assign to 's.0' because it is borrowed` + Rust 2024 note + `help: + use<>` | **Yes** |
| `ed2021_rpitit_trait_method_already_captures_self` | `trait Maker { fn make(&self) -> impl Sized; }` | 2021 | **Rejected `E0506` (`rc=1`)** | `cannot assign to 's.0' because it is borrowed` | **Yes** (`in_trait_or_impl = Some(...)`) |
| `ed2024_rpitit_trait_method_captures_self` | `trait Maker { fn make(&self) -> impl Sized; }` | 2024 | **Rejected `E0506` (`rc=1`)** | `cannot assign to 's.0' because it is borrowed` | **Yes** |

Notice the subtle distinction between inherent methods and trait methods in Edition 2021: an inherent `impl S` method has `in_trait_or_impl == None` (so it does *not* capture `&self`'s elided lifetime in Edition 2021, transitioning at Edition 2024), whereas a trait method (`RPITIT`) has `in_trait_or_impl == Some(RpitContext::Trait | RpitContext::Impl)` and already captured `&self`'s lifetime in Edition 2021.

---

### 4. `CoerceUnsized` vs. `DispatchFromDyn` ABI-Preserving Smart-Pointer Rules

Basis: source + execution + derived (mechanized Lean proof)

#### 4.1 Exact Coherence Split in `coherence/builtin.rs`

Both `CoerceUnsized` (`library/core/src/ops/unsize.rs:34-72`) and `DispatchFromDyn` (`library/core/src/ops/unsize.rs:74-137`) are compiler-checked built-in lang-item traits dispatched by `compiler/rustc_hir_analysis/src/coherence/builtin.rs:32-54`. Although they often appear together on smart pointers (`Box`, `Rc`, `Arc`, `Pin`, custom `MyPtr<T>`), their compiler checks enforce fundamentally different invariants:

- **`CoerceUnsized` (`coerce_unsized_info`, `builtin.rs:655-888`)** governs *unsizing coercions* (thin-to-wide pointer conversion, e.g., `Ptr<[T; N]> -> Ptr<[T]>` or `Ptr<Concrete> -> Ptr<dyn Trait>`), where codegen explicitly constructs a new struct value by unsizing the single changed field and copying all unchanged fields verbatim (`CustomCoerceUnsized::Struct(field_idx)`, `builtin.rs:847`).
- **`DispatchFromDyn` (`visit_implementation_of_dispatch_from_dyn`, `builtin.rs:287-463`)** governs *dynamic dispatch receivers* (`fn method(self: SmartPtr<Self>)` invoked on `SmartPtr<dyn Trait>`), where the vtable shim expects a narrow pointer to the concrete `Self` while the call site holds a wide `SmartPtr<dyn Trait>`. As documented in `builtin.rs:322-329`, downstream codegen and call-ABI lowering rely on *every* `DispatchFromDyn` struct being **ABI-identical to its inner raw/reference pointer**—treating it effectively as `#[repr(transparent)]` even without that attribute (because standard library smart pointers such as `Box<T, A>` parameterize over an allocator `A` that is 1-ZST only for specific instantiations like `Global`).

The exact side-by-side comparison extracted from `builtin.rs:287-463` vs. `builtin.rs:655-888` is:

| Property / Check | `CoerceUnsized` (`builtin.rs:655-888`) | `DispatchFromDyn` (`builtin.rs:287-463`) |
| :--- | :--- | :--- |
| **Builtin `&T`/`&mut T`/`*const T`/`*mut T` base rules** | Allows lifetime shrinking (`r_a: r_b`), mut-to-imm weakening (`&mut -> &`, `*mut -> *const`), and ref-to-raw-ptr (`&T -> *const U`, `&mut T -> *mut U`) (`builtin.rs:680-727`) | Strict equality only: `&'a T -> &'a U`, `&'a mut T -> &'a mut U`, `*const T -> *const U`, `*mut T -> *mut U` (`r_a == r_b && mutbl_a == mutbl_b`, `builtin.rs:343-348`) |
| **Struct `#[repr(C)]` / `#[repr(packed)]`** | Allowed (no repr restriction) | **Forbidden (`E0378`)**: `if def_a.repr().c() \|\| def_a.repr().packed()` emits `DispatchFromDynRepr` (`builtin.rs:364-366`) |
| **`PhantomData<...>` field handling** | **Explicitly whitelisted** via `is_phantom_data()` on normalized field def type before comparing `a == b` (`builtin.rs:790-801`) | **Explicitly whitelisted** via `is_phantom_data()` on normalized field def type before comparing `ty_a == ty_b` (`builtin.rs:374-385`) |
| **Unchanged field (`ty_a == ty_b`)** | **Unconditionally ignored** (`builtin.rs:812-814`), permitting arbitrary non-ZST payloads (`u64`, over-aligned ZSTs, generic types) | Allowed **iff** `layout.is_1zst() && !ty_a.has_non_region_param()` (`builtin.rs:391-403`); otherwise emits **`E0378` (`DispatchFromDynZST`)** (`builtin.rs:405-409`) |
| **Multiple changed non-`PhantomData` fields (`ty_a != ty_b`)** | **Forbidden (`E0375`, `CoerceMulti`)** (`builtin.rs:828-844`) | **Forbidden (`E0375`, `CoerceMulti`)** (`builtin.rs:452-459`) |
| **Zero changed fields** | **Forbidden (`E0374`, `CoerceNoField`)** (`builtin.rs:822-827`) | **Forbidden (`E0374`, `CoerceNoField`)** (`builtin.rs:419-424`) |
| **Recursive obligation on unique changed field** | `a: CoerceUnsized<b>` (`builtin.rs:848, 865`) | `ty_a: DispatchFromDyn<ty_b>` (`builtin.rs:431`) |

Two subtle compiler facts emerge directly from inspecting `builtin.rs:371-416` and verifying them empirically:
1. **Why custom generic ZST `MyZst<T>` triggers `E0375` while `OtherGenZst<X>` and `ConstZst<N>` trigger `E0378`**: Because only `core::marker::PhantomData` is whitelisted by `is_phantom_data()` (`builtin.rs:382`), a custom wrapper `struct MyZst<T: ?Sized>(PhantomData<T>);` inside `BadCustomGenZstPtr<T>(*const T, MyZst<T>)` is *not* skipped. When comparing source `BadCustomGenZstPtr<T>` and target `BadCustomGenZstPtr<U>`, field `1` has `ty_a = MyZst<T> != MyZst<U> = ty_b`, so it enters `coerced_fields` as a *second* coerced field and fails with **`E0375`** (`implementing DispatchFromDyn does not allow multiple fields to be coerced`) even when `CoerceUnsized` is omitted! By contrast, when a ZST mentions a *different* type or const generic that does not vary across `T -> U` (`OtherGenZst<X>` or `ConstZst<N>`), `ty_a == ty_b` holds, so it reaches the unchanged-field branch (`builtin.rs:391-411`) and fails `!ty_a.has_non_region_param()` with **`E0378`**—specifically to prevent library unsoundness from transmuting between distinct generic ZST tokens (`builtin.rs:394-395`).
2. **Why `#[derive(CoercePointee)]` is even stricter**: `visit_implementation_of_coerce_pointee_validity` (`builtin.rs:1013-1041`) checks that derived `CoercePointee` structs explicitly carry `#[repr(transparent)]` (`def.repr().transparent()`, line `1034`), closing the manual-impl gap where a `#[repr(Rust)]` struct relies on `DispatchFromDyn`'s 1-ZST field gate to imply transparent layout.

#### 4.2 Empirical `CoerceUnsized` / `DispatchFromDyn` Matrix (`rustc` + `Miri`)

All 11 cases executed by `support/probe_variance_dropck_rpit_dyn.py` on `rustc 1.98.0-nightly` + `miri 0.1.0` match `builtin.rs` and our Lean proofs (`dispatchFromDyn_preserves_pointer_abi`, `ce3_overaligned_zst_breaks_dispatch_from_dyn_abi`, `phantom_and_1zst_smart_ptrs_preserve_abi`, `extra_field_repr_c_and_custom_generic_zst_rejected`) 11/11:

| Probe Case | Struct Definition | Traits Implemented | `rustc` / `Miri` Result | Exact Diagnostic / Output |
| :--- | :--- | :--- | :--- | :--- |
| `custom_dispatch_from_dyn_ok` / `_miri` | `MyPtr<T: ?Sized>(*const T)` | `CoerceUnsized` + `DispatchFromDyn` | **Pass (`rc=0`)** native & `Miri` | `CUSTOM_DISPATCH=123` |
| `dispatch_from_dyn_1byte_nongeneric_zst_miri` | `GoodZstPtr<T: ?Sized>(*const T, UnitZst)` | `CoerceUnsized` + `DispatchFromDyn` | **Pass (`rc=0`)** `Miri` | `ZST_DISPATCH=456` |
| `dispatch_from_dyn_phantom_t_whitelisted_*` | `PhantomTPtr<T: ?Sized>(*const T, PhantomData<T>)` | `CoerceUnsized` + `DispatchFromDyn` | **Pass (`rc=0`)** native & `Miri` | `PHANTOM_DISPATCH=789` |
| `coerce_unsized_extra_non_zst_allowed` | `CoerceWithMeta<T: ?Sized>(*const T, u64)` | `CoerceUnsized` only | **Compiles (`rc=0`)** | Coerces `[u8; 4]` to `[u8]` carrying `u64` |
| `dispatch_from_dyn_extra_non_zst_rejected_e0378` | `BadPtr<T: ?Sized>(*const T, u64)` | `CoerceUnsized` + `DispatchFromDyn` | **Rejected `E0378` (`rc=1`)** | `extra field '1' of type 'u64' is not allowed` |
| `dispatch_from_dyn_align16_zst_rejected_e0378` | `BadAlignedPtr<T: ?Sized>(*const T, Align16Zst)` (`#[repr(align(16))]`) | `CoerceUnsized` + `DispatchFromDyn` | **Rejected `E0378` (`rc=1`)** | `extra field '1' of type 'Align16Zst' is not allowed` |
| `dispatch_from_dyn_custom_generic_zst_with_coerce_e0375` | `BadCustomGenZstPtr<T: ?Sized>(*const T, MyZst<T>)` | `CoerceUnsized` + `DispatchFromDyn` | **Rejected `E0375` (`rc=1`)** | `implementing 'CoerceUnsized' does not allow multiple fields to be coerced` |
| `dispatch_from_dyn_custom_generic_zst_alone_e0375` | `BadCustomGenZstPtr<T: ?Sized>(*const T, MyZst<T>)` | `DispatchFromDyn` only | **Rejected `E0375` (`rc=1`)** | `implementing 'DispatchFromDyn' does not allow multiple fields to be coerced` |
| `dispatch_from_dyn_unchanged_type_generic_zst_e0378` | `BadOtherGenZstPtr<T: ?Sized, X>(*const T, OtherGenZst<X>)` | `DispatchFromDyn` only | **Rejected `E0378` (`rc=1`)** | `extra field '1' of type 'OtherGenZst<X>' is not allowed` |
| `dispatch_from_dyn_const_generic_zst_rejected_e0378` | `BadConstZstPtr<T: ?Sized, const N: usize>(*const T, ConstZst<N>)` | `DispatchFromDyn` only | **Rejected `E0378` (`rc=1`)** | `extra field '1' of type 'ConstZst<N>' is not allowed` |
| `dispatch_from_dyn_repr_c_rejected` | `#[repr(C)] struct ReprCPtr<T: ?Sized>(*const T)` | `DispatchFromDyn` only | **Rejected `E0378` (`rc=1`)** | `structs implementing 'DispatchFromDyn' may not have '#[repr(packed)]' or '#[repr(C)]'` |

**Mechanized ABI-Equivalence Proof (`support/VarianceDropckAndDispatchFromDynSoundness.lean:813-1158`)**:
Theorem `dispatchFromDyn_preserves_pointer_abi` proves constructively (depending solely on `[propext]`) that whenever a struct `s` satisfies `dispatchFromDynAdmissible s = true` with valid `PhantomData` layout (`size_of == 0, align_of == 1`, per `library/core/src/marker.rs:805-807`) and a unique coerced pointer field `fPtr` (`sizeBytes ≠ 0`, `1 ≤ alignBytes`), `s` has exact total size `fPtr.sizeBytes`, exact alignment `fPtr.alignBytes`, `nonZstCount s.fields = 1`, and transparent pointer ABI `AbiKind.transparentPointer fPtr.sizeBytes fPtr.alignBytes`. Counterexample `ce3_overaligned_zst_breaks_dispatch_from_dyn_abi` explicitly constructs `BadAlignedPtr<T>(*const T, Align16Zst)` on 64-bit (`widePtr = (16, 8)`, `align16Zst = (0, 16)`), proving that `fieldsAlign = 16 ≠ 8`, `classifySmartPtrAbi = .nonTransparentAggregate 16 16`, and `dispatchFromDynAdmissible = false`.

---

### 5. Mapping onto `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` Trusted Boundary

Basis: source + derived

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` shows that Anneal's current trusted MIR model is intentionally fail-closed across all four compiler features analyzed above, establishing exact guardrails for future verification extensions:

| `rustc` Feature | Current Handling in `joshlf/anneal@c131b320e` | Exact Source Citation | Required Soundness Contract for Future Support |
| :--- | :--- | :--- | :--- |
| **Variance & `AscribeUserType`** | Regions are erased in `MirTy.ref (mutability) (pointee)` (`MirAst.lean:304-305, 319`); `StatementKind::AscribeUserType(..., ty::Variance)` lowers fail-closed to `StatementKind.unsupported` | `trusted/lean/Trusted/MirAst.lean:304-305, 641, 654-656` | Post-borrowck MIR carries erased regions; any future MIR type-checking or retag-preservation layer verifying subtyping coercions must preserve `Variance::xform` and `glb` monotonicity and never treat `&mut T` / `*mut T` / `UnsafeCell<T>` as covariant in `T`. |
| **`dropck`, `#[may_dangle]`, `Drop` terminators** | `TerminatorKind::Drop` lowers fail-closed to `TerminatorKind.unsupported`; `BackwardIncompatibleDropHint` lowers to `StatementKind.unsupported`; correspondence bridge returns `.error (.unsupported "Drop unsupported")`; `.move` conservatively deinitializes non-ZST locals (`deinitMovedPlace = true`) | `trusted/lean/Trusted/MirAst.lean:646, 753-754, 782-784`; `trusted/lean/Trusted/MirSemantics.lean:949-976`; `trusted/correspondence/Trusted/Correspondence.lean:2186` | Once `TerminatorKind::Drop` is admitted, verification of any `unsafe impl<#[may_dangle] T> Drop` container cannot rely on `rustc` `dropck` alone: proofs must independently verify Axis 1 (`PhantomData<T>` present if `T`'s drop glue runs) AND Axis 2 (`Drop` never reads `T` directly when `T` may be trivially droppable). |
| **Edition 2024 `RPIT` (`impl Trait`) & `OpaqueCast`** | `ProjectionElem::OpaqueCast(T)` lowers fail-closed to `ProjectionElem.unsupported`; unmodeled alias/opaque types fail closed to `MirTy.unsupported` | `trusted/lean/Trusted/MirAst.lean:308-311, 461, 469-471` | Capture runs after clean `rustc` analysis (`trusted/rustc-capture/src/driver.rs:75-84`), so opaque types have already been borrow-checked under the edition-specific `resolve_bound_vars` rule (`opaque.span.at_least_rust_2024()` vs. `use<...>`). Capturing monomorphized MIR must preserve hidden-type resolution and never collapse `OpaqueCast` without checking revealed concrete layout. |
| **`CoerceUnsized` / `DispatchFromDyn` & `dyn Trait`** | `TyKind::Dynamic`, `TyKind::FnPtr`, and non-fieldless-enum ADTs lower fail-closed to `MirTy.unsupported`; `Rvalue::Cast` (`PointerCoercion::Unsize`) lowers to `Rvalue.unsupported`; indirect `TerminatorKind::Call` lowers to `TerminatorKind.unsupported` | `trusted/lean/Trusted/MirAst.lean:285, 308-311, 572, 612-618, 782-784` | Extending MIR semantics to `dyn Trait` dispatch requires enforcing the `DispatchFromDyn` ABI-transparency invariant (`size = ptrSize`, `align = ptrAlign`, 1 non-ZST pointer field, no `#[repr(C)]`/`#[repr(packed)]`, no over-aligned ZSTs) rather than the weaker `CoerceUnsized` invariant. |
| **Proof-Checker TCB Discipline** | `TrustedBoundary.lean` rejects `sorryAx` (`constantHasSorry`) and forbids compiler-reflection primitives `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, `Lean.reduceBool`, `Lean.reduceNat` (`forbiddenVendorCompilerRefs`) | `trusted/audit/TrustedBoundary.lean:1606-1617` | Our formalization `support/VarianceDropckAndDispatchFromDynSoundness.lean` complies strictly with Anneal's TCB audit rules: 0 `sorryAx`, 0 `Classical.choice`, 0 `Quot.sound`, 0 `Lean.ofReduceBool`, 0 `partial def`. |

## Boundaries

The following explicit negative-space classifications define what this report does **not** establish:

- **Higher-ranked trait bounds (`for<'a>`), Polonius next-generation borrow checker (`-Zpolonius=next`), and coroutine witness dropck**: **not examined** empirically in the probe. Source inspection of `compiler/rustc_borrowck/src/type_check/liveness/trace.rs:409-420` and `compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs:315-378` shows that `-Zpolonius=next` records live-region variances across the whole local type (not only dropck kinds) and that coroutine dropck approximates erased witness regions by forcing all upvars use-live whenever any interior witness needs drop. Full empirical and formal verification of Polonius-next and coroutine-witness dropck is outside this report's scope.
- **`AsyncDrop` (`adt_async_drop_tys`) and `CovariantUnsafeCell`**: **not examined** empirically. Source audit at `rust-lang/rust@342d74463` confirmed `covariant_unsafe_cell_type -> [ty::Covariant]` in `variance/terms.rs:114` and `adt_async_drop_tys` in `rustc_ty_utils/src/needs_drop.rs:499-516` (with an explicit `FIXME(async_drop)` skipping boxed `dyn` pointees at lines `401-406`). Because `covariant_unsafe_cell_type` was added after `14210df0e` (`2026-05-31`), it could not be executed on the local `rustc 1.98.0-nightly (14210df0e)` toolchain.
- **`Reborrow` and `CoerceShared` built-in coherence checks**: **not examined** empirically. Source inspection of `compiler/rustc_hir_analysis/src/coherence/builtin.rs:46-47, 465-653` observed their dispatch alongside `CoerceUnsized` and `DispatchFromDyn`, but their runtime/coherence matrices were not probed or formalized.
- **Uninhabited types, non-1-ZST `ManuallyDrop<T>` interiors, and custom allocator `Box<T, A>` instantiations**: **not examined** empirically beyond the `Align16Zst`, `UnitZst`, `OtherGenZst<X>`, and `ConstZst<N>` witnesses. In particular, `DispatchFromDyn` on `Box<T, A>` in `library/alloc` uses a `where A: Allocator` impl gated by standard-library layout assumptions where `Global` is a 1-ZST; generic custom allocators that mention a type parameter `A` cannot implement `DispatchFromDyn` without failing `!ty_a.has_non_region_param()` unless `A` is fixed to a concrete 1-ZST (e.g., `Global`).
- **Lean formalization model scope (attractive stronger conclusion explicitly *not* established)**: **known not to apply** as a full-compiler soundness proof of `rustc`'s entire MIR/LLVM backend. `support/VarianceDropckAndDispatchFromDynSoundness.lean` is a standalone, self-contained formalization of the four core type-system invariants (4-element variance lattice and `TyExpr` lifetime subtyping, 2-slot reverse-declaration-order dropck schedules, `opaque_captures_all_in_scope_lifetimes` edition rules, and struct field-layout ABI transparency for `DispatchFromDyn`). It does **not** import `joshlf/anneal`'s `Trusted.MirSemantics` (which currently rejects `Drop`, `Dynamic`, `OpaqueCast`, and `PointerCoercion::Unsize` fail-closed) and does **not** mechanically link `rustc`'s Rust source code to the Lean definitions via translation validation.
- **Macro-hygiene mixed-edition `RPIT` spans**: **not examined** empirically. While `resolve_bound_vars.rs:328` clearly checks `opaque.span.at_least_rust_2024()`, cross-crate declarative/procedural macro invocation spanning Edition 2021 and Edition 2024 crates was not executed in the probe.
- **Target ABI variations beyond `x86_64-unknown-linux-gnu`**: **not examined** empirically. All `rustc` and `Miri` runs executed on `x86_64-unknown-linux-gnu`. While `DispatchFromDyn`'s `1-ZST` and `#[repr(C)]`/`#[repr(packed)]` checks in `builtin.rs` are target-independent at HIR/typeck time (except through `layout.is_1zst()`), target-specific calling-convention lowering (e.g., `ScalarPair` register passing on `aarch64` or `i686` or `windows-msvc`) is **unsupported** by this probe and would require target-specific ABI codegen verification.
- **Future `PhantomData<T>` dropck evolution**: **unknown**. `library/core/src/marker.rs:797` explicitly warns: *"The exact interaction of `PhantomData` with drop check may change in the future."* Claims in this report hold strictly for the audited revisions (`14210df0e` and `342d74463`).

## Evidence

All primary-source citations, empirical outputs, and mechanized proofs were acquired and verified on `2026-11-22`.

### A. Primary-Source Code Audits

1. **`rust-lang/rust` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`2026-11-22T00:04:39Z`)**:
   - `compiler/rustc_type_ir/src/lib.rs:260-336`: `pub enum Variance`, `Variance::xform` (PLDI'11 Fig. 1), and `fmt::Debug` tokens (`+`, `-`, `o`, `*`).
   - `compiler/rustc_hir_analysis/src/variance/mod.rs:30-227`: `crate_variances`, `variances_of`, and `variance_of_opaque`.
   - `compiler/rustc_hir_analysis/src/variance/terms.rs:66-123`: `determine_parameters_to_be_inferred` and hardcoded `lang_items` (`phantom_data`, `unsafe_cell_type`, `covariant_unsafe_cell_type`).
   - `compiler/rustc_hir_analysis/src/variance/constraints.rs:49-491`: constraint generation across leaf no-ops (`215-224`), `Ref` (`230-233`), `RawPtr` (`249-251`), `Adt` (`259-261`, `352-401`), `Alias` (`263-277`), `Dynamic` (`279-301`), `Param` (`303-305`), `FnPtr`/`FnDef` (`307-309`, `423-434`), `ReEarlyParam` (`445-447`), and `TypeAndMut` (`474-490`).
   - `compiler/rustc_hir_analysis/src/variance/solve.rs:17-164`: `fn glb`, `solve_constraints`, `SolveContext::solve` (`2C` bound), `enforce_const_invariance`, `create_map` (`FnDef` bivariant -> invariant promotion).
   - `compiler/rustc_hir_analysis/src/variance/dump.rs:8-53`: `#[rustc_dump_variances]` and `#![rustc_dump_variances_of_opaques]`.
   - `compiler/rustc_hir_analysis/src/check/wfcheck.rs:2081-2172` and `check/check.rs:644-679, 827, 924`: `check_variances_for_type_defn` (`E0392` on unconstrained `ty::Bivariant` ADT params) and `use<...>` precise-capture validation against `tcx.variances_of`.
   - `compiler/rustc_borrowck/src/type_check/liveness/mod.rs:35-293` and `liveness/trace.rs:146-188, 400-563, 785-830`: separation of `use_live_at` vs. `drop_live_at` and `dropck_local` invocation of `DropckOutlives`.
   - `compiler/rustc_middle/src/ty/util.rs:466-538`: `TyCtxt::destructor_constraints` checking `!pure_wrt_drop` (`#[may_dangle]`).
   - `compiler/rustc_traits/src/dropck_outlives.rs:20-73`: `adt_dtorck_constraint` special-casing `PhantomData<T>` into `dtorck_types: [T]` (`40-52`) while pushing `destructor_constraints` into `outlives` (`59`).
   - `compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs:28-427`: `trivial_dropck_outlives` (`28-95`), `compute_dropck_outlives_with_errors` (`108-253`), and `dtorck_constraint_for_ty_inner` (`258-427`).
   - `compiler/rustc_ty_utils/src/needs_drop.rs:365-565`: `drop_tys_helper`, `adt_drop_tys`, `adt_async_drop_tys`.
   - `compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs:322-331, 527-699`: `opaque_captures_all_in_scope_lifetimes`, `visit_opaque_ty`, and `visit_precise_capturing_arg`.
   - `compiler/rustc_hir_analysis/src/coherence/builtin.rs:32-54, 287-463, 655-888, 1013-1041`: `visit_implementation_of_dispatch_from_dyn`, `coerce_unsized_info`, and `visit_implementation_of_coerce_pointee_validity`.
   - `library/core/src/ops/unsize.rs:34-137` and `library/core/src/marker.rs:225-238, 795-813`: `CoerceUnsized`, `DispatchFromDyn`, `Unsize`, and `PhantomData` layout guarantees (`size_of == 0`, `align_of == 1`).

2. **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19T21:39:21Z`)**:
   - `trusted/lean/Trusted/MirAst.lean:272-321, 448-475, 562-662, 742-795`: fail-closed `.unsupported` boundaries on `Dynamic`, `FnPtr`, non-fieldless-enum ADTs, `OpaqueCast`, `Cast` (`PointerCoercion::Unsize`), `AscribeUserType(..., ty::Variance)`, `BackwardIncompatibleDropHint`, `Drop`, and indirect `Call`.
   - `trusted/lean/Trusted/MirSemantics.lean:949-976`: `evalOperandToSlot` with conservative move deinitialization (`deinitMovedPlace = true`).
   - `trusted/correspondence/Trusted/Correspondence.lean:2186`: `drop` hook returning `.error (.unsupported "Drop unsupported")`.
   - `trusted/audit/TrustedBoundary.lean:1606-1617`: `constantHasSorry` and `forbiddenVendorCompilerRefs`.
   - `trusted/rustc-capture/src/driver.rs:25, 45-47, 75-84`: compiler version pin and `after_analysis` clean-analysis check.

### B. Preserved Empirical Probe and Golden Results

- **Runnable probe**: `support/probe_variance_dropck_rpit_dyn.py` (Python 3.10+, standard library only; scrubs all host, user-home, sysroot, and temporary directory paths).
- **Captured golden output**: `support/probe_variance_dropck_rpit_dyn_results.json` (`23,705` bytes), captured `2026-11-22T07:42:02Z` using:
  - `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`)
  - `miri 0.1.0 (14210df0e2 2026-05-31)`
- **Summary of live counts**:
  - Part A: 12/12 type-constructor two-sided variance probes + 5/5 lifetime-variance probes + 2/2 `E0392` rejections + 1/1 `#[rustc_dump_variances]` internal compiler dump (`['a: +, 'b: +, A: +, B: o, C: -, D: +, E: +, F: o]`).
  - Part B: 7/7 `dropck`/`#[may_dangle]`/`PhantomData` cases — 3 live `Miri` UAF detections (`rc = 1` after `rustc` `rc = 0`: Axis 1 no-phantom, Axis 1 `PhantomData<fn() -> T>`, Axis 2 `Copy` `&'a String` direct read with `PhantomData<T>`), 2 `rustc` `E0597` rejections (Axis 1 with `PhantomData<T>`, Axis 2 without `#[may_dangle]`), and 2 `Miri` positive controls (`rc = 0`: `SAFE_DROP_LEN=14`, `SOUND_MAY_DANGLE_COPY_OK`).
  - Part C: 10/10 Edition 2021 vs. Edition 2024 `RPIT` / `use<...>` / inherent-method / `RPITIT` cases (4 passing executions + 6 `E0506` rejections).
  - Part D: 11/11 `CoerceUnsized` / `DispatchFromDyn` cases (3 passing `Miri` dynamic-dispatch executions + 1 `CoerceUnsized` extra-field compile pass + 2 `E0375` rejections + 5 `E0378` rejections covering `u64`, `Align16Zst`, `OtherGenZst<X>`, `ConstZst<N>`, and `#[repr(C)]`).

### C. Preserved Kernel-Checked Lean `v4.34.1` Formalization

- **File**: `support/VarianceDropckAndDispatchFromDynSoundness.lean` (`1,158` lines, `50,628` bytes).
- **Verifier**: Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`, Release), invoked with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`, zero warnings, zero errors).
- **Hygiene & Axiom Audit (`#print axioms` on all 21 headline theorems)**:
  - **0** occurrences of `sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `partial def`, or `._unsafe_rec` anywhere in the file.
  - **Zero-axiom theorems (`[]`)**: `Variance.xform_assoc`, `Variance.xform_contra_contra_eq_cov`, `Variance.xform_contra_involutive`, `rpit_use_bound_overrides_edition_default`, `rpit_edition_2021_vs_2024_delta`.
  - **`[propext]`-only theorems (0 `Classical.choice`, 0 `Quot.sound`, 0 `sorryAx`, 0 `Lean.ofReduceBool`)**: `Variance.glb_comm`, `Variance.glb_assoc`, `Variance.xform_distrib_glb_right`, `Variance.xform_not_distrib_glb_left`, `inferVariance_of_not_mentionsParam`, `inferVariance_ambient_factor`, `inferVariance_sound`, `twelve_constructor_variances`, `dropck_may_dangle_uaf_free_iff_ownership_and_no_direct_read`, `dropck_without_may_dangle_always_uaf_free`, `ce1_phantom_fn_misses_dropck_ownership_uaf`, `ce2_direct_read_of_copy_ref_under_may_dangle_bypasses_phantom_t`, `dispatchFromDyn_preserves_pointer_abi`, `ce3_overaligned_zst_breaks_dispatch_from_dyn_abi`, `phantom_and_1zst_smart_ptrs_preserve_abi`, `extra_field_repr_c_and_custom_generic_zst_rejected`.

## Revalidation

Each claim class has a narrow, cheap, standalone revalidation procedure requiring only the files preserved inside this package:

1. **Re-run the empirical `rustc` + `Miri` matrix on a newer nightly toolchain** (checks all 4 parts — variance lattice, `#[rustc_dump_variances]`, `E0392`, both `#[may_dangle]` Miri UAF axes + `E0597`, Edition 2021 vs. 2024 `RPIT` + `use<...>`, and `CoerceUnsized`/`DispatchFromDyn` `Miri` + `E0378`/`E0375`):
   ```bash
   python3 support/probe_variance_dropck_rpit_dyn.py --out /tmp/reval_probe.json
   diff -u support/probe_variance_dropck_rpit_dyn_results.json /tmp/reval_probe.json
   ```
   A pass requires identical `inferred_variance` entries across all 12+5 variance cases, `compile_rc = 1` (`E0392`) on unused ADT params, `rc = 1` Miri UAF on `axis1_no_phantom_uaf_miri`, `axis1_phantom_fn_uaf_miri`, and `axis2_direct_read_copy_t_even_with_phantom_t_miri`, `E0597` on `axis1_phantom_t_blocks_e0597` and `axis2_without_may_dangle_blocks_copy_t_e0597`, `rc = 0` on both `Miri` positive controls, `E0506` vs. `rc = 0` on all 10 Edition 2021/2024 `RPIT` cases, and exact `Miri` / `E0378` / `E0375` outcomes across all 11 `DispatchFromDyn` / `CoerceUnsized` cases.

2. **Re-verify the kernel-checked Lean `v4.34.1` formalization and axiom footprint**:
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/VarianceDropckAndDispatchFromDynSoundness.lean
   ```
   To re-audit axioms without mutating the package file, copy it to `/tmp/audit_axioms.lean`, append `#print axioms` commands for every public theorem in `RustcVarianceDropckDispatch`, run `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false /tmp/audit_axioms.lean`, and verify zero occurrences of `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or `Lean.trustCompiler`.

3. **Targeted upstream source diff checks when upgrading `rust-lang/rust` or `joshlf/anneal`**:
   - **Variance**: Diff `compiler/rustc_type_ir/src/lib.rs` (`Variance::xform`), `compiler/rustc_hir_analysis/src/variance/{terms,constraints,solve}.rs`, and `compiler/rustc_hir_analysis/src/check/wfcheck.rs` (`check_variances_for_type_defn`) for changes to hardcoded lang-item variances or `E0392` exemptions.
   - **`dropck` & `#[may_dangle]`**: Diff `compiler/rustc_traits/src/dropck_outlives.rs` (`adt_dtorck_constraint`), `compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs` (`trivial_dropck_outlives`), and `compiler/rustc_middle/src/ty/util.rs` (`destructor_constraints`) — especially if `PhantomData<T>` semantics change as warned in `library/core/src/marker.rs:797`.
   - **`RPIT` capture**: Diff `compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs` (`opaque_captures_all_in_scope_lifetimes`).
   - **`CoerceUnsized` / `DispatchFromDyn`**: Diff `compiler/rustc_hir_analysis/src/coherence/builtin.rs` (`visit_implementation_of_dispatch_from_dyn`, `coerce_unsized_info`) for any relaxation of `is_1zst()`, `!has_non_region_param()`, `is_phantom_data()`, or `#[repr(C)]`/`#[repr(packed)]`.
   - **Anneal trusted boundary**: Diff `trusted/lean/Trusted/MirAst.lean` (`MirTy`, `ProjectionElem`, `Rvalue`, `StatementKind`, `TerminatorKind`) and `trusted/correspondence/Trusted/Correspondence.lean` whenever `Drop`, `Dynamic`, `OpaqueCast`, `AscribeUserType`, or `PointerCoercion::Unsize` moves out of `.unsupported`.
