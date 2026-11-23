# Rustc Variance Inference Lattice, Higher-Ranked Subtyping, and Zerocopy Pointer Variance

## Summary

Rust combines definition-site variance inference for nominal items (`struct`, `enum`, `union`, `fn`) with structural subtyping over regions (`'big: 'small`), higher-ranked function binders (`for<'a>`), and raw or interior-mutable primitives. Directly inspecting `rust-lang/rust`, `google/zerocopy`, and `joshlf/anneal` alongside live `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) experiments and a standalone constructive Lean `v4.34.1` mechanization ([VarianceLatticeHrtbSubtypingSoundness.lean](support/VarianceLatticeHrtbSubtypingSoundness.lean)) establishes five core results:

1. **Four-point semi-lattice and left-biased `Variance::xform` algebra (`compiler/rustc_type_ir/src/lib.rs`, `compiler/rustc_hir_analysis/src/variance/solve.rs`).** `rustc` models variance over the four-point bounded distributive lattice `Invariant < {Covariant, Contravariant} < Bivariant` (`o < {+, -} < *`). Its composition operator `Variance::xform` adopts Figure 1 of Altidor, Huang, and Smaragdakis (PLDI 2011) with one critical ordering twist: in `Variance::xform`, `(Variance::Invariant, _) => Variance::Invariant` precedes `(Variance::Bivariant, _) => Variance::Bivariant`. Consequently, `rustc`'s `Variance::xform` is associative, left-unit (`Covariant`), monotone in both arguments, and strictly conservative relative to symmetric PLDI'11 composition (`rustc_xform(a, b) <= pldi11_xform(a, b)`), **but it is not commutative** (`Invariant.xform(Bivariant) = Invariant != Bivariant = Bivariant.xform(Invariant)`) and **breaks right-distributivity over `glb` at `c = Bivariant`** (`(Covariant.glb Contravariant).xform(Bivariant) = Invariant` while `(Covariant.xform Bivariant).glb(Contravariant.xform Bivariant) = Bivariant`). Commutativity holds on all 14 other pairs not mixing `Invariant` and `Bivariant`.
2. **Bounded `2C` / `2N` fixed-point constraint solver and `CovariantUnsafeCell` override filtering (`terms.rs`, `constraints.rs`, `solve.rs`).** Starting every inferred parameter at top (`Bivariant`) and descending via greatest lower bound `glb(eval(term), old)` converges in at most `2C` iterations (and potential sum `<= 2N` over `N` inferred parameters) to the greatest, most-permissive sound assignment (Tarski/Kleene least-restrictive fixed point). Across compiler revisions, introducing `CovariantUnsafeCell<T>(UnsafeCell<T>)` (`rust-lang/rust` commit `77977f9966b681ff865f810869859bcb2eb13a8e`, present on trunk `960ba7cf7e8666ecb449402ca82b6e9e631bd227` and absent on `1.98.0-nightly` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) required `solve_constraints` to collect `overridden_inferreds` and execute `constraints.retain(...)`; without filtering, field inspection of the inner `UnsafeCell<T>` emits `[CovariantUnsafeCell::T <= UnsafeCell::T = Invariant]` and overwrites the hardcoded `Covariant` seed back to `Invariant`. Post-pass hooks force all `const` generic parameters to `Invariant` and clamp unused `ty::FnDef` `Bivariant` parameters to `Invariant`, whereas unused ADT parameters retain `Bivariant` (`*`) and fail compilation with `E0392` even when named in `where` bounds. Mutually recursive even contravariant cycles converge to alternating non-invariant polarities (`[-]` / `[+]`), while odd contravariant cycles with covariant occurrences collapse to `Invariant` (`[o]`).
3. **Higher-ranked subtyping via `enter_forall`, universe placeholders, `leak_check`, and double-contravariant reversal (`type_relating.rs`, `higher_ranked.rs`, `leak_check.rs`).** When relating `for<..>` binders covariantly (`sub <: sup`), `TypeRelating::binders` opens `sup` inside `InferCtxt::enter_forall`, replacing bound regions with placeholders in a fresh `UniverseIndex` that outer inference variables cannot name, and instantiates `sub` with fresh inference variables. Coercing `for<'a> fn(&'a u8) -> u8 <: fn(&'static u8) -> u8` instantiates `'a := 'static` and succeeds (`HRTB_TO_STATIC=77`). Conversely, coercing `fn(&'static u8) -> u8 <: for<'a> fn(&'a u8) -> u8` creates placeholder `P0` in universe `U1`, flips argument variance contravariantly, records `P0: 'static` (`U0`), and fails `leak_check`'s SCC universe dominance check (`RegionsInsufficientlyPolymorphic` -> `E0308`). Disabling `-Zno-leak-check` skips `leak_check` in `higher_ranked.rs` (`return Ok(())`), yet region checking/NLL still rejects the coercion with `E0308` (printing `found fn pointer fn(&_) -> _`). Placing a higher-ranked function in argument position of a higher-order function flips polarity twice (`- x - = +`), accepting `fn(fn(&'static u8) -> u8) -> u8 <: fn(for<'a> fn(&'a u8) -> u8) -> u8` (`DOUBLE_FLIP=55`) and rejecting the converse.
4. **Zerocopy `PtrInner<'a, T>` and `Ptr<'a, T, I>` variance design (`zerocopy/src/pointer/{inner.rs, ptr.rs}`, `fe70ab691`).** `PtrInner<'a, T>` pairs `ptr: NonNull<T>` with `_marker: PhantomData<&'a core::cell::UnsafeCell<T>>` (chosen over `&'a mut T` because `zerocopy` MSRV 1.65 forbids `&mut` in `const fn PtrInner::new`), and `Ptr<'a, T, I>` wraps `PtrInner<'a, T>` plus `_invariants: PhantomData<I>`. This yields exact variance `['a: +, T: o]` on `PtrInner` and `['a: +, T: o, I: +]` on `Ptr`, matching `&'a mut T` in `'a` and `T` while keeping aliasing/alignment/validity marker `I` covariant. Because Rust computes one variance vector per ADT rather than per generic specialization, `Shared` and `Exclusive` `Ptr` both forbid shortening lifetimes inside `T`, preventing aliasing-lifetime forgery through mutable/exclusive mutation and enforcing the invariant property checked in `zerocopy/tests/ui/ptr-is-invariant-over-v.rs`.
5. **Constructive Lean `v4.34.1` mechanization and live `rustc` empirical suite.** The self-contained module `support/VarianceLatticeHrtbSubtypingSoundness.lean` (1,686 LOC, 682 declarations, 249 theorems) mechanizes all four layers without `sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `partial def`, or `_unsafe_rec` constants (axioms: `[propext, Quot.sound]`), while `support/probe_variance_subtyping_hrtb.py` reproduces every `#[rustc_dump_variances]` output, positive coercion, `E0308` / lifetime rejection, `-Zno-leak-check` diagnostic difference, and real `zerocopy 0.8.64` `Ptr` check.

| Component | Key Mechanism / Definition | Core Property Verified | Primary Target |
| :--- | :--- | :--- | :--- |
| Variance lattice & `xform` | `Invariant < {+, -} < Bivariant`; `(Invariant, _)` before `(Bivariant, _)` | Associative, monotone, left-unital (`+`), **non-commutative** on `(Invariant, Bivariant)` | `compiler/rustc_type_ir/src/lib.rs:260-325` |
| Fixed-point inference | Top start `Bivariant`; `glb(eval(term), old)`; `overridden_inferreds` filter | Terminates in `<= 2N` potential drops; maximal (most permissive) solution | `compiler/rustc_hir_analysis/src/variance/solve.rs:17-153` |
| HRTB binder subtyping | `TypeRelating::binders`, `enter_forall`, `leak_check` SCC min-universe pass | `for<'a> fn(&'a T) <: fn(&'static T)` holds; converse rejected by `leak_check` (and NLL under `-Zno-leak-check`) | `compiler/rustc_infer/src/infer/relate/{type_relating.rs, higher_ranked.rs}`, `leak_check.rs` |
| `zerocopy` `PtrInner` / `Ptr` | `NonNull<T>` + `PhantomData<&'a UnsafeCell<T>>` + `PhantomData<I>` | Variance `['a: +, T: o, I: +]`; blocks `&'big` -> `&'small` referent forgery across `Exclusive` and `Shared` | `zerocopy/src/pointer/{inner.rs, ptr.rs}`, commit `fe70ab6911f954f3` |
| Anneal MIR boundary | `StatementKind::AscribeUserType(..., ty::Variance)` -> `.unsupported` | Variance inference completes pre-MIR; downstream MIR verification erases variance except ascription failure closure | `joshlf/anneal@c131b320` `trusted/lean/Trusted/MirAst.lean:641,654-656` |

## Applicability

This report characterizes the combination and cross-revision evolution of four concrete upstream codebases alongside a constructive Lean 4 formalization:

- **`rust-lang/rust` trunk `main` (`960ba7cf7e8666ecb449402ca82b6e9e631bd227`) vs `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, 2026-05-31) vs `77977f9966b681ff865f810869859bcb2eb13a8e` (2026-07-22).**
  The four-point `Variance` definition, `Variance::xform` match ordering, `glb` definition, `2C` Kleene solver loop, `enforce_const_invariance`, `ty::FnDef` unused-parameter clamping to `Invariant`, `TypeRelating::binders`, `InferCtxt::enter_forall`, and SCC `leak_check` apply identically across both examined revisions (`14210df0e27c` and `960ba7cf7e86`). Three documented compiler changes distinguish `960ba7cf7e86` from `14210df0e27c`:
  1. `CovariantUnsafeCell<T>(UnsafeCell<T>)` (`library/core/src/cell/covariant_unsafe_cell.rs`, lang item `covariant_unsafe_cell`) and the corresponding `overridden_inferreds` + `constraints.retain(...)` filtering in `solve.rs:49-65` were introduced in commit `77977f9966b681ff865f810869859bcb2eb13a8e` on 2026-07-22. Live execution on `rustc 1.98.0-nightly` (`14210df0e27c`) empirically fails to resolve `#![feature(covariant_unsafe_cell)]` and `core::cell::CovariantUnsafeCell` (`E0635`, `E0432`), confirming pre-feature state.
  2. Lazy type alias variance inference (`DefKind::TyAlias if tcx.type_alias_is_lazy(def_id)`) existed in `terms.rs:102-104`, `mod.rs`, `constraints.rs`, and `dump.rs` at `14210df0e27c`, and is absent in `960ba7cf7e86` (`terms.rs:90-103`).
  3. Nightly `library/core/src/marker/variance.rs` (`#![unstable(feature = "phantom_variance_markers", issue = "135806")]`) and `#[rustc_assert_variance(...)]` annotations are present in `960ba7cf7e86`, wrapping `PhantomData` primitives (`PhantomCovariant`, `PhantomContravariant`, `PhantomInvariant`, and lifetime forms).

| Aspect / Feature | `rust-lang/rust` `14210df0e27c` (`1.98.0-nightly`) | `rust-lang/rust` `960ba7cf7e86` (trunk `main`) | Source / Execution Basis |
| :--- | :--- | :--- | :--- |
| `Variance::xform` `(Invariant, _)` before `(Bivariant, _)` | Present | Present | Source (`lib.rs`) |
| `glb` + `2C` descending loop + `enforce_const_invariance` + `FnDef` clamp | Present | Present | Source (`solve.rs`) + Execution (`rustc 1.98.0-nightly`) |
| `DefKind::TyAlias` lazy alias variance | Present (`terms.rs:102-104`) | Removed (`terms.rs:90-103`) | Source (`terms.rs`) |
| `CovariantUnsafeCell` + `overridden_inferreds` constraint filter | Absent (`E0432` / `E0635` live error) | Present (`terms.rs:114`, `solve.rs:49-65`) | Source (`solve.rs`, `77977f9966b6`) + Execution |
| `TypeRelating::binders`, `enter_forall`, SCC `leak_check`, `-Zno-leak-check` | Present | Present | Source + Execution (`rustc 1.98.0-nightly`) |

- **`google/zerocopy` trunk `main` (`2b88472905b75a71b3940ef2a23a814abff46695`), crate snapshot `0.8.64` (`907b9175fee081872ec883ca4709e6ad922f8ed0`), and historical commit `fe70ab6911f954f390b9ff04871e3c58fbba24e0`.**
  Comparison between `907b9175fee0` (directly compiled into `libzerocopy.rlib` by the empirical probe harness) and `2b88472905b7` shows zero differences under `zerocopy/src/` or `zerocopy/tests/` (the 10 non-`anneal/` changed paths are CI scripts, Dockerfiles, `.vscode`, `.gemini`, and `AGENTS.md`). Therefore, compiled probe observations on `907b9175fee0` transfer directly to `2b88472905b7`. In contrast, historical commit `fe70ab6911f954f3` predates workspace flattening, locating files at `src/pointer/{inner.rs, ptr.rs}` and `tests/ui-nightly/ptr-is-invariant-over-v.rs` rather than `zerocopy/src/...`; its core mechanism (`PhantomData<&'a core::cell::UnsafeCell<T>>`) remains unchanged on `2b88472905b7`.
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`).**
  Applies only at the post-typeck MIR AST boundary (`trusted/lean/Trusted/MirAst.lean:641,654-656`), explaining why type-level subtyping and variance live upstream of Anneal's fail-closed `AscribeUserType` handling rather than being re-inferred inside Anneal's Lean MIR semantics.
- **PLDI'11 "Taming the Wildcards" (`10.1145/1993498.1993569`) and sibling corpus formalizations.**
  PLDI'11 is the cited theoretical ancestor in `rustc_type_ir/src/lib.rs:302-303` and `solve.rs:17`, and differs from `rustc` in `xform(Invariant, Bivariant)`. For introductory subtyping soundness over simple references (`&T`, `&mut T`), see the companion corpus report `../lifetime-variance-subtyping-soundness-and-mutable-reference-invariance/REPORT.md`; this report extends beyond toy reference subtyping to `rustc`'s full 4-point lattice, PLDI'11 algebraic divergence, finite constraint solving, `CovariantUnsafeCell` overrides, `for<'a>` `enter_forall`/`leak_check`, and `zerocopy` `PtrInner`/`Ptr` aliasing soundness.
- **Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) mechanization scope.**
  All Lean theorems apply directly to the faithfully modeled finite subset: the exact 4-element `Variance` lattice, `Variance::xform` and `xformPldi11`, finite-index `VarianceTerm` / `VarianceConstraint` fixed-point solving, stratified universe De Bruijn `Region` / `Ty` subtyping with `forallFn` (`TypeRelating::binders` + `enter_forall` / `leak_check`), one-hole type contexts `TyCtx`, and an operational single-step heap-and-clock semantics for `Ptr` mutation. Full `rustc` MIR/borrowck NLL polonius constraints, trait solver coherence, and multi-thread operational models (Stacked/Tree Borrows) lie outside the mechanized Lean model as recorded under **Boundaries**.

## Findings

### 1. Four-Point Variance Semi-Lattice and `Variance::xform` Algebra

`Basis: documentation + source + execution + derived`

#### 1.1 Lattice Order and `glb` / `lub` Operations

Both `rustc_type_ir` and `rustc_hir_analysis::variance::solve` define variance as the four-element bounded distributive lattice with bottom `Invariant` (`o`), incomparable middle elements `Covariant` (`+`) and `Contravariant` (`-`), and top `Bivariant` (`*`). In `compiler/rustc_type_ir/src/lib.rs:260-336` (`960ba7cf7e8666ecb449402ca82b6e9e631bd227`):

```rust
pub enum Variance {
    Covariant,     // T<A> <: T<B> iff A <: B -- e.g., function return type
    Invariant,     // T<A> <: T<B> iff B == A -- e.g., type of mutable cell
    Contravariant, // T<A> <: T<B> iff B <: A -- e.g., function param type
    Bivariant,     // T<A> <: T<B>            -- e.g., unused type parameter
}
```

Diagnostics and `#[rustc_dump_variances]` map variants to `+`, `-`, `o`, and `*` (`lib.rs:329-334`). The greatest lower bound `glb` in `compiler/rustc_hir_analysis/src/variance/solve.rs:17-34` (`960ba7cf7e86`, and `16-34` in `14210df0e27c`) realizes the diamond partial order:

```rust
fn glb(v1: ty::Variance, v2: ty::Variance) -> ty::Variance {
    // Greatest lower bound of the variance lattice as defined in The Paper:
    //
    //       *
    //    -     +
    //       o
    match (v1, v2) {
        (ty::Invariant, _) | (_, ty::Invariant) => ty::Invariant,
        (ty::Covariant, ty::Contravariant) => ty::Invariant,
        (ty::Contravariant, ty::Covariant) => ty::Invariant,
        (ty::Covariant, ty::Covariant) => ty::Covariant,
        (ty::Contravariant, ty::Contravariant) => ty::Contravariant,
        (x, ty::Bivariant) | (ty::Bivariant, x) => x,
    }
}
```

Semantics-wise, each variance `v` is uniquely determined by the subset `{fwd, bwd}` of subtyping obligations it imposes (`needsFwd : Variance -> Bool` and `needsBwd : Variance -> Bool` in Lean):
- `Bivariant` (`*`): `(needsFwd = false, needsBwd = false)` — neither `A <: B` nor `B <: A` is required (chain height `potential = 2`).
- `Covariant` (`+`): `(needsFwd = true, needsBwd = false)` — requires `A <: B` (`potential = 1`).
- `Contravariant` (`-`): `(needsFwd = false, needsBwd = true)` — requires `B <: A` (`potential = 1`).
- `Invariant` (`o`): `(needsFwd = true, needsBwd = true)` — requires both `A <: B` and `B <: A` (`potential = 0`).

In Lean (`support/VarianceLatticeHrtbSubtypingSoundness.lean:117-264`), `Variance.ofDirs v.needsFwd v.needsBwd = v` establishes the polarity isomorphism, `Variance.le v w` (`v` is at least as restrictive as `w`, i.e., imposes at least the same polarity bits) is proven reflexive, antisymmetric, and transitive, `glb` / `lub` satisfy all bounded distributive lattice laws (`glb_comm`, `glb_assoc`, `glb_idem`, `glb_lub_absorb`, `lub_glb_absorb`, `distrib_glb_lub`, `distrib_lub_glb`), and `Variance.le_iff_glb_eq` proves `a.le b <-> a.glb b = a`.

#### 1.2 Exact `rustc` `Variance::xform` vs PLDI'11 Composition

Contextual composition `outer.xform(inner)` computes the net variance of a type parameter appearing at variance `inner` inside an ambient context of variance `outer`. In `compiler/rustc_type_ir/src/lib.rs:304-324` (`960ba7cf7e86`, unchanged in `14210df0e27c`), `Variance::xform` is defined as:

```rust
pub fn xform(self, v: Variance) -> Variance {
    match (self, v) {
        // Figure 1, column 1.
        (Variance::Covariant, Variance::Covariant) => Variance::Covariant,
        (Variance::Covariant, Variance::Contravariant) => Variance::Contravariant,
        (Variance::Covariant, Variance::Invariant) => Variance::Invariant,
        (Variance::Covariant, Variance::Bivariant) => Variance::Bivariant,

        // Figure 1, column 2.
        (Variance::Contravariant, Variance::Covariant) => Variance::Contravariant,
        (Variance::Contravariant, Variance::Contravariant) => Variance::Covariant,
        (Variance::Contravariant, Variance::Invariant) => Variance::Invariant,
        (Variance::Contravariant, Variance::Bivariant) => Variance::Bivariant,

        // Figure 1, column 3.
        (Variance::Invariant, _) => Variance::Invariant,

        // Figure 1, column 4.
        (Variance::Bivariant, _) => Variance::Bivariant,
    }
}
```

Inspecting lines 319 and 322 exposes an exact algebraic divergence from Figure 1 of Altidor, Huang, and Smaragdakis (PLDI 2011), which treats `bivariant` as globally absorbing (`Bivariant` on either side returns `Bivariant`, modeled by `Variance.xformPldi11` in Lean lines 176-184):

| `outer \ inner` | `Covariant (+)` | `Contravariant (-)` | `Invariant (o)` | `Bivariant (*)` |
| :--- | :---: | :---: | :---: | :---: |
| **`Covariant (+)`** | `+` | `-` | `o` | `*` |
| **`Contravariant (-)`** | `-` | `+` | `o` | `*` |
| **`Invariant (o)`** | `o` | `o` | `o` | **`o` in `rustc`** (`*` in PLDI'11) |
| **`Bivariant (*)`** | `*` | `*` | **`*` in `rustc`** (`*` in PLDI'11) | `*` |

Because `(Variance::Invariant, _) => Variance::Invariant` precedes `(Variance::Bivariant, _) => Variance::Bivariant` in `match (self, v)`:

1. **Non-commutativity (`Variance.xform_rustc_not_comm`):**
   `Invariant.xform(Bivariant) = Invariant`, whereas `Bivariant.xform(Invariant) = Bivariant`. Conversely, `Variance.xform_comm_unless_inv_bi` proves that `a.xform b = b.xform a` holds for every other pair `(a, b)` in the 16-entry multiplication table.
2. **Failure of right-distributivity over `glb` at `Bivariant`:**
   - `Variance.xform_glb_dist_left` holds unconditionally: `a.xform (b.glb c) = (a.xform b).glb (a.xform c)`.
   - Right-distributivity `(a.glb b).xform c = (a.xform c).glb (b.xform c)` holds whenever `c != Bivariant` (`Variance.xform_glb_dist_right_of_ne_bivariant`), weakens to `<=` everywhere (`Variance.xform_glb_dist_right_le`), and **fails strictly at `c = Bivariant`** (`Variance.xform_glb_dist_right_fails_at_bivariant`):
     - LHS: `(Covariant.glb Contravariant).xform(Bivariant) = Invariant.xform(Bivariant) = Invariant`.
     - RHS: `(Covariant.xform(Bivariant)).glb(Contravariant.xform(Bivariant)) = Bivariant.glb Bivariant = Bivariant`.
3. **Preserved monoid, monotonicity, and sound conservativity laws:**
   Case exhaustion across all $4^3 = 64$ triples proves `Variance.xform` remains strictly **associative** (`Variance.xform_assoc`), has two-sided **identity `Covariant`** (`xform_id_left`, `xform_id_right`), is left-absorbing for both `Invariant` and `Bivariant` (`xform_inv_left`, `xform_biv_left`), makes `Contravariant` involutive and polarity-swapping (`contravariant_xform_involutive`, `xform_contravariant_flips_dirs`), is **monotone in both arguments** (`xform_mono`), and stays conservatively below PLDI'11 (`xform_rustc_le_pldi11`: `(a.xform b).le (a.xformPldi11 b)`).

*Derivation of why `rustc` remains sound despite this discrepancy:* Whenever a subtyping check asks whether `G<A> <: G<B>` in an `Invariant` context (for example `&mut G<T>`) and `G<T>` ignores `T` (`Bivariant`), relating `G<A>` to `G<B>` both forward and backward still ignores `T` in `RelateTypeArgs` (because `G`'s own parameter variance `*` short-circuits argument comparison, just as `type_relating.rs:344` expects bivariance to be handled in `relate_with_variance`), OR if an ambient `Invariant` forces equality `A == B` conservatively at constraint-solving time (`Invariant.xform(Bivariant) = Invariant`), that restriction is *stronger* (`<=`), never unsound. Moreover, in `constraints.rs:557` (`let variance_i = self.xform(variance, variance_decl)`), `variance` is the *outer* ambient field/position variance and `variance_decl` is the *inner* callee parameter variance; thus `*const PhantomUnused<T>` computes `Covariant.xform(Bivariant) = Bivariant`, `&mut PhantomUnused<T>` computes `Invariant.xform(Bivariant) = Invariant`, while an unused struct parameter `Foo<T>(PhantomUnused<*mut T>)` computes `Bivariant.xform(Invariant)` only if passed as an ambient term — in practice, if an outer parameter occurs nowhere in fields, no `Constraint` targets it at all, leaving it `Bivariant`. Notice that `rustc_hir_analysis::variance::constraints::ConstraintContext::xform` (`constraints.rs:339-350`) optimizes `(ConstantTerm(c1), ConstantTerm(c2)) => self.constant_term(c1.xform(c2))` and `(_, ConstantTerm(Covariant)) => v1`; both rewrites preserve exact equality with `rustc`'s `Variance::xform` because `Covariant` is an exact two-sided identity (`xform_id_right`).

---

### 2. Three-Phase Fixed-Point Variance Inference Engine

`Basis: source + execution + derived`

#### 2.1 Phase 1 — Determining Inferred Variables and Seeding Lang Items (`terms.rs`)

`rustc_hir_analysis::variance::crate_variances` (`mod.rs:30-35`) orchestrates three sequential modules sharing a crate-lifetime `DroplessArena`:

1. **`terms::determine_parameters_to_be_inferred(tcx, &arena)` (`terms.rs:66-107` on `960ba7cf7e86`):**
   Walks `tcx.hir_crate_items(()).definitions()` and allocates contiguous slices of `InferredTerm(InferredIndex(i))` for each generic parameter of every:
   - `DefKind::Struct | DefKind::Union | DefKind::Enum` (plus every variant's `ctor_def_id` if present),
   - `DefKind::Fn | DefKind::AssocFn`.
   Items with `generics.count() == 0` are omitted from `inferred_starts` (`terms.rs:132-134`), requiring `constraints.rs:536` (`if args.is_empty() { return; }`) to guard lookups. On `14210df0e27c` (`1.98.0-nightly`), `terms.rs:102-104` also allocated inferreds for `DefKind::TyAlias if tcx.type_alias_is_lazy(def_id)`; `960ba7cf7e86` removed that arm.

   `lang_items(tcx)` (`terms.rs:109-123` on `960ba7cf7e86`) builds the hardcoded variance overrides for items defined within the currently compiled crate (`as_local()?`, i.e., when compiling `core`):
   - `lang_items.phantom_data()` -> `[ty::Covariant]`
   - `lang_items.unsafe_cell_type()` -> `[ty::Invariant]`
   - `lang_items.covariant_unsafe_cell_type()` -> `[ty::Covariant]` (absent on `14210df0e27c`, added in `77977f9966b6`).

#### 2.2 Phase 2 — Structural Constraint Generation (`constraints.rs`)

`constraints::add_constraints_from_crate` walks the same items and emits `Constraint { inferred, variance: &'a VarianceTerm<'a> }` representing the lattice inequality `[inferred] <= eval(variance)`. Key rules verified directly in `compiler/rustc_hir_analysis/src/variance/constraints.rs`:

- **References & raw pointers (`lines 230-233, 249-251, 474-490`):**
  - `&'r T` (`Mutability::Not`): constrains `'r` with `variance` and `T` with `variance` (`['a: +, T: +]`).
  - `&'r mut T` (`Mutability::Mut`): constrains `'r` with `variance` and `T` with `self.invariant(variance)` (`['a: +, T: o]`).
  - `*const T`: constrains `T` with `variance` (`[T: +]`).
  - `*mut T`: constrains `T` with `self.invariant(variance)` (`[T: o]`).
- **Functions (`lines 307-309, 423-434`):**
  - `fn(Inputs...) -> Output`: skips the `PolyFnSig` binder, computes `contra = self.contravariant(variance)` (`variance.xform(Contravariant)`), constrains each input with `contra`, and constrains `Output` with `variance`. Bound regions (`ReBound`) inside higher-ranked signatures generate no constraints (`lines 451-456`).
- **ADTs and `PhantomData` (`lines 259-261, 352-401`):**
  - For field type `Adt(def, args)` in ambient variance `v`, parameter `i` receives `variance_i = self.xform(v, variance_decl)` where `variance_decl` is either `InferredTerm` (intra-crate local `DefId`) or `ConstantTerm(variances_of(def_id)[i])` (cross-crate `ty::VariancesOf`).
  - For `core::marker::PhantomData<T>`, because `lang_items` hardcodes `PhantomData`'s variance to `[Covariant]`, `variance_i = v.xform(Covariant) = v`, making `PhantomData` transparently inherit the variance of `T` (e.g., `PhantomData<fn(T) -> T>` yields `Invariant`, `PhantomData<*mut T>` yields `Invariant`, `PhantomData<&'a UnsafeCell<T>>` yields `'a: Covariant, T: Invariant`).
- **Arrays, const arguments, and `[T; 0]` (`lines 235-238, 396-398, 405-418`):**
  - `ty::Array(typ, len)` adds constraints from `len` (`add_constraints_from_const`) and `typ` (`add_constraints_from_ty`) with the same `variance`. Even zero-length arrays `[T; 0]` constrain `T` positively (`UnusedParam<T>(..., [T; 0])` yields `[T: +]` in live execution), whereas completely unreferenced ADT parameters emit no constraints on `[T]` and report `[T: *]` plus `error[E0392]: type parameter T is never used` — even when `T: Copy` appears in a `where`/inline bound (`BoundUnused<T: Copy>` yields `[T: *]` + `E0392`).
  - `add_constraints_from_const` inspects only `ty::ConstKind::Alias(_, alias_const)`, making arguments of unevaluated const aliases invariant (`add_constraints_from_invariant_args`); plain const parameters emit no field constraint and are handled post-solve.
- **Aliases and trait objects (`lines 263-301`):**
  - Associated projections (`ty::Projection`), inherent aliases (`ty::Inherent`), and opaques (`ty::Opaque`) force all generic args invariant via `add_constraints_from_invariant_args`. Free type aliases (`ty::Free`) call `tcx().expand_free_alias_tys(ty)` and recurse on the expanded type (`lines 274-277`).
  - `dyn Trait<Args> + 'r` is covariant in `'r` (`add_constraints_from_region`), invariant in principal trait args (`add_constraints_from_invariant_args`), and invariant with fixed `self.invariant` on projection bounds (`lines 291-300`).

#### 2.3 Phase 3 — Constraint Solving, Convergence, and Lang-Item Override Filtering (`solve.rs`)

`solve::solve_constraints` (`solve.rs:44-72` on `960ba7cf7e86`) initializes `solutions = vec![ty::Bivariant; terms_cx.inferred_terms.len()]`, primes every `(id, variances)` in `terms_cx.lang_items`, removes constraints targeting overridden parameters, runs `SolveContext::solve()`, and materializes `CrateVariancesMap`:

```rust
let mut overridden_inferreds = FxHashSet::default();
let mut solutions = vec![ty::Bivariant; terms_cx.inferred_terms.len()];
// prime the solutions for certain lang items which have hard-coded variance
for (id, variances) in &terms_cx.lang_items {
    let InferredIndex(start) = terms_cx.inferred_starts[id];
    for (i, &variance) in variances.iter().enumerate() {
        solutions[start + i] = variance;
        overridden_inferreds.insert(start + i);
    }
}

// ensure the solutions for overridden inferreds are never constrained by anything else
if !overridden_inferreds.is_empty() {
    constraints.retain(|Constraint { inferred: InferredIndex(inferred), .. }| {
        !overridden_inferreds.contains(inferred)
    });
}
```

**Why `overridden_inferreds` + `constraints.retain(...)` became mandatory (`CovariantUnsafeCell` bug prevented):**
Before commit `77977f9966b681ff865f810869859bcb2eb13a8e`, the only two lang items in `lang_items(tcx)` (`14210df0e27c` `terms.rs:112-117`) were `PhantomData<T>(...)` (fieldless) and `UnsafeCell<T> { value: T }` (where `solve.rs` primed `solutions[start] = Invariant`, the lattice bottom!). Because `Invariant` is the bottom element (`glb(_, Invariant) = Invariant`), the constraint `[UnsafeCell::T] <= Covariant` generated from `value: T` was a harmless no-op. However, `library/core/src/cell/covariant_unsafe_cell.rs:20` defines:

```rust
#[lang = "covariant_unsafe_cell"]
pub struct CovariantUnsafeCell<#[rustc_assert_variance(covariant)] T: ?Sized>(UnsafeCell<T>);
```

Phase 2 inspects the field `UnsafeCell<T>` and emits `[CovariantUnsafeCell::T] <= InferredTerm(UnsafeCell::T)`. On the very first sweep, `evaluate` returns `Invariant`, so `glb(Invariant, Covariant)` would silently clobber `CovariantUnsafeCell`'s primed `Covariant` solution back to `Invariant`. Removing all constraints whose target lies in `overridden_inferreds` makes the override non-defeasible. This exact mechanism is mechanized in Lean:
- `covariantUnsafeCell_unfiltered_clobbers_to_invariant`: proves `solveLoop covariantUnsafeCellFieldConstraints 4 (initWithLangOverrides covariantUnsafeCellOverrides) 1 = .invariant`.
- `covariantUnsafeCell_filtered_preserves_covariant`: proves `solveWithOverrides ... 0 = .invariant` and `solveWithOverrides ... 1 = .covariant`.

**Fixed-point convergence and optimality:**
Because `glb` strictly lowers values only along chains `Bivariant (2) -> {Covariant, Contravariant} (1) -> Invariant (0)` (`Variance.potential_strict_drop`), each variable can change at most twice (`2N` total state drops across `N` inferred parameters, and at most `2C` constraints as noted in `solve.rs:66-69`). Furthermore, every `VarianceTerm` evaluation is monotone (`evalTerm_mono`). Thus, in Lean:
- `solveConstraints_is_fixed_point`: constructively proves via finite chain potential descent (`solveLoop_chain_potential_drop` + `statePotential_le`) that `solveLoop cs (2 * n) (topState n)` reaches an exact fixed point of `solvePass`.
- `solveConstraints_sound_and_complete`: proves BOTH soundness (`Satisfies cs (solveConstraints cs)`) AND completeness / optimality (`∀ s_sol, Satisfies cs s_sol -> stateLe s_sol (solveConstraints cs)` — every sound variance vector is at least as restrictive pointwise as `rustc`'s solution).

**Post-solve overrides (`solve.rs:94-138` on `main`) and cycle behavior:**
After `solve()` converges, `create_map()` runs two post-fixes:
1. `enforce_const_invariance(generics, variances)`: recursively walks `generics.own_params` and `generics.parent`, setting every `GenericParamDefKind::Const` parameter to `ty::Invariant` (`ConstParam<const N: usize>` dumps `[N: o]`).
2. `if let ty::FnDef(..) = ...`: converts every `ty::Bivariant` variance of a function definition to `ty::Invariant`, because unused generic parameters on functions are legal and must default to invariant rather than bivariant (`pub fn fn_unused<T>(_x: u8) {}` dumps `[T: o]`).

Empirical `#[rustc_dump_variances]` probes confirm cyclic fixed points predicted by the lattice:
- Mutually recursive covariant cycle + contravariant sink (`MutualA<T>(*const MutualB<T>)`, `MutualB<T>(*const MutualA<T>, PhantomData<fn(T)>)`) descends cleanly from `(*, *)` to `([T: -], [T: -])` (`mutualAB_solves_contravariant` in Lean).
- Even contravariant 2-cycle (`MutualCycleInvA<T>(PhantomData<fn(MutualCycleInvB<T>)>)`, `MutualCycleInvB<T>(PhantomData<fn(MutualCycleInvA<T>)>, *const T)`) stabilizes at **`[T: -]` on `A` and `[T: +]` on `B`** without collapsing to invariant, because two contravariant flips around the cycle return to the same polarity (`mutualCycleEven_solves_contra_cov` in Lean).
- Odd contravariant 1-cycle (`SelfCycleOddInv<T>(PhantomData<fn(SelfCycleOddInv<T>)>, *const T)`) hits both `+` (from `*const T`) and `- x + = -`, descending via `glb(+, -)` to **`[T: o]`** (`selfCycleOdd_solves_invariant` in Lean).

*(Opaque types & marker wrappers)*: Unlike structs/enums/functions, `OpaqueTy` and RPITIT `AssocTy` bypass the crate-wide fixed-point solver (`mod.rs:55-78`) and invoke `variance_of_opaque` (`mod.rs:97-227`), which defaults all type/const generics to `Invariant`, initializes ancestor/own lifetime generics to `Bivariant`, and sets any lifetime reachable through explicit trait/projection/outlives bounds to `Invariant` via `OpaqueTypeLifetimeCollector`. On `960ba7cf7e86`, `library/core/src/marker/variance.rs` provides unstable ergonomic `PhantomData` wrappers (`PhantomCovariant<T>`, `PhantomContravariant<T>`, `PhantomInvariant<T>` and lifetime counterparts) annotated with `#[rustc_assert_variance(...)]`.

---

### 3. Higher-Ranked Function Subtyping (`enter_forall` and `leak_check`)

`Basis: documentation + source + execution + derived`

#### 3.1 `TypeRelating::binders` and `InferCtxt::enter_forall` (`type_relating.rs`, `higher_ranked.rs`)

When `rustc`'s `TypeRelating` compares two `ty::Binder<'tcx, T>` values (`a` as left-hand side, `b` as right-hand side) under `self.ambient_variance`, `TypeRelating::binders` (`compiler/rustc_infer/src/infer/relate/type_relating.rs:275-351` on `960ba7cf7e86`) fast-paths equal binders or binders without escaping bound vars, and otherwise dispatches on `ambient_variance`:

```rust
match self.ambient_variance {
    ty::Covariant => {
        infcx.enter_forall(b, |b| {
            let a = infcx.instantiate_binder_with_fresh_vars(span, HigherRankedType, a);
            self.relate(a, b)
        })?;
    }
    ty::Contravariant => {
        infcx.enter_forall(a, |a| {
            let b = infcx.instantiate_binder_with_fresh_vars(span, HigherRankedType, b);
            self.relate(a, b)
        })?;
    }
    ty::Invariant => {
        infcx.enter_forall(b, |b| {
            let a = infcx.instantiate_binder_with_fresh_vars(span, HigherRankedType, a);
            self.relate(a, b)
        })?;
        infcx.enter_forall(a, |a| {
            let b = infcx.instantiate_binder_with_fresh_vars(span, HigherRankedType, b);
            self.relate(a, b)
        })?;
    }
    ty::Bivariant => {
        unreachable!("Expected bivariance to be handled in relate_with_variance")
    }
}
```

Semantically, checking `for<'b> a <: for<'a> b` requires: **for all** instantiations of the supertype (`b`), there **exists** an instantiation of the subtype (`a`) such that `a <: b`. `InferCtxt::enter_forall_and_leak_universe` (`compiler/rustc_infer/src/infer/relate/higher_ranked.rs:24-52`) calls `self.create_next_universe()` to step from outer universe `U0` (`UniverseIndex::ROOT`) to a strictly greater `next_universe = U1`, substituting every bound region in the `for<..>` binder with `ty::Region::new_placeholder(tcx, ty::PlaceholderRegion::new(next_universe, br))`. Crucially:
- A `UniverseIndex` satisfies `u1.can_name(u2) <=> u1 >= u2` (`compiler/rustc_type_ir/src/lib.rs:367-370`), so outer variables living in `U0` (`U0 < U1`, `cannot_name(U1) == true`) cannot be unified with `U1` placeholders.
- Conversely, inference variables created *inside* the `enter_forall` closure inherit universe `U1` and *can* name `U1` placeholders as well as outer `U0` regions (`'static` lives in `U0`).

Tracing the two canonical coercions makes the polarity asymmetry concrete:

1. **Positive coercion `for<'a> fn(&'a u8) -> u8 <: fn(&'static u8) -> u8`:**
   - Outer relation is `Covariant`. `sup` (`fn(&'static u8) -> u8`) has no escaping bound vars, so `enter_forall(sup)` is a no-op (`higher_ranked.rs:29-31`), while `sub`'s `'a` becomes fresh inference var `'?0` in universe `U0`.
   - Function arguments flip ambient variance to `Contravariant` (`constraints.rs` / `TypeRelating` flips variance for inputs), relating `&'?0 u8` against `&'static u8` contravariantly, i.e., `&'static u8 <: &'?0 u8`, requiring `'static: '?0`.
   - Setting `'?0 = 'static` (or any concrete caller region) trivially satisfies `'static: '?0`. Confirmed in `probe_results.json` (`HRTB_TO_STATIC=77`) and Lean theorem `hrtb_to_static_sound`.

2. **Rejected coercion `fn(&'static u8) -> u8 <: for<'a> fn(&'a u8) -> u8`:**
   - Outer relation is `Covariant`. `sup` binds `'a`, so `enter_forall` allocates universe `U1` and substitutes `'a := !a` (`PlaceholderRegion(U1)`). `sub` has no bound vars (`&'static u8`).
   - Function input polarity flips to `Contravariant`, relating `&'static u8` (`sub`) with `&'!a u8` (`sup`) contravariantly: `&'!a u8 <: &'static u8`.
   - Region relating emits the outlives constraint **`!a : 'static`** (`!a` in `U1` must outlive `'static` in `U0`).
   - `leak_check(outer_universe = U0)` inspects the constraint graph and rejects **`!a : 'static`** because `!a` belongs to `U1` which `U0` cannot name (`U0.cannot_name(U1)`). Confirmed in live `rustc` (`error[E0308]: mismatched types` / `"one type is more general than the other"`) and Lean theorem `static_to_hrtb_rejected`.

#### 3.2 How SCC `leak_check` Works and What Happens Under `-Zno-leak-check`

In `compiler/rustc_infer/src/infer/region_constraints/leak_check.rs:14-275`, `RegionConstraintCollector::leak_check` executes in two passes over the subgraph of outlives edges flagged `ty::VisibleForLeakCheck::Yes`:

1. **SCC construction (`MiniGraph::new`, `lines 360-380`):** For every constraint `R2: R1`, inserts directed edge `R2 -> R1` (`sup` edge direction in graph terms; note comment on line 368 reverses argument order `iterate_region_constraints` callback `(target, source)` and pushes `(source_node, target_node)`, so `sub` flows to `sup` / `R2 -> R1` tracks what `R2` must outlive) and runs Tarjan SCC (`Sccs::new(&graph)`).
2. **`assign_placeholder_values` (`lines 144-175`):** For each SCC `S`, computes `scc_universes[S]` as the minimum `UniverseIndex` among nodes in `S`. If `S` contains a placeholder `P` with `outer_universe.cannot_name(P.universe)` and `scc_placeholders[S]` already holds a distinct placeholder `P'`, immediately returns `TypeError::RegionsInsufficientlyPolymorphic` (`P1: P2, P1 != P2`, cyclic equality between distinct placeholders).
3. **`propagate_scc_value` (`lines 184-257`):** Walks SCCs in dependency order. For each `scc1 -> scc2`:
   - Propagates minimum successor universe into `scc1_universe.take_min(scc2_universe, ...)`.
   - If `scc1` equals a leak-checked placeholder `P1`, checks TWO error conditions:
     1. `scc1_universe.universe.cannot_name(P1.universe)` -> `P1 : R` where `R` lies in an older universe that cannot name `P1` (`TypeError::RegionsInsufficientlyPolymorphic`).
     2. Some successor `scc2` reaches a distinct placeholder `P2` -> `P1 : P2` (`P1 != P2`).
   - Crucially (`lines 72-73`), `R: P1` (a region in an outer universe constrained to outlive an inner placeholder `P1`) does **not** error in `leak_check` because `R = 'static` is a valid upper bound (`'static` outlives all placeholders).

**Why `-Zno-leak-check` still fails with `E0308`:**
As documented in `higher_ranked.rs:89-97` ("Any legitimate subtyping errors that it would have caught will now be caught later on, during region checking"), `-Zno-leak-check` skips `leak_check`, allowing MIR borrowck / NLL region inference to solve universe constraints globally later. Running `rustc --edition=2024 -Zno-leak-check` on `static_to_hrtb_no_leak_check_rejected` (`probe_results.json:93-102`) empirically confirms compilation **still fails with `error[E0308]`** (`one type is more general than the other`), with one revealing diagnostic difference: without early `leak_check` rejection during HIR typeck, inference reaches borrowck/fallback and prints `found fn pointer fn(&_) -> _` instead of `fn(&'static _) -> _`.

#### 3.3 Double-Contravariant HRTB Polarity Flip (`- x - = +`)

Suppose a higher-order function expects a callback argument whose own parameter is a function pointer. Placing the binder check inside a covariant outer function's *input* position multiplies ambient variance by `Contravariant`:

- Outer type check: `fn(fn(&'static u8) -> u8) -> u8 <: fn(for<'a> fn(&'a u8) -> u8) -> u8`
- At `TyCtx.fnArg (.fnPtr arg .u8)` (`ambient = Contravariant`): flips LHS and RHS, reducing the obligation to:
  `for<'a> fn(&'a u8) -> u8 <: fn(&'static u8) -> u8`
- At the inner `fn` input position, `Contravariant.xform(Contravariant) = Covariant` (`contravariant_xform_involutive`), restoring the positive instantiation direction!

Semantically, trace caller vs. callee obligations in the higher-order signature:
- `call_with_static(g)` (`fn(fn(&'static u8) -> u8) -> u8`) passes `&'static 55` into its callback argument `g`.
- Coercing `call_with_static` to `fn(for<'a> fn(&'a u8) -> u8) -> u8` promises future callers that any polymorphic callback `id_ref : for<'a> fn(&'a u8) -> u8` they supply will execute safely inside `call_with_static`. Because a function defined `for<'a>` handles `'static` in particular, passing `id_ref` to `call_with_static` is sound (`DOUBLE_FLIP=55` in live execution; Lean theorem `double_contravariant_flip_sound`).
- Conversely, coercing `fn(for<'a> fn(&'a u8) -> u8) -> u8` to `fn(fn(&'static u8) -> u8) -> u8` is unsound because the higher-order implementation is allowed to invoke its callback on short-lived local stack references `'a`, whereas a future caller's `fn(&'static u8) -> u8` callback requires `'static`; this reverse direction is rejected both in live `rustc` (`E0308`) and in Lean (`double_flip_reverse_rejected`).

---

### 4. `google/zerocopy` `PtrInner<'a, T>` and `Ptr<'a, T, I>` Variance Architecture

`Basis: documentation + source + execution + derived`

#### 4.1 Exact Definition and MSRV 1.65 Rationale (`inner.rs`, `ptr.rs`)

In `google/zerocopy@2b88472905b75a71b3940ef2a23a814abff46695`, the safe pointer abstraction is factored into an outer invariant-carrying wrapper `Ptr<'a, T, I>` and an inner lifetime-and-provenance core `PtrInner<'a, T>`. In `zerocopy/src/pointer/inner.rs:32-72`:

```rust
pub struct PtrInner<'a, T>
where
    T: ?Sized,
{
    ptr: NonNull<T>,
    // SAFETY: `&'a UnsafeCell<T>` is covariant in `'a` and invariant in `T`
    // [1]. We use this construction rather than the equivalent `&mut T`,
    // because our MSRV of 1.65 prohibits `&mut` types in const contexts.
    //
    // [1] https://doc.rust-lang.org/1.81.0/reference/subtyping.html#variance
    _marker: PhantomData<&'a core::cell::UnsafeCell<T>>,
}
```

`PtrInner::new` (`inner.rs:98-102`) is `pub const unsafe fn new(ptr: NonNull<T>) -> PtrInner<'a, T>`. Because `zerocopy` supported MSRV 1.65 at the time of `inner.rs`'s design, `&'a mut T` could not appear in `PhantomData<&'a mut T>` inside `const fn` signatures without hitting pre-stabilization `const_mut_refs` restrictions, even though `&'a mut T` has the identical variance vector `['a: +, T: o]`. Replacing `&'a mut T` with `&'a core::cell::UnsafeCell<T>` invokes `Covariant.xform(Ref_lifetime) = +` for `'a` and `Covariant.xform(Covariant.xform(UnsafeCell::T)) = + x (+ x o) = o` for `T`, in a type legal inside `const fn` (`PhantomData`).

`zerocopy/src/pointer/ptr.rs:57-73` then wraps `PtrInner`:

```rust
pub struct Ptr<'a, T, I>
where
    T: ?Sized,
    I: Invariants,
{
    // SAFETY: `PtrInner<'a, T>` is covariant in `'a` and invariant in `T`.
    ptr: PtrInner<'a, T>,
    _invariants: PhantomData<I>,
}
```

Because `PtrInner<'a, T>` contributes `'a: +` and `T: o`, `NonNull<T>` contributes `T: +` (`glb(+, o) = o`), and `PhantomData<I>` contributes `I: +` (where `I` is an `(Aliasing, Alignment, Validity)` triple implementing `Invariants`, `zerocopy/src/pointer/invariant.rs:19-29`), `rustc` infers **`['a: +, T: o]`** for `PtrInner` and **`['a: +, T: o, I: +]`** for `Ptr` (verified empirically in `zerocopy_ptr_dump_variances` and formally in Lean theorem `zerocopyPtr_derived_variances`). This variance vector interacts directly with `Ptr`'s safe operations in `zerocopy/src/pointer/ptr.rs:135-296`:
- `Copy` and `Clone` are implemented only for `I: Invariants<Aliasing = Shared>` (`ptr.rs:135-152`), preserving uniqueness for `Exclusive`.
- Lifetime shortening without copying `Ptr` relies both on covariance in `'a` (`Ptr<'big, T, I> <: Ptr<'small, T, I>`) and explicit `Ptr::reborrow<'b>(&'b mut self) -> Ptr<'b, T, I> where 'a: 'b` (`ptr.rs:293-296`).
- Covariant `I` permits subtyping coercions whenever an invariant parameter itself carries lifetime parameters, while avoiding invariant barriers on marker-type projections.

#### 4.2 Historical Fix (`fe70ab691`), Uniform ADT Variance, and Referent Invariance Proof

Prior to `google/zerocopy` commit `fe70ab6911f954f390b9ff04871e3c58fbba24e0` (`[pointer] Fix Ptr[Inner] variance (#2351) (#2393)`, 2025-02-25):
- Doc comments claimed `Ptr<'a, T>` and `PtrInner<'a, T>` were covariant in both `'a` and `T`.
- `PtrInner<'a, T>` held `PhantomData<&'a T>`, making it genuinely covariant in both `'a` and `T`.
- `Ptr<'a, T, I>` used associated types/GATs in trait projections on `I`, which forced `add_constraints_from_invariant_args` and inadvertently made `'a` or `T` invariant via trait projections!
- Meanwhile, covariant `T` is *unsound* for `Exclusive` pointers (which can overwrite the referent in place just like `&'a mut T`).

Commit `fe70ab6911f954f3` changed `PtrInner` to `PhantomData<&'a core::cell::UnsafeCell<T>>` so `Ptr<'a, T, Exclusive>` matches `&'a mut T` (`['a: +, T: o]`). Why is `Ptr<'a, T, Shared>` **also** invariant in `T`?
1. **Structural language constraint:** `rustc` computes **one variance slice** per nominal ADT definition in `CrateVariancesMap` (`constraints.rs` / `solve.rs`). Rust has no conditional variance dependent on a type argument (`Shared` vs `Exclusive`), so forcing `T: o` for `Exclusive` necessarily makes `Ptr<'a, T, I>` invariant in `T` for all `I`, including `Shared`.
2. **Interior mutability safety (`UnsafeCell` / `Sync` soundness):** Even a `Shared` pointer `Ptr<'a, T, (Shared, ...)>` can refer to interior-mutable types (`UnsafeCell<U>`, atomics, mutexes) or be transmuted/upgraded under invariants; requiring referent invariance matches `zerocopy/tests/ui/ptr-is-invariant-over-v.rs:17-34`, which asserts compile-time rejection of `Ptr<'small, &'big u32, ...>` -> `Ptr<'small, &'small u32, ...>` for **both** `(Exclusive, Aligned, Safe)` (`_when_exclusive`) and `(Shared, Aligned, Safe)` (`_when_shared`). Both rejections were reproduced live against the compiled `zerocopy 0.8.64` `libzerocopy.rlib` (`real_zerocopy_referent_invariant_rejected`), while lifetime shortening (`Ptr<'big, u8, ...>` -> `Ptr<'small, u8, ...>`) succeeded for both `Shared` (`REAL_ZC_SHARED=91`) and `Exclusive` (`REAL_ZC_EXCL=7`).

**Why `T` covariance permits aliasing-lifetime forgery (mechanized in Lean `Part 4`):**
In `support/VarianceLatticeHrtbSubtypingSoundness.lean:1527-1684`:
- Define runtime `Heap` mapping locations to `MemSlot { allocDur : Nat, val : HeapVal }`, `ValWellTyped h clk val ty` requiring every `&'r inner` stored inside a slot with `outerDur` to point to an allocation surviving at least `outerDur` whenever `clk <= outerDur`, and `writeThroughPtrAndReadOuter` which overwrites the referent slot via a `Ptr` and then dereferences it through a surviving outer alias at `readClk`.
- **Soundness under `T: o, 'a: +` (`ptr_lifetime_covariant_and_invariant_T_sound`):** Shortening `'big` to `'small` preserves `ValWellTyped` (`ptr_lifetime_shortening_preserves_ValWellTyped`), and writing a new `&'big u8` guarantees `.ok newVal` on any read within `'big`.
- **Forgery under hypothetical `T: +` (`zcPtrBadCov`, `ptrBadCov_coercion_accepted` & `ptrBadCov_forgery_causes_dangling_read`):** Starting from `forgeryInitHeap` where slot `0` (`allocDur = 10`, `'big`) holds `&'10 u8` at slot `1`, coercing `PtrBadCov<'5, &'10 u8, Exclusive>` to `PtrBadCov<'2, &'2 u8, Exclusive>` succeeds via `SubTy.zcPtrBadCov`. Writing `&'2 u8` pointing to short-lived slot `2` (`allocDur = 2`) into slot `0`, and subsequently reading slot `0` via the surviving `'big` alias at clock `readClk = 5` (`2 < 5 <= 10`, after slot `2` expired!), evaluates via `rfl` directly to **`ExecResult.danglingRead 2 5 2`**. Meanwhile, `ptrReal_blocks_forgery_coercion` proves that `SubTy.zcPtr` rejects that exact coercion.

---

### 5. Anneal Downstream Verification Boundary and Lean 4 Formalization

`Basis: source + execution + derived`

#### 5.1 Pre-MIR Boundary in `joshlf/anneal` (`MirAst.lean`)

In `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), Anneal consumes post-cleanup MIR bodies emitted by `anneal-rustc-capture` and models `rustc_middle::mir::StatementKind` in `trusted/lean/Trusted/MirAst.lean:630-662`. Specifically, line 641 quotes upstream `AscribeUserType(Box<(Place<'tcx>, UserTypeProjection)>, ty::Variance)`, and lines 654-656 explicitly fold it into `.unsupported` (fail-closed rejection in MIR execution if encountered). Thus:
- Subtyping coercions, higher-ranked `enter_forall`/`leak_check` validation, and `zerocopy`'s `Ptr<'a, T, I>` variance barriers are discharged strictly in `rustc` HIR/typeck + borrowck **before** MIR body generation.
- Conversely, if Anneal models surface Rust type safety or user type ascriptions (`AscribeUserType`), those variance constraints are governed by `rustc_type_ir::Variance` and `rustc_hir_analysis::variance` rather than operational MIR semantics alone.

#### 5.2 Complete Lean `v4.34.1` Mechanization Inventory (`VarianceLatticeHrtbSubtypingSoundness.lean`)

All definitions in `support/VarianceLatticeHrtbSubtypingSoundness.lean` (`namespace RustcVarianceHrtbPtr`, 1,686 LOC) mark every definition `noncomputable def`, avoid `deriving` on inductive types (providing manual `beq` + `beq_eq_true_iff` and `eq_or_ne`), avoid `sorry` / `Classical.choice` / `omega` / `bv_decide` / `native_decide` / `partial def`, and compile with zero `_unsafe_rec` constants using only constructive axioms `[propext, Quot.sound]`:

| Section | Core Definitions | Key Kernel-Checked Theorems |
| :--- | :--- | :--- |
| **Part 1** (`L26-L375`) Variance Lattice & `xform` | `Variance`, `needsFwd`, `needsBwd`, `ofDirs`, `glb`, `lub`, `le`, `potential`, `xform`, `xformPldi11` | `ofDirs_needs`, `le_{refl,antisymm,trans}`, `glb_{comm,assoc,idem,le_left,le_right}`, `le_glb`, `le_iff_glb_eq`, `distrib_{glb_lub,lub_glb}`, `xform_{assoc,id_left,id_right,inv_left,biv_left,mono}`, `contravariant_xform_involutive`, `xform_contravariant_flips_dirs`, `xform_glb_dist_{left,right_le,right_of_ne_bivariant,right_fails_at_bivariant}`, `xform_rustc_not_comm`, `xform_comm_unless_inv_bi`, `xform_rustc_le_pldi11`, `potential_strict_drop`, `potential_le_two` |
| **Part 2** (`L391-L985`) Fixed-Point Solver & `CovariantUnsafeCell` | `VarianceTerm`, `VarianceConstraint`, `evalTerm`, `topState`, `applyConstraint`, `solvePass`, `solveLoop`, `solveConstraints`, `Satisfies`, `statePotential`, `filterOverridden`, `solveWithOverrides`, `zerocopyPtrConstraints` | `evalTerm_mono`, `statePotential_{le,mono,strict_drop_at}`, `applyConstraint_le`, `solvePass_{le,preserves_bound}`, `solveLoop_{le,preserves_bound,chain_potential_drop,stable_of_fixed}`, `fixed_point_satisfies`, `stateEqOrDiff`, `findFixedPoint`, **`solveConstraints_is_fixed_point`**, **`solveConstraints_sound_and_complete`**, `mutualAB_solves_contravariant`, `mutualCycleEven_solves_contra_cov`, `selfCycleOdd_solves_invariant`, `covariantUnsafeCell_unfiltered_clobbers_to_invariant`, `covariantUnsafeCell_filtered_preserves_covariant`, `zerocopyPtr_derived_variances` |
| **Part 3** (`L994-L1496`) HRTB Subtyping & Polarity Soundness | `Region`, `Region.outlives`, `Region.substBVar`, `Region.wf`, `Ty`, `Ty.substRegion`, `SubTy` (`forallLeft`, `forallRight`, `zcPtrInner`, `zcPtr`, `zcPtrBadCov`), `RelTy`, `TyCtx`, `TyCtx.{plug,variance,siblingsRefl}`, `tyHrtbFn`, `tyStaticFn` | `Region.outlives_{refl,trans}`, `placeholder_not_outlives_static`, `SubTy.refl_basic`, `RelTy.{covariant_iff,contravariant_iff,invariant_iff,flip_contravariant,mono_of_le,xform_compose}`, **`ctx_polarity_sound_both`**, **`ctx_polarity_sound`**, **`hrtb_to_static_sound`**, **`static_to_hrtb_rejected`**, **`double_contravariant_flip_sound`**, **`double_flip_reverse_rejected`** |
| **Part 4** (`L1505-L1686`) `zerocopy` `Ptr` Soundness & Forgery Witness | `HeapVal`, `MemSlot`, `Heap`, `ValWellTyped`, `ExecResult`, `writeThroughPtrAndReadOuter`, `forgeryInitHeap` | `zerocopy_ptr_lifetime_covariant_ok`, `zerocopy_ptr_referent_invariant_rejected`, `ptr_lifetime_shortening_preserves_ValWellTyped`, **`ptr_lifetime_covariant_and_invariant_T_sound`**, `ptrBadCov_coercion_accepted`, **`ptrBadCov_forgery_causes_dangling_read`**, **`ptrReal_blocks_forgery_coercion`** |

## Boundaries

The following scope boundaries and negative results prevent unwarranted generalization:

1. **`known not to apply` — Commutativity and right-distributivity of `rustc`'s `Variance::xform`.**
   Proof by explicit witness (`Variance.xform_rustc_not_comm` and `Variance.xform_glb_dist_right_fails_at_bivariant`) establishes that PLDI'11 commutativity and unconditional right-distributivity over `glb` do **not** hold for `rustc_type_ir::Variance::xform`: `Invariant.xform(Bivariant) = Invariant != Bivariant = Bivariant.xform(Invariant)`.
2. **`known not to apply` — Unfiltered constraint solving in the presence of `CovariantUnsafeCell`.**
   Proof `covariantUnsafeCell_unfiltered_clobbers_to_invariant` and inspection of `solve.rs:49-65` establish that hardcoding `solutions[start] = Covariant` without `overridden_inferreds` filtering (`constraints.retain(...)`) fails to produce `Covariant` because the inner `UnsafeCell<T>` field constraint overrides it to `Invariant`.
3. **`known not to apply` — Early `leak_check` necessity under `-Zno-leak-check`.**
   Running `rustc 1.98.0-nightly -Zno-leak-check` (`static_to_hrtb_no_leak_check_rejected`) establishes that skipping `leak_check` does **not** make `fn(&'static u8) -> u8 <: for<'a> fn(&'a u8) -> u8` compile; borrowck/NLL still rejects it with `E0308`. (Whether `-Zno-leak-check` changes trait-coherence overlap decisions was `not examined`.)
4. **`unsupported` — `CovariantUnsafeCell` compilation on `rustc 1.98.0-nightly` (`14210df0e27c`).**
   Live compilation with `#![feature(covariant_unsafe_cell)]` on `14210df0e27c` fails with `E0635` and `E0432` because `CovariantUnsafeCell` landed later on `2026-07-22` (`77977f9966b681ff865f810869859bcb2eb13a8e`). Empirical runtime execution on a post-`77977f9966b6` `rustc` toolchain binary was `not examined` on this host; `CovariantUnsafeCell` behavior on `960ba7cf7e86` rests on direct source inspection and Lean modeling.
5. **`not examined` — Next-generation trait solver (`-Znext-solver`) and `rustc_next_trait_solver` binder relation.**
   Source inspection covered the classic `TypeRelating` in `compiler/rustc_infer/src/infer/relate/type_relating.rs:58` (`assert!(!infcx.next_trait_solver)`). While `rustc_type_ir::Variance` itself is shared (`compiler/rustc_type_ir/src/lib.rs`), `-Znext-solver` generalization, `NormalizesTo`, and alias-relate variance interactions were `not examined`.
6. **`not examined` — MIR/Borrowck Polonius region inference, opaque/RPITIT cycles, and Stacked/Tree Borrows.**
   `variance_of_opaque` in `mod.rs:97-227` was audited at the source level (showing how `OpaqueTypeLifetimeCollector` walks explicit bounds), but cyclic opaque/TAIT examples and full NLL region constraint solving were not executed or mechanized in Lean. Likewise, the Lean operational model (`Part 4`) proves single-location aliasing-lifetime soundness and dangling-read forgery via allocation durations rather than modeling full Stacked Borrows or Tree Borrows protector/permission graphs.
7. **`unknown` — Future deprecation/removal schedule of `leak_check` and stabilization of `phantom_variance_markers` / `covariant_unsafe_cell`.**
   Source comments in `leak_check.rs:26-27` state *"The eventual fate of the leak checker is not yet settled"*, and both `#![unstable(feature = "phantom_variance_markers", issue = "135806")]` and `#![unstable(feature = "covariant_unsafe_cell", issue = "159735")]` remain unstable on `960ba7cf7e86`; stabilization timelines cannot be determined from source.

## Evidence

### Upstream Git Source Coordinates

| Subject | Repository & Commit | File & Range | What Was Verified |
| :--- | :--- | :--- | :--- |
| `Variance` & `xform` | `rust-lang/rust` `@960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_type_ir/src/lib.rs:257-378` | `Variance`, `Variance::xform` arm ordering (`Invariant` before `Bivariant`), `Debug` symbols (`+`, `-`, `o`, `*`), `UniverseIndex::can_name` / `cannot_name` |
| `terms` (`main` vs `1.98.0`) | `rust-lang/rust` `@960ba7cf7e86...` & `@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_hir_analysis/src/variance/terms.rs:1-150` | `InferredIndex`, `VarianceTerm`, `lang_items(...)`, addition of `covariant_unsafe_cell_type()` in `960ba7cf7e86`, removal of lazy `DefKind::TyAlias` |
| `constraints` | `rust-lang/rust` `@960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_hir_analysis/src/variance/constraints.rs:151-491` | `ConstraintContext::xform` short-circuits, `&`/`*`/`fn`/`Adt`/array/const/alias/`dyn Trait`/`ReBound` constraint emission |
| `solve` (`main` vs `1.98.0`) | `rust-lang/rust` `@960ba7cf7e86...` & `@14210df0e27c...` | `compiler/rustc_hir_analysis/src/variance/solve.rs:1-164` | `glb`, `overridden_inferreds` + `constraints.retain(...)`, `2C` `while changed` loop, `enforce_const_invariance`, `ty::FnDef` `Bivariant -> Invariant` clamp |
| `mod` & `dump` | `rust-lang/rust` `@960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `variance/{mod.rs:30-227, dump.rs:1-60}` | `crate_variances`, `variances_of`, `variance_of_opaque`, `#[rustc_dump_variances]` formatting |
| `CovariantUnsafeCell` | `rust-lang/rust` `@77977f9966b681ff865f810869859bcb2eb13a8e` & `@960ba7cf7e86...` | `library/core/src/cell/covariant_unsafe_cell.rs:1-172` | `#[lang = "covariant_unsafe_cell"]`, wrapper over `UnsafeCell<T>`, `#[rustc_assert_variance(covariant)]` |
| Phantom variance markers | `rust-lang/rust` `@960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `library/core/src/marker/variance.rs:1-285` | `PhantomCovariant`, `PhantomContravariant`, `PhantomInvariant`, lifetime forms, `#[rustc_assert_variance(...)]` |
| Higher-ranked relating | `rust-lang/rust` `@960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `infer/relate/{higher_ranked.rs:24-105, type_relating.rs:275-351}` | `enter_forall_and_leak_universe`, `enter_forall`, `leak_check`, `TypeRelating::binders` |
| SCC `leak_check` | `rust-lang/rust` `@960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `infer/region_constraints/leak_check.rs:13-405` | `MiniGraph`, `assign_placeholder_values`, `propagate_scc_value`, `RegionsInsufficientlyPolymorphic` |
| `zerocopy` pointers | `google/zerocopy` `@2b88472905b75a71b3940ef2a23a814abff46695` (`src/` == `@907b9175fee081872ec883ca4709e6ad922f8ed0`) | `zerocopy/src/pointer/{inner.rs:32-102, ptr.rs:57-73}`, `zerocopy/tests/ui/ptr-is-invariant-over-v.rs:17-35` | `PtrInner<'a, T>` (`PhantomData<&'a UnsafeCell<T>>`), MSRV 1.65 `const` safety comment, `Ptr<'a, T, I>`, `Exclusive` & `Shared` invariance UI test |
| Historical `zerocopy` fix | `google/zerocopy` `@fe70ab6911f954f390b9ff04871e3c58fbba24e0` | `src/pointer/{inner.rs, ptr.rs}`, `tests/ui-nightly/ptr-is-invariant-over-v.rs` | Transition from covariant `PhantomData<&'a T>` + GATs to `['a: +, T: o]` |
| Anneal MIR boundary | `joshlf/anneal` `@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean:641,654-656` | `StatementKind::AscribeUserType(..., ty::Variance)` classified under `.unsupported` |

### Empirical `rustc 1.98.0-nightly` + `zerocopy 0.8.64` Execution (`support/probe_results.json`)

Executed on `2026-11-23` via `python3 support/probe_variance_subtyping_hrtb.py` using `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and compiling `zerocopy` `0.8.64` (`907b9175fee081872ec883ca4709e6ad922f8ed0` with `--cfg no_zerocopy_allocator_api_1_100_0` matching `zerocopy` source at `2b88472905b7`):

| Group / Probe Key | Compile / Run Outcome | Exact Observed Output / Diagnostic Summary |
| :--- | :--- | :--- |
| `rustc_dump_variances_output` | `compile=1` (19 errors) | `CovPtr [T: +]`, `InvPtr [T: o]`, `FnVar [T: -, U: +]`, `FnInv [T: o]`, `CellWrap [T: o]`, `SharedRef ['a: +, T: +]`, `MutRef ['a: +, T: o]`, `UnusedParam [T: +]`, `TrueUnused [T: *]` (+`E0392`), `BoundUnused [T: *]` (+`E0392`), `ConstParam [N: o]`, `fn_unused [T: o]`, `MutualA [T: -]`, `MutualB [T: -]`, `MutualCycleInvA [T: -]`, `MutualCycleInvB [T: +]`, `SelfCycleOddInv [T: o]` |
| `covariant_unsafe_cell_availability` | `compile=1` | `E0432: unresolved import core::cell::CovariantUnsafeCell` and `E0635: unknown feature covariant_unsafe_cell` |
| `subtyping_positive_coercions` | `compile=0, run=0` | `COV_REF=42 FN_CONTRA=42 CONST_PTR=42 LOCAL=9` |
| `invariant_mut_ref_rejected` | `compile=1` | `error: lifetime may not live long enough` (`mutable references are invariant over their type parameter`) |
| `invariant_unsafe_cell_rejected` | `compile=1` | `error: lifetime may not live long enough` (`the struct UnsafeCell<T> is invariant over the parameter T`) |
| `contravariant_fn_reverse_rejected` | `compile=1` | `error: lifetime may not live long enough` (`fn(&'static u8) -> fn(&'a u8)` requires `'a: 'static`) |
| `invariant_phantom_fn_t_to_t_rejected` | `compile=1` | `error: lifetime may not live long enough` on `PhantomData<fn(&'static u8) -> &'static u8>` -> `PhantomData<fn(&'a u8) -> &'a u8>` |
| `invariant_phantom_mut_ptr_rejected` | `compile=1` | `error: lifetime may not live long enough` (`mutable pointers are invariant over their type parameter`) |
| `hrtb_and_double_contravariant_flip_ok` | `compile=0, run=0` | `HRTB_TO_STATIC=77 DOUBLE_FLIP=55` |
| `static_to_hrtb_rejected` | `compile=1` | `error[E0308]: mismatched types` (`one type is more general than the other`: expected `for<'a> fn(&'a _) -> _`, found `fn(&'static _) -> _`) |
| `static_to_hrtb_no_leak_check_rejected` | `compile=1` (`-Zno-leak-check`) | `error[E0308]: mismatched types` (`one type is more general than the other`: expected `for<'a> fn(&'a _) -> _`, found `fn(&_) -> _`) |
| `double_flip_reverse_rejected` | `compile=1` | `error[E0308]: mismatched types` (`expected fn(fn(&'static _) -> _) -> _`, `found fn(for<'a> fn(&'a _) -> _) -> _`) |
| `zerocopy_ptr_dump_variances` | `compile=1` (2 errors) | `ZcPtrInner ['a: +, T: o]`, `ZcPtr ['a: +, T: o, I: +]` |
| `zerocopy_ptr_lifetime_covariant_ok` | `compile=0, run=0` | `ZC_PTR_COVARIANT_LT=91` |
| `zerocopy_ptr_shared_referent_t_invariant_rejected` | `compile=1` | `error: lifetime may not live long enough` (`the struct ZcPtr<'a, T, I> is invariant over the parameter T`) |
| `real_zerocopy_crate` + `real_zerocopy_lifetime_covariant_ok` | `crate_build=0, compile=0, run=0` | `REAL_ZC_SHARED=91 REAL_ZC_EXCL=7` |
| `real_zerocopy_referent_invariant_rejected` | `compile=1` (2 errors) | Both `_when_exclusive` and `_when_shared` fail: `the struct Ptr<'a, T, I> is invariant over the parameter T` |

### Lean `v4.34.1` Kernel Verification and MetaM Purity Audit (`support/VarianceLatticeHrtbSubtypingSoundness.lean`)

Verified on `2026-11-23` against `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`):
- **Standalone compiler check:**
  `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/VarianceLatticeHrtbSubtypingSoundness.lean` exited `0` with zero warnings or errors (`1,686` lines, `77,215` bytes).
- **MetaM constant & axiom audit over `RustcVarianceHrtbPtr.*`:**
  - `DECL_COUNT=682` (including `THM_COUNT=249`)
  - `UNSAFE_REC_COUNT=0` (every `def` marked `noncomputable def`, zero `deriving` clauses on inductive types)
  - `AXIOMS=[Quot.sound, propext]` (`0` `sorryAx`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`)
  - Zero occurrences of `omega`, `bv_decide`, `native_decide`, `partial def`, `sorry`, or `Classical` outside doc comments.

## Revalidation

All verification checks are standalone and repeatable without external network access:

1. **Re-run the live `rustc` and real `zerocopy` probe suite:**
   Run without `--zerocopy-lib` to validate standard-library and compiler probes, or supply `--zerocopy-lib <path/to/zerocopy/src/lib.rs>` to recompile and test `zerocopy` `Ptr<'a, T, I>` directly:
   ```bash
   python3 reports/rustc-variance-inference-lattice-hrtb-subtyping-and-zerocopy-ptr-variance/support/probe_variance_subtyping_hrtb.py \
     --zerocopy-lib /path/to/zerocopy/src/lib.rs \
     --out /tmp/revalidated_probe_results.json
   ```
   Verify `subtyping_positive_coercions` (`COV_REF=42 FN_CONTRA=42 CONST_PTR=42 LOCAL=9`), `hrtb_and_double_contravariant_flip_ok` (`HRTB_TO_STATIC=77 DOUBLE_FLIP=55`), `real_zerocopy_lifetime_covariant_ok` (`REAL_ZC_SHARED=91 REAL_ZC_EXCL=7`), all `E0308` / invariance rejections, and whether `covariant_unsafe_cell_availability` still errors (`rustc <= 1.98.0-nightly`) or succeeds (post-`77977f9966b6` nightlies).

2. **Re-verify the Lean `v4.34.1` formalization and kernel axioms:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/rustc-variance-inference-lattice-hrtb-subtyping-and-zerocopy-ptr-variance/support/VarianceLatticeHrtbSubtypingSoundness.lean
   ```
   To re-audit `_unsafe_rec` count and `Lean.collectAxioms` across `RustcVarianceHrtbPtr.*`, elaborate the file alongside `import Lean` in a temporary script calling `Lean.collectAxioms` over every constant in `env.constants` whose name starts with `RustcVarianceHrtbPtr.` and assert `UNSAFE_REC_COUNT=0` and `AXIOMS=[Quot.sound, propext]`.

3. **Run `zerocopy`'s upstream variance UI test:**
   Inside a `google/zerocopy` checkout, run UI tests targeting `zerocopy/tests/ui/ptr-is-invariant-over-v.rs` (e.g., `cargo test --test ui ptr-is-invariant-over-v`) to confirm both `_when_exclusive` and `_when_shared` match the `.stderr` golden diagnostics.

4. **Check upstream `rust-lang/rust` drift against `960ba7cf7e8666ecb449402ca82b6e9e631bd227`:**
   Diff the variance and higher-ranked modules against `960ba7cf7e86`:
   ```bash
   git diff 960ba7cf7e8666ecb449402ca82b6e9e631bd227..HEAD -- \
     compiler/rustc_type_ir/src/lib.rs \
     compiler/rustc_hir_analysis/src/variance/ \
     compiler/rustc_infer/src/infer/relate/higher_ranked.rs \
     compiler/rustc_infer/src/infer/relate/type_relating.rs \
     compiler/rustc_infer/src/infer/region_constraints/leak_check.rs \
     library/core/src/cell/covariant_unsafe_cell.rs \
     library/core/src/marker/variance.rs
   ```
   If `Variance::xform` arm ordering (`Invariant` vs `Bivariant`), `overridden_inferreds` filtering in `solve.rs`, or `TypeRelating::binders` (`-Znext-solver` unification with `rustc_next_trait_solver`) changes, re-audit the affected subsection under **Findings**.
