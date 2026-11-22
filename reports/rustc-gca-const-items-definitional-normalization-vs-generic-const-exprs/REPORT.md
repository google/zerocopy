# `rustc` Type-Level Const Generics: `gca_min_const_items`, `gca_const_items`, and `core::gca!(...)` Definitional Normalization Under `-Znext-solver=globally` vs. `generic_const_exprs`

## Summary

In `rustc` starting with Rust `1.100.0` (verified in `rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` / `1.102.0-nightly` and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` / `main`), the pre-`1.100.0` feature gates `min_generic_const_args` and `generic_const_args` — together with their `type const` keyword syntax that broke ordinary `const` items in array lengths — were removed (`E0557`) and replaced by the Generic Constant Arguments (GCA) feature family: `#![feature(gca_min_const_items)]` (tracking issue `#132980`), `#![feature(gca_const_items)]` (tracking issue `#151972`), and the compiler built-in macro `core::gca!(...)` (`library/core/src/marker.rs:1088-1097`, `compiler/rustc_builtin_macros/src/gca.rs:8-26`).

Under the nightly default next-generation trait solver (`-Znext-solver=globally`, enabled via `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY`, tracking issue `#160895`), GCA const items provide **definitional type-level normalization without `where [(); ...]:` (`ConstEvaluatable`) bounds** and without triggering CTFE on polymorphic expressions:

1. **Direct Representation (`ConstItemRhs::Direct`) and Definitional Normalization:** Wrapping a const item's right-hand side or const generic argument in `core::gca!(...)` lowers it via `ast::ExprKind::GcaMacro` / `ast::TyKind::GcaMacro` into `hir::ConstItemRhs::Direct` and `ty::ConstKind::Alias(IsRigid::No, AliasConst { kind, args })` rather than an opaque `AnonConst` body. The query `const_of_item` (`compiler/rustc_hir_analysis/src/collect.rs:1844-1879`) returns `Some(EarlyBinder<Const>)` exclusively for direct items, enabling `rustc_next_trait_solver` (`normalizes_to.rs:464-486`, `project_goals/free_alias.rs:36-53`, `project_goals/inherent.rs:47-69`) to unfold `<T as Tr>::SIZE`, `FREE`, and `S::ASSOC` definitionally. When arguments remain polymorphic (`TooGeneric`) under `gca_const_items`, `EvalCtxt::evaluate_const` (`eval_ctxt/mod.rs:1677-1695`) marks the alias rigid (`IsRigid::Yes`) with `Certainty::Yes`, permitting `[u8; core::gca!(<T as Tr>::SIZE)]` to typecheck without any `where [(); ...]:` bound and to normalize definitionally to `[u8; 4]` upon concrete instantiation (`Four`).
2. **Compatibility Restoration Across the `1.100.0` Transition:** In `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), enabling `#![feature(min_generic_const_args)]` rejected ordinary `pub const PLAIN: usize = 3; pub fn f() -> [u8; PLAIN]` with `error: use of const in the type system not defined as type const`. Post-`1.100.0` `gca_min_const_items` + `gca_const_items` restores plain `const` compatibility (`rc = 0`) because direct representation is opt-in per expression via `core::gca!(...)` (unless `gca_macroless_args` or `gca_macroless_items` is additionally enabled), while rejecting unguarded generic arithmetic (`core::gca!(T::N + 1)`) at the definition site (`error: complex const arguments must be placed inside of a const block`).
3. **Why `#![feature(generic_const_exprs)]` Forces a Solver Downgrade and Breaks Substitution Stability:** `TyCtxt::next_trait_solver_globally` (`compiler/rustc_middle/src/ty/context.rs:3150-3154`) explicitly returns `false` whenever `self.features().generic_const_exprs()` is enabled, silently downgrading the crate to `-Znext-solver=coherence` (the legacy trait solver) while `warn_next_solver_and_gce` (`compiler/rustc_ast_passes/src/feature_gate.rs:735-751`) emits the `#160895` warning. In `1.98.0-nightly`, prior to that automatic downgrade, combining `-Znext-solver=globally` with `generic_const_exprs` hard-errored and overflowed with 12 `E0275` errors. Inside the legacy solver, `PredicateKind::ConstEquate` (`fulfill.rs:706-830`) expands `AnonConst` bodies via `thir_abstract_const` into `ty::ConstKind::Expr` and relates them via strictly positional `impl Relate for ty::Expr` (`compiler/rustc_middle/src/ty/relate.rs:101-124`) with zero algebraic commutativity — rejecting `[u8; N + 1]` against `[u8; 1 + N]` with `E0308`. Simultaneously, `is_const_evaluatable` (`const_evaluatable.rs:26-88`) discharges `where [(); N - 1]:` purely syntactically from `caller_bounds`, allowing an uncalled `fn sub_one<const N: usize>() -> [u8; N - 1]` to compile cleanly (`rc = 0`) while deferring `0_usize - 1_usize` underflow (`E0080`) until call-site instantiation / monomorphization.
4. **Acyclic `is_trivial_const` Query Termination vs. Mutual Cycle `E0391`:** Ordinary constant evaluation (`eval_to_const_value_raw_provider`, `eval_queries.rs:377`) first probes `tcx.trivial_const(def_id)` (`compiler/rustc_mir_transform/src/trivial_const.rs:46-124`), which accepts single-block MIR bodies assigning either an already-computed `Const::Val` or a parameterless `Const::Unevaluated` chain. Because `mir_built` (`mir_transform/src/lib.rs:395-408`) invokes `trivial_const` on the freshly constructed `Body`, mutually recursive plain constants `pub const A: usize = B; pub const B: usize = A;` deterministically trigger a 4-hop `E0391` query cycle (`trivial_const(A) -> mir_built(A) -> trivial_const(B) -> mir_built(B) -> trivial_const(A)`), whereas direct `type const` / GCA cycles under `-Znext-solver=globally` fail inside next-solver normalization (`E0271`).
5. **Implications for Anneal's Trusted Boundary and Kernel-Checked Lean `v4.34.1` Soundness:** At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` currently models monomorphized post-cleanup MIR and fails closed (`.unsupported`) on `TyKind::Array`, `Rvalue::Repeat`, and unevaluated constants, while `trusted/rustc-capture/src/driver.rs` pins `1.98.0-nightly` and hooks `after_analysis` with `Compilation::Continue`. Extending capture to const-generic arrays and GCA items requires capturing **post-normalization monomorphized array lengths** (since generic MIR bodies retain unnormalized `<T as Tr>::SIZE` in `Rvalue::Repeat`), preserving fail-closed rejection of `generic_const_exprs` post-monomorphization `E0080` hazards, and rejecting cyclic const definitions. A standalone, axiom-clean (`0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`) Lean `v4.34.1` formalization (`support/GcaTrivialConstNormalizationSoundness.lean`) mechanizes solver downgrade, acyclic `TrivialConst` termination and total monomorphization (`acyclicTrivialConst_norm_total_no_post_mono_fault`), definitional GCA projection normalization (`gca_assoc_const_unifies_with_literal`), and all three constructive sharpness counterexamples (`ce1`, `ce2`, `ce3`).

## Applicability

This report characterizes the exact relationship across five pinned, durable upstream subjects recorded in `REPORT.json`:

1. **`rust-lang/rust` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`main`, `2026-11-22`):** Primary compiler source authority for the post-`1.100.0` GCA feature gates, `core::gca!` built-in macro expansion, AST-to-HIR direct const lowering, `const_of_item`, `rustc_next_trait_solver` const projection/free/inherent/anon normalization, `TyCtxt::next_trait_solver_globally` automatic GCE downgrade, `trivial_const` cycle mechanics, and legacy GCE `ConstEquate` / `Relate for ty::Expr` / `is_const_evaluatable`.
2. **`rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`, LLVM `23.1.5`):** Empirical post-`1.100.0` toolchain executing the four-part GCA vs. GCE differential probe (`support/capture_1_102_0_nightly_gca_vs_gce.json`) under both native codegen and Miri. Source cross-check of `removed.rs`, `unstable.rs`, and `ty/context.rs` confirms identical feature removal (`1.100.0`) and `next_trait_solver_globally` downgrade logic between `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`.
3. **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly` + `miri 0.1.0`, `2026-05-31`, LLVM `22.1.6`):** Live pre-`1.100.0` toolchain executed directly on `x86_64-unknown-linux-gnu` via `support/probe_gca_const_items_vs_gce.py` (`support/probe_1_98_0_nightly_results.json`), documenting the exact pre-rename `min_generic_const_args` / `generic_const_args` (`type const`) regime, its incompatibility with plain `const` items in array types, its hard error + `E0275` overflow when combining `-Znext-solver=globally` with `generic_const_exprs`, live Miri execution under both Stacked Borrows and Tree Borrows (`-Zmiri-tree-borrows`), generic vs. monomorphized `--emit=mir` inspection, and identical GCE `E0308` / `E0080` and plain-const `E0391` behaviors.
4. **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`):** Target verified-Rust framework whose capture driver (`trusted/rustc-capture/src/driver.rs`) and trusted MIR AST (`trusted/lean/Trusted/MirAst.lean`) define the TCB boundary against which GCA/GCE normalization and monomorphization semantics are evaluated.
5. **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):** Kernel proof checker used to verify `support/GcaTrivialConstNormalizationSoundness.lean` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

### Version Scope Matrix (Shared vs. Divergent Behaviors)

| Behavior / Compiler Mechanism | `1.98.0-nightly` (`14210df0e2`) | `1.102.0-nightly` (`3ef0c22cdb`) & `main` (`342d74463a`) |
| :--- | :--- | :--- |
| Default `-Znext-solver` on nightly | `Coherence` (opt-in `-Znext-solver=globally`) | `Globally` (via `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY`, `#160895`) |
| `#![feature(min_generic_const_args)]` | Active incomplete feature (`#132980`) | **Removed in `1.100.0`** (`E0557`, renamed to `gca_min_const_items`) |
| `#![feature(generic_const_args)]` | Active incomplete feature (`#151972`); hard-errors without `-Znext-solver=globally` | **Removed in `1.100.0`** (`E0557`, renamed to `gca_const_items`; requires `gca_min_const_items` and `-Znext-solver=globally`) |
| Direct const item syntax | `type const` keyword; breaks plain `const N: usize = 3; [u8; N]` | `core::gca!(...)` macro (`#[rustc_always_gca]` on trait decls); **preserves plain `const` in `[u8; N]`** |
| Generic arithmetic inside direct const (`T::N + 1`) | Rejected at definition site (`complex const arguments must be placed inside of a const block`) | Rejected at definition site (`complex const arguments must be placed inside of a const block`) |
| `#![feature(generic_const_exprs)]` + `-Znext-solver=globally` | Hard error (`incompatible`) + 12 `E0275` WF overflow errors | Automatic silent downgrade in `TyCtxt::next_trait_solver_globally()` to `Coherence` + `#160895` warning |
| GCE `N + 1` vs. `1 + N` (`[u8; N + 1]` -> `[u8; 1 + N]`) | Rejected with `E0308` (positional `Relate for ty::Expr`) | Rejected with `E0308` (identical legacy solver path after downgrade) |
| GCE `N - 1` uncalled def vs. `N = 0` call site | Uncalled def compiles (`rc = 0`); `sub_one::<0>()` fails `E0080` | Uncalled def compiles (`rc = 0`, warning only); `sub_one::<0>()` fails `E0080` |
| Plain cyclic `const A: usize = B; const B: usize = A;` | Rejected with `E0391` via `trivial_const` -> `mir_built` 4-hop cycle | Rejected with `E0391` via identical `trivial_const` -> `mir_built` 4-hop cycle |

### Scope Caveats

- All GCA (`gca_min_const_items`, `gca_const_items`, `gca_adts`, `gca_macroless_args`, `gca_macroless_items`) and GCE (`generic_const_exprs`) features are marked `incomplete` in `compiler/rustc_feature/src/unstable.rs` and require nightly toolchains. None of these features are stabilized on stable Rust (`1.99.x` or `1.100.x` stable channels).
- Applicability to `joshlf/anneal` concerns both the current `1.98.0-nightly` capture boundary (`trusted/rustc-capture/src/driver.rs:25`) and planned upgrades to post-`1.100.0` nightlies where `-Znext-solver=globally` is the default.
- The Lean `v4.34.1` mechanization models the abstract type-level const normalization, trivial-const dependency graph, solver downgrade predicate, and GCE structural equality / checked-subtraction semantics; it does not import `rustc`'s Rust source or `joshlf/anneal`'s `Trusted.MirSemantics` directly (see **Boundaries**).

## Findings

### 1. The `1.100.0` Feature Rename (`E0557`), `core::gca!(...)` Macro Architecture, and Plain-`const` Backwards Compatibility

Basis: source + documentation + execution

#### 1.1 Removal of Pre-`1.100.0` MGCA/GCA Feature Gates

In `rust-lang/rust` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1` and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), `compiler/rustc_feature/src/removed.rs` records the `1.100.0` renaming of the entire GCA feature family (in addition to the earlier `1.94.0` merge of `associated_const_equality`):

```rust
// compiler/rustc_feature/src/removed.rs (rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1)
// lines 65-66:
(removed, associated_const_equality, "1.94.0", Some(92827),
 Some("merged into `gca_min_const_items`")),
// line 170:
(removed, generic_const_args, "1.100.0", Some(151972), Some("renamed to `gca_const_items`")),
// lines 196-197:
(removed, macroless_const_item_generic_const_args, "1.100.0", Some(162540), Some("renamed to `gca_macroless_items`")),
(removed, macroless_generic_const_args, "1.100.0", Some(159006), Some("renamed to `gca_macroless_args`")),
// line 201:
(removed, min_generic_const_args, "1.100.0", Some(132980), Some("renamed to `gca_min_const_items`")),
```

On `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), compiling `#![feature(min_generic_const_args)]` fails immediately with `E0557`:

```text
error[E0557]: feature has been removed
  = note: removed in 1.100.0
  = note: renamed to `gca_min_const_items`
```

By contrast, in `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `compiler/rustc_feature/src/unstable.rs:568,628,634,860` still declared `generic_const_args`, `mgca_type_const_syntax`, and `min_generic_const_args` (with `DEPENDENT_FEATURES = &[(sym::generic_const_args, &[sym::min_generic_const_args]), ...]`), and probing `#![feature(gca_min_const_items)]` on `1.98.0-nightly` emits `error[E0635]: unknown feature gca_min_const_items`.

#### 1.2 Post-`1.100.0` GCA Feature Lattice and Dependency Constraints

In `compiler/rustc_feature/src/unstable.rs` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), the active GCA feature family forms an explicit dependency lattice:

| Feature Gate | Status / Since / Issue | Required Dependencies (`DEPENDENT_FEATURES`, lines `891-912`) | Semantic Role |
| :--- | :--- | :--- | :--- |
| `gca_min_const_items` | `incomplete`, `1.84.0`, `#132980` | None (also subsumes `associated_const_equality` in `feature_gate.rs:513-515`) | Direct const items via `core::gca!(...)`, paths to direct const items, and primitive literals |
| `gca_const_items` | `incomplete`, `1.95.0`, `#151972` | `gca_min_const_items` **and** `-Znext-solver=globally` (`feature_gate.rs:763-783`) | Generics in const items with definitional equality & rigid fallback (`IsRigid::Yes`) when `TooGeneric` |
| `gca_adts` | `incomplete`, `1.101.0`, `#163420` | `min_adt_const_params` OR `adt_const_params` | Struct/tuple/array/constructor direct const arguments |
| `gca_macroless_args` | `incomplete`, `1.99.0`, `#159006` | `gca_min_const_items` | Elides `core::gca!(...)` in const generic argument positions |
| `gca_macroless_items` | `incomplete`, `1.100.0`, `#162540` | `gca_min_const_items` | Elides `core::gca!(...)` on const item right-hand sides |
| `function_arg_const_generics` | `incomplete`, `1.101.0`, `#163261` | `gca_min_const_items` OR `gca_adts` | Allows function arguments to be const generics |

Note `Features::gca(&self)` (`compiler/rustc_feature/src/unstable.rs:126-128`):

```rust
pub fn gca(&self) -> bool {
    self.gca_min_const_items() || self.gca_adts()
}
```

#### 1.3 `core::gca!(...)` Built-In Macro Expansion and AST-to-HIR Lowering

Unlike the pre-`1.100.0` `type const` keyword syntax, post-`1.100.0` `rustc` exposes a built-in compiler macro in `library/core/src/marker.rs:1088-1097` (re-exported at `library/std/src/lib.rs:761-762` as `pub use core::gca;`):

```rust
#[rustc_builtin_macro(gca)]
#[unstable(feature = "gca_min_const_items", issue = "132980", implied_by = "gca_adts")]
#[macro_export]
macro_rules! gca {
    ($($arg:tt)*) => {
        /* compiler built-in */
    };
}
```

The expander is registered at `compiler/rustc_builtin_macros/src/lib.rs:90` (`gca: gca::expand`) and implemented in `compiler/rustc_builtin_macros/src/gca.rs:8-26`:

```rust
pub(crate) fn expand<'cx>(
    cx: &'cx mut ExtCtxt<'_>,
    span: Span,
    tts: TokenStream,
) -> MacroExpanderResult<'cx> {
    let ExpandResult::Ready(expr) = get_single_expr_from_tts(cx, span, tts, "gca!") else {
        return ExpandResult::Retry(());
    };
    let expr = match expr {
        Ok(expr) => expr,
        Err(err) => return ExpandResult::Ready(DummyResult::any(span, err)),
    };

    ExpandResult::Ready(Box::new(base::MacEager {
        expr: Some(cx.expr(span, ast::ExprKind::GcaMacro(expr.clone()))),
        ty: Some(cx.ty(span, ast::TyKind::GcaMacro(expr))),
        ..Default::default()
    }))
}
```

Returning both `expr: Some(ExprKind::GcaMacro(...))` and `ty: Some(TyKind::GcaMacro(...))` allows `core::gca!(...)` to parse uniformly in array-length / const-item RHS expression positions and in generic-argument positions (where rustc initially parses ambiguous type/const arguments as `ast::Ty`).

During AST-to-HIR lowering (`compiler/rustc_ast_lowering/src/lib.rs:1466-1481, 2754-2893`):
- **Const item RHS (`lower_const_item_rhs`, lines `2754-2775`):** When `gca_min_const_items()` is active and the RHS satisfies `can_lower_expr_to_const_arg_direct(body, context)` (where `context` is `DirectConstArgContext::GCA_MACRO` unless `gca_macroless_items()` is enabled), the item lowers to `hir::ConstItemRhs::Direct(const_arg)`. Otherwise — including for every ordinary `const PLAIN: usize = 3;` without `core::gca!(...)` — it lowers to `hir::ConstItemRhs::Body(body_id)`.
- **Direct representability gate (`can_lower_expr_to_const_arg_direct`, lines `2827-2893`):** Admits only:
  - `ExprKind::Path` (paths to const params, free/assoc consts, or const ctors depending on `DirectConstArgContext` flags),
  - `ExprKind::Lit` and negated literals (`UnOp::Neg`),
  - `ExprKind::ConstBlock` (`const { ... }`, which lowers to an opaque `AnonConst` checked without generics),
  - `ExprKind::Underscore`, `ExprKind::Paren`, single-expr `ExprKind::Block`,
  - Under `gca_adts`: `Call` (tuple ctor), `Tup`, `Struct`, `Array`.
  - **Every other expression — specifically binary arithmetic like `T::N + 1` — hits the wildcard arm `_ => Err(UnrepresentableConstArgError::new(expr))` (line `2891`)**, whose `emit` method (`lines 3478-3485`) emits:
    `"complex const arguments must be placed inside of a const block"`.
- **Why plain `const` compatibility was restored in `1.100.0`:** In `1.98.0-nightly`, `min_generic_const_args` globally switched path resolution in type-level const arguments to require `type const` on every referenced constant, breaking `pub const PLAIN: usize = 3; pub fn f() -> [u8; PLAIN]` (`rc = 1` in `probe_1_98_0_nightly_results.json`, `error: use of const in the type system not defined as type const`). Under post-`1.100.0` GCA, plain `const PLAIN: usize = 3` in `[u8; PLAIN]` (without `core::gca!`) continues to lower through the stable `AnonConstKind::MCG` path (`rc = 0` in `capture_1_102_0_nightly_gca_vs_gce.json`), while bare generic associated constants `[u8; T::N]` without `core::gca!` fall into `ForbidParamUsesFolder::error` (`compiler/rustc_hir_analysis/src/hir_ty_lowering/mod.rs:420-455`) and emit:
  - `error: generic parameters may not be used in const operations`
  - `help: add #![feature(gca_const_items)] and wrap the expression in the gca! macro` (when `gca_min_const_items` is enabled without `gca_const_items`).

---

### 2. Definitional Type-Level Normalization Under Default `-Znext-solver=globally`

Basis: source + execution + derived

#### 2.1 `const_of_item`, `ConstKind::Alias`, and `wfcheck::check_const_item`

In `compiler/rustc_type_ir/src/const_kind.rs:21-49, 108-149`, type-level constants are unified under `ConstKind::Alias(ty::IsRigid, ty::AliasConst<I>)` with five `AliasConstKind` variants:
- `Projection { def_id }` (`<Self as Trait>::AssocConst`),
- `InherentSelf { def_id }` and `InherentImpl { def_id }` (inherent associated consts, converting Self-form args to Impl-form args so impl-header constraints are preserved),
- `Free { def_id }` (module-level `const` items),
- `Anon { def_id }` (anonymous constants, classified by `AnonConstKind::{GCE, MCG, RepeatExprCount, NonTypeSystemAnon, NonTypeSystemInline}`, lines `294-306`).

The query `const_of_item` (`compiler/rustc_hir_analysis/src/collect.rs:1844-1879`) bridges HIR direct const items to type-level normalization:

```rust
fn const_of_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<ty::EarlyBinder<'tcx, Const<'tcx>>> {
    let ct_rhs = /* ItemKind::Const | TraitItemKind::Const | ImplItemKind::Const */;
    let ct_arg = match ct_rhs {
        hir::ConstItemRhs::Direct(ct_arg) => ct_arg,
        hir::ConstItemRhs::Body(_) => return None,
    };
    let icx = ItemCtxt::new(tcx, def_id);
    let identity_args = ty::GenericArgs::identity_for_item(tcx, def_id);
    let ct = icx.lowerer().lower_const_arg(
        ct_arg,
        tcx.type_of(def_id.to_def_id()).instantiate(tcx, identity_args).skip_norm_wip(),
    );
    ...
}
```

At item well-formedness checking (`compiler/rustc_hir_analysis/src/check/wfcheck.rs:1296-1348`, `check_const_item`), every direct const item (`tcx.is_direct_const(def_id)`) is checked for:
1. `item_ty: ConstParamTy` (unless `const_param_ty_unchecked` is enabled, lines `1307-1318`);
2. No generic parameters in `item_ty` unless `generic_const_parameter_types` is enabled (lines `1323-1325`);
3. Deep normalization of `const_of_item(def_id)` and a `ClauseKind::ConstArgHasType(norm_ct, item_ty)` obligation (lines `1328-1343`).

#### 2.2 Complete Next-Solver Normalization Dispatch (`normalizes_to.rs` & `project_goals/*.rs`)

When equating two constants under `-Znext-solver=globally`, `super_combine_consts` (`compiler/rustc_type_ir/src/relate/combine.rs:182-195`) never emits `PredicateKind::ConstEquate`; instead, any non-rigid `ConstKind::Alias(IsRigid::No, alias)` emits a `ty::ProjectionClause { projection_term: alias.into(), term }`. In `compiler/rustc_next_trait_solver/src/solve/project_goals/mod.rs:21-40`, `compute_projection_goal` dispatches across all four constant alias kinds:

| `AliasTermKind` | Next-Solver Handler & File | Direct (`const_of_item = Some(c)`) Path | Body (`const_of_item = None`) Path |
| :--- | :--- | :--- | :--- |
| `ProjectionConst { def_id }` | `normalizes_to.rs:464-486` (via `normalize_associated_term`) | Instantiates `c` with `target_args`, recursively calls `ecx.normalize(goal.param_env, c)`, pushes `ConstArgHasType` (`lines 95-148`) | Calls `ecx.evaluate_const(param_env, goal.predicate.alias, goal.predicate.term, alias_const)` |
| `FreeConst { def_id }` | `project_goals/free_alias.rs:36-53` | Instantiates `free` with `free_alias.args`, calls `self.normalize`, pushes `ConstArgHasType` | Calls `self.evaluate_const(...)` |
| `InherentConstSelf` / `InherentConstImpl` | `project_goals/inherent.rs:47-69` | Rebases Self-form to Impl-form (`convert_inherent_self_to_impl`), instantiates `inherent`, calls `self.normalize`, pushes `ConstArgHasType` | Calls `self.evaluate_const(...)` with `InherentConstImpl` as rigid identity |
| `AnonConst { def_id }` | `project_goals/anon_const.rs:14-25` | N/A (anon consts have bodies, not `const_of_item`) | Always calls `self.evaluate_const(...)` |

Inside `EvalCtxt::evaluate_const` (`compiler/rustc_next_trait_solver/src/solve/eval_ctxt/mod.rs:1554-1695`):
- If `alias_const.args` contains any non-region generic parameter, placeholder, or inference variable (excluding `AnonConstKind::RepeatExprCount` back-compat), CTFE is skipped and `Err(ty::ConstEvalErr::TooGeneric)` is produced (`lines 1631-1635`).
- If concrete (no params/placeholders/infers), it runs `cx.const_eval_resolve_for_typeck(TypingEnv::fully_monomorphized(), erased_alias_const, span)` -> `ConstKind::Value(ValueConst::new(ty, val))` (`lines 1639-1660`).
- **Crucial GCA Rule (`lines 1677-1695`):** When `evaluated_const` is `None` (`TooGeneric`) and `cx.features().gca_const_items()` is enabled:
  - If `alias_const.has_non_region_infer()`, returns `Certainty::AMBIGUOUS`;
  - Otherwise, instantiates `expected_term` to **`projection_term.to_term(cx, ty::IsRigid::Yes)` with `Certainty::Yes`** — treating the generic const alias as an **opaque rigid term** with definitional equality (reflexive equality `<T as Tr>::SIZE == <T as Tr>::SIZE` without evaluating the body!).
- **Why NO `where [(); ...]:` bound is needed:** In `compiler/rustc_trait_selection/src/traits/const_evaluatable.rs:89-94`, the `else if tcx.features().gca()` branch returns `Ok(())` without querying `param_env.caller_bounds()` for `ClauseKind::ConstEvaluatable`, and in `compiler/rustc_next_trait_solver/src/solve/mod.rs:213-233`, `compute_const_evaluatable_goal` accepts any `ConstKind::Alias(IsRigid::Yes, _)` with `Certainty::Yes` and normalizes `IsRigid::No` directly via `self.normalize`.

#### 2.3 Why `gca_const_items` Requires `-Znext-solver=globally`

`compiler/rustc_ast_passes/src/feature_gate.rs:763-783` enforces:

```rust
fn check_features_requiring_new_solver(sess: &Session, features: &Features) {
    if sess.opts.unstable_opts.next_solver == NextSolverConfig::Globally {
        return;
    }
    // Require the new solver with GCA, because the old solver can't implement GCA correctly as it
    // does not support normalization obligations for free and inherent consts.
    if let Some(gca_span) = features
        .enabled_lang_features()
        .iter()
        .find(|feat| feat.gate_name == sym::gca_const_items)
        .map(|feat| feat.attr_sp)
    {
        sess.dcx().emit_err(diagnostics::MissingDependentFeatures {
            parent_span: gca_span,
            parent: sym::gca_const_items,
            missing: String::from("-Znext-solver=globally"),
        });
    }
}
```

This matches our live `1.98.0-nightly` observation (`probe_1_98_0_nightly_results.json`): compiling `#![feature(min_generic_const_args, generic_const_args)]` without `-Znext-solver=globally` exits `rc = 1` with `error: generic_const_args requires -Znext-solver=globally to be enabled`.

#### 2.4 Empirical Verification (Native Execution, Miri, and MIR Inspection)

- **Post-`1.100.0` (`rustc 1.102.0-nightly`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `support/capture_1_102_0_nightly_gca_vs_gce.json`):** `part_a_gca_const_items_definitional_normalization` compiles cleanly under default `-Znext-solver=globally` (`compile_rc = 0`, empty `stderr`), executes natively (`native_rc = 0`, `EXACT_LEN=4 FIRST=7 GLOBAL_LEN=5`), and executes identically under Miri (`miri_rc = 0`, `EXACT_LEN=4 FIRST=7 GLOBAL_LEN=5`) without any `where [(); ...]:` bound.
- **Pre-`1.100.0` (`rustc 1.98.0-nightly`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `support/probe_1_98_0_nightly_results.json`):** Under explicit `-Znext-solver=globally`, the `type const` equivalent compiles cleanly (`rc = 0`), prints `EXACT_LEN=4 FIRST=7 GLOBAL_LEN=5` natively (`native_rc = 0`), passes live `miri 0.1.0` under both Stacked Borrows (`rc = 0`) and Tree Borrows (`-Zmiri-tree-borrows`, `rc = 0`), and fails on a mutated-value negative canary (`rc = 1`).
- **MIR Representation (`--emit=mir`, `probe_1_98_0_nightly_results.json`):** Inspecting emitted MIR reveals a critical structural seam for verification tools:
  ```text
  fn make_buf(_1: u8) -> [u8; <T as Tr>::SIZE] {
      let mut _0: [u8; <T as Tr>::SIZE];
      ...
      _0 = [copy _1; <T as Tr>::SIZE];
  }
  // In monomorphized caller `main`:
  let _1: [u8; 4];
  let _2: [u8; 5];
  _1 = make_buf::<Four>(const 7_u8) -> [return: bb1, unwind continue];
  ```
  Generic un-monomorphized MIR preserves the unnormalized projection `<T as Tr>::SIZE` in both local declarations (`[u8; <T as Tr>::SIZE]`) and `Rvalue::Repeat(Operand, ty::Const)`, whereas concrete caller sites normalize `<Four as Tr>::SIZE` to `4` and `GLOBAL` to `5` before MIR codegen/monomorphization.

---

### 3. Contrast With `generic_const_exprs`: `#160895` Solver Downgrade, `E0308` Non-Commutativity, and Deferred Post-Instantiation `E0080`

Basis: source + execution + derived

#### 3.1 Automatic `-Znext-solver=globally` -> `-Znext-solver=coherence` Downgrade (`#160895`)

In `compiler/rustc_session/src/config.rs:1071-1086` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), nightly builds compile with `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY`, making `NextSolverConfig::default() == NextSolverConfig::Globally`. However, `rustc_next_trait_solver` explicitly panics on GCE constructs:
- `eval_ctxt/mod.rs:1071-1073`: `ty::PredicateKind::ConstEquate(_, _) => panic!("ConstEquate should not be emitted when -Znext-solver is active")`
- `solve/mod.rs:237-238` & `solve/mod.rs:259-261`: `ty::ConstKind::Expr(_) => unimplemented!("feature(generic_const_exprs) is not supported in the new trait solver")`

To avoid crashing nightly crates using `#![feature(generic_const_exprs)]` once `-Znext-solver=globally` became the nightly default, `rustc` implements a two-part automatic downgrade:

1. **Silent effective solver switch (`compiler/rustc_middle/src/ty/context.rs:3150-3154`, identical at `3ef0c22cdb` lines `2897-2901`):**
   ```rust
   pub fn next_trait_solver_globally(self) -> bool {
       self.sess.opts.unstable_opts.next_solver == NextSolverConfig::Globally
           && !self.sess.opts.unstable_opts.higher_ranked_assumptions
           && !self.features().generic_const_exprs()
   }
   ```
   Notice that `sess.opts.unstable_opts.next_solver` itself remains `NextSolverConfig::Globally`, while `TyCtxt::next_trait_solver_globally()` returns `false` across the entire crate (also disabling `use_typing_mode_post_typeck_through_borrowck()`, line `3174`).
2. **Diagnostic emission (`compiler/rustc_ast_passes/src/feature_gate.rs:735-751` & `diagnostics.rs:41-50`):** `warn_next_solver_and_gce` emits `NextSolverDisabledForGenericConstExprs` citing `#160895`:
   ```text
   warning: `feature(generic_const_exprs)` is not supported with the next-generation trait solver
     = note: `-Znext-solver=globally` is currently enabled by default for testing
     = note: reverted the setting to `-Znext-solver=coherence` for this crate
     = note: the currently stable trait solver will be used for this crate
     = note: see issues #160895 <https://github.com/rust-lang/rust/issues/160895> for more information
   ```

**Pre-`#160895` empirical contrast (`1.98.0-nightly`, `14210df0e2`):** In `1.98.0-nightly`, `TyCtxt::next_trait_solver_globally()` (`context.rs:2675-2677`) simply returned `self.sess.opts.unstable_opts.next_solver.globally` without checking `generic_const_exprs()`. Running `rustc -Znext-solver=globally` on a GCE crate in `1.98.0-nightly` (`probe_1_98_0_nightly_results.json`, `gce_noncomm_explicit_next_solver_globally`) fails with `error: -Znext-solver=globally and generic_const_exprs are incompatible, using them at the same time is not allowed` followed by **12 `error[E0275]: overflow evaluating whether [(); N + 1] is well-formed` errors**.

**Derived consequence for mixed crates:** Because `check_features_requiring_new_solver` (`feature_gate.rs:764`) inspects `sess.opts.unstable_opts.next_solver` while `TyCtxt::next_trait_solver_globally()` returns `false` whenever `generic_const_exprs()` is enabled, enabling `generic_const_exprs` in any crate strips `-Znext-solver=globally` from the entire crate — making GCE fundamentally incompatible with any feature or trait-solving behavior that depends on `next_trait_solver_globally()`, including `gca_const_items`.

#### 3.2 Positional `AbstractConst` / `AnonConst` Unification Failure (`N + 1` vs. `1 + N`, `E0308`)

Under `generic_const_exprs` (executing in the legacy trait solver after downgrade), array lengths `[u8; N + 1]` and `[u8; 1 + N]` lower to two distinct `AnonConst` `DefId`s (`AliasConstKind::Anon { def_id }`). Equating them proceeds through four source locations:

1. `super_combine_consts` (`compiler/rustc_type_ir/src/relate/combine.rs:207-213`): because `infcx.next_trait_solver()` is `false` and `generic_const_exprs()` is `true`, emits `ty::PredicateKind::ConstEquate(a, b)`.
2. `fulfill.rs:706-762` (`compiler/rustc_trait_selection/src/traits/fulfill.rs`): expands both constants via `tcx.expand_abstract_consts(c1)` and `tcx.expand_abstract_consts(c2)` (`compiler/rustc_middle/src/ty/abstract_const.rs:37-79`), which queries `thir_abstract_const(def_id)` to turn each `AnonConst` into `ty::ConstKind::Expr(ty::Expr)`.
3. `ty::Expr::new_binop` (`compiler/rustc_middle/src/ty/consts/kind.rs:33-46`): stores binary operators as an **ordered** 4-element `GenericArgs` slice `[lhs_ty, rhs_ty, lhs_ct, rhs_ct]`. Thus `N + 1` becomes `Expr { kind: Binop(Add), args: [usize, usize, Param(N), Value(1)] }`, whereas `1 + N` becomes `Expr { kind: Binop(Add), args: [usize, usize, Value(1), Param(N)] }`.
4. `impl Relate for ty::Expr` (`compiler/rustc_middle/src/ty/relate.rs:101-124`):
   ```rust
   match (ae.kind, be.kind) {
       (ty::ExprKind::Binop(a_binop), ty::ExprKind::Binop(b_binop)) if a_binop == b_binop => {}
       ...
       _ => return Err(TypeError::Mismatch),
   }
   let args = relation.relate(ae.args(), be.args())?;
   Ok(ty::Expr::new(ae.kind, args))
   ```
   `relation.relate(ae.args(), be.args())` unifies element-by-element (`relate_args_invariantly`). At index 2 it compares `Param(N)` against `Value(1)` and fails with `TypeError::ConstMismatch`. Because neither `N + 1` nor `1 + N` can evaluate concretely (`EvaluateConstErr::HasGenericsOrInfers`, `fulfill.rs:824-830`), fulfillment reports `E0308: mismatched types (expected 1 + N, found N + 1)`.

Both `1.98.0-nightly` and `1.102.0-nightly` confirm this empirically (`gce_same_order_n_plus_1_ok`: `rc = 0` for `[u8; N + 1] -> [u8; N + 1]`; `gce_noncomm_default_solver` / `gce_reverts_default_next_solver_and_fails_commutativity_e0308`: `rc = 1`, `E0308`).

#### 3.3 Syntactic `where [(); N - 1]:` Acceptance at Definition Site and Deferred Post-Instantiation `E0080`

In `compiler/rustc_trait_selection/src/traits/const_evaluatable.rs:26-88, 159-229`:
- At the definition site of `pub fn sub_one<const N: usize>() -> [u8; N - 1] where [(); N - 1]:`, `is_const_evaluatable` expands `N - 1` into `ConstKind::Expr(Binop(Sub), [usize, usize, Param(N), Value(1)])` and invokes `satisfied_from_param_env` (`lines 51-54`).
- `satisfied_from_param_env` walks `ClauseKind::ConstEvaluatable(ce)` clauses in `param_env.caller_bounds()` — which contains `[(); N - 1]:` — matches the subtree structurally via `ocx.eq(..., c, self.ct)`, and returns `Ok(())` **without checking whether `N - 1` is defined for all `N : usize`**!
- Consequently, the uncalled generic function compiles with **`rc = 0`** on both `1.98.0-nightly` (0 warnings) and `1.102.0-nightly` (`#160895` downgrade warning only).
- Only when a caller instantiates `sub_one::<0>()` does `is_const_evaluatable` (`lines 70-85`) / `try_evaluate_const` / CTFE evaluate `0_usize - 1_usize`, failing with **`E0080: attempt to compute 0_usize - 1_usize, which would overflow`** on both the where-bound anonymous constant (`sub_one::<0>::{constant#0}`) and the return-type anonymous constant (`sub_one::<0>::{constant#1}`).

This illustrates the core substitution-stability failure of `generic_const_exprs`: well-typed generic definitions can harbor latent compile-time arithmetic faults (`E0080`) that surface only upon concrete monomorphization, whereas GCA forbids arbitrary fallible expressions directly inside generic const arguments (requiring `const { ... }` blocks, which reject generic parameters via `ForbidParamUsesFolder` at `hir_ty_lowering/mod.rs:420-426`).

---

### 4. `is_trivial_const` Query Fast-Path and Deterministic 4-Hop `E0391` Cycle Detection

Basis: source + execution + derived

In `compiler/rustc_const_eval/src/const_eval/eval_queries.rs:371-388` (`eval_to_const_value_raw_provider`, whose query description at `compiler/rustc_middle/src/queries.rs:1389-1394` is `"simplifying constant for the type system {}"`) and `eval_queries.rs:468-473` (`eval_in_interpreter`), `rustc` short-circuits full CTFE whenever `tcx.trivial_const(def_id)` returns `Some((val, ty))`.

The query provider `trivial_const_provider` (`compiler/rustc_mir_transform/src/trivial_const.rs:46-124`) accepts a `Const`, `AssocConst`, or type-system `AnonConst` (excluding `AnonConstKind::NonTypeSystemInline`, bodies with impossible clauses, or opaque types) iff its `mir_built` body has:
- Exactly `1` basic block (`START_BLOCK`),
- Exactly `1` statement (`StatementKind::Assign((RETURN_PLACE, Rvalue::Use(Operand::Constant(c), _)))`),
- Terminator `TerminatorKind::Return`, and
- `c.const_` matching either:
  - `Const::Val(v, ty)` -> returns `Some((v, ty))` (base case: already computed, control flow cannot panic), OR
  - `Const::Unevaluated(UnevaluatedConst { def, args, .. }, _ty)` with `args.is_empty()` -> recursively queries `tcx.trivial_const(def)` (`lines 105-110`), OR
  - `Const::Ty(..)` or non-empty `args` -> returns `None` (`lines 104, 106-108`).

Crucially, `mir_built` (`compiler/rustc_mir_transform/src/lib.rs:395-408`) ALSO calls `trivial_const::trivial_const(tcx, def, || &body)` immediately after `tcx.build_mir_inner_impl(def)` to skip MIR lint passes for trivial constants:

```rust
fn mir_built(tcx: TyCtxt<'_>, def: LocalDefId) -> &Steal<Body<'_>> {
    let mut body = tcx.build_mir_inner_impl(def);
    if trivial_const::trivial_const(tcx, def, || &body).is_some() {
        let body = tcx.alloc_steal_mir(body);
        pass_manager::dump_mir_for_phase_change(tcx, &body.borrow());
        return body;
    }
    ...
}
```

#### Exact 4-Hop Cycle Trace (`E0391`) vs. Direct GCA Cycle (`E0271`)

For `pub const A: usize = B; pub const B: usize = A; pub type Arr = [u8; A];`:
1. Type-level evaluation invokes `eval_to_const_value_raw(A)` (`"simplifying constant for the type system A"`).
2. Line `377` of `eval_queries.rs` calls `tcx.trivial_const(A)` (`"checking if A is a trivial const"`, `queries.rs:2826-2827`).
3. `trivial_const_provider(A)` forces `tcx.mir_built(A)` (`"building MIR for A"`).
4. `mir_built(A)` builds `{ _0 = const B; return; }` and calls `trivial_const::trivial_const(tcx, A, || &body)`, which hits `Const::Unevaluated(B, [])` and queries `tcx.trivial_const(B)` (`"checking if B is a trivial const"`).
5. `trivial_const_provider(B)` forces `tcx.mir_built(B)` (`"building MIR for B"`), which calls `trivial_const` on `B`'s body and queries `tcx.trivial_const(A)` — completing the cycle and aborting with **`error[E0391]: cycle detected when checking if A is a trivial const`** (observed identically on both `1.98.0-nightly` and `1.102.0-nightly`).

**Important empirical divergence for direct `type const` / GCA cycles (`probe_1_98_0_nightly_results.json`, `part_d_cyclic_const_e0391.direct_gca_const_cycle`):** When the cycle is declared as direct type-level constants (`pub type const A: usize = B; pub type const B: usize = A;` in `1.98.0-nightly` under `-Znext-solver=globally`), evaluation bypasses `mir_built` / `trivial_const` completely and enters `rustc_next_trait_solver`'s `normalize_free_alias` (`project_goals/free_alias.rs:36-45`). There, the next-solver search graph breaks the coinductive/inductive normalization cycle with **`error[E0271]: type mismatch resolving B normalizes-to _`** and `error: the constant B is not of type usize` instead of `E0391`.

---

### 5. Implications for Anneal's Trusted Boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Basis: source + derived

Direct inspection of `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes four concrete trust-boundary contracts governing const-generic and GCA/GCE support:

1. **Current Fail-Closed Status in `Trusted.MirAst` (`trusted/lean/Trusted/MirAst.lean`):**
   - `MirTy` (`lines 308-321`) models monomorphized scalar/unit/never/fieldless-enum/tuple/ref/rawPtr types and explicitly routes `TyKind::Array(I::Ty, Const<I>)` to `.unsupported` (`FaultKind.unsupported`).
   - `ConstLit` (`lines 492-506`) accepts only evaluated `ConstValue::Scalar(Scalar::Int)` and `ConstValue::ZeroSized`; `Rvalue::Repeat(Operand, ty::Const)` (`lines 568, 612`) lowers fail-closed to `Rvalue.unsupported`.
   - `Body` (`lines 815-867`) captures monomorphized `Runtime(PostCleanup)` MIR with explicit `pointerWidthBits = 64` and `mirProfileVersion = 1` (`lines 888-914`).
2. **Capture-Time Normalization Requirement (Why Generic MIR Cannot Cross the TCB Directly):**
   - As our `--emit=mir` probe confirmed, generic MIR for `make_buf<T: Tr>` retains `<T as Tr>::SIZE` unevaluated in both `LocalDecl` (`[u8; <T as Tr>::SIZE]`) and `Rvalue::Repeat([copy _1; <T as Tr>::SIZE])`.
   - Any future extension of `anneal-rustc-capture` and `Trusted.MirAst` to support `MirTy.array (elem : MirTy) (len : Nat)` and `Rvalue.repeat` MUST capture **post-normalization monomorphized instances** (`Instance::resolve` + `tcx.normalize_erasing_regions(TypingEnv::fully_monomorphized(), ...)`), extracting `ValTreeKind::Leaf(ScalarInt)` (`usize`) as a concrete `Nat` length and failing closed on any surviving `ConstKind::Alias`, `ConstKind::Param`, `ConstKind::Expr`, or `ValTreeCreationError`.
3. **Why `after_analysis` Alone Cannot Certify `generic_const_exprs` Crates (`trusted/rustc-capture/src/driver.rs:75-84, 131-147`):**
   - `AnalysisCallbacks::after_analysis` records `self.analysis_reached = tcx.dcx().has_errors().is_none()` and deliberately returns `Compilation::Continue` so that post-analysis/monomorphization errors abort `run_compiler` before `anneal-rustc-capture` reports success.
   - Under `generic_const_exprs`, an uncalled library function `pub fn sub_one<const N: usize>() -> [u8; N - 1] where [(); N - 1]:` passes `after_analysis` AND full library compilation (`rc = 0`) with zero errors, only to fail with `E0080` in a downstream caller instantiating `N = 0`. Moreover, enabling `generic_const_exprs` on post-`1.100.0` nightlies silently forces `TyCtxt::next_trait_solver_globally() == false`, altering trait resolution semantics across the entire crate. Therefore, a verified compiler capture boundary targeting post-`1.100.0` `rustc` should **prefer GCA (`gca_min_const_items` + `gca_const_items` + `-Znext-solver=globally`)** and **reject or explicitly quarantine crates enabling `#![feature(generic_const_exprs)]`** (checking `tcx.features().generic_const_exprs()` and `tcx.next_trait_solver_globally()` in the capture driver).
4. **Toolchain Pin Transition (`1.98.0-nightly` -> Post-`1.100.0`):**
   - `trusted/rustc-capture/src/driver.rs:25` currently pins `1.98.0-nightly`, where `-Znext-solver=coherence` is default and `min_generic_const_args` uses `type const`. When upgrading `anneal-rustc-capture` past `1.100.0`, test fixtures and capture assertions must migrate from `min_generic_const_args` / `generic_const_args` to `gca_min_const_items` / `gca_const_items` + `core::gca!(...)` and account for `NextSolverConfig::Globally` becoming the default.

---

### 6. Kernel-Checked Lean `v4.34.1` Mechanization (`support/GcaTrivialConstNormalizationSoundness.lean`)

Basis: source + execution + derived

The standalone, zero-import Lean `v4.34.1` module `support/GcaTrivialConstNormalizationSoundness.lean` (`758` lines, `33,262` bytes) formalizes the solver configuration gate, `is_trivial_const` DAG semantics and cycle detector, GCA definitional normalization under `-Znext-solver=globally`, and GCE positional `AbstractConst` / deferred-underflow semantics. Every recursive or dependent value definition carries an explicit `noncomputable def` modifier (matching Anneal's `Trusted.MirAst` TCB discipline) without `noncomputable section`, eliminating all compiler-generated `._unsafe_rec` helpers.

#### Mechanized Theorem Inventory and Kernel Axiom Audit

Verified via `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`lean_rc = 0`) plus a Lean `MetaM` environment audit over all `463` constants (`0` `._unsafe_rec`, `0` `partial`/`unsafe` definitions) and a source token audit (`0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `noncomputable section`):

| Theorem (`support/GcaTrivialConstNormalizationSoundness.lean`) | Line | Formal Claim | `#print axioms` |
| :--- | ---: | :--- | :--- |
| `gce_reverts_default_next_solver` | `75` | `cfg.genericConstExprs = true → effectiveSolverMode cfg = .oldCoherence` (mirrors `context.rs:3150-3154`) | `[propext]` |
| `gce_emits_warning_under_nightly_default` | `85` | `cliNextSolver = .globally ∧ genericConstExprs = true → emitsGceDowngradeWarning cfg = true` | `[propext]` |
| `gce_disables_effective_gca_const_items` | `93` | `cfg.genericConstExprs = true → gcaConstItemsEffectiveAllowed cfg = false` | `[propext]` |
| `gca_preserves_next_solver_globally` | `100` | Enabling `gca_min_const_items` without GCE or `-Zhigher-ranked-assumptions` keeps `.nextGlobally`, allows `gca_const_items`, and emits no downgrade warning | `[propext]` |
| `acyclicTrivialConst_norm_total_no_post_mono_fault` | `315` | For any rank-witnessed `AcyclicTrivialEnv env rank` and any `id`, `∃ v, ∀ fuel σ, rank id + 1 ≤ fuel → evalTrivialAtMono env σ fuel id = .ok v` (terminating, fuel-confluent, cycle-free, and invariant/total across all monomorphization substitutions `σ`) | `[Quot.sound]` |
| `gca_assoc_const_unifies_with_literal` | `481` | Under `.globally` + `gca_min_const_items` (no GCE, **no `where [(); ...]:` bounds**), `projDef c tr assoc = some (.lit n)` normalizes `[u8; core::gca!(<c as Tr>::ASSOC)]` to `[u8; n]` and unifies (`unifyGcaNormTy = true`) for all `fuel ≥ 2` | `[propext]` |
| `gca_chained_assoc_to_free_const_unifies_with_literal` | `524` | Multi-hop `<c as Tr>::ASSOC = core::gca!(FREE)` with `FREE = core::gca!(n)` unifies definitionally with `[u8; n]` for all `fuel ≥ 3` | `[propext]` |
| `gca_generic_proj_rigid_and_instantiation_sound` | `572` | Generic `<T as Tr>::ASSOC` normalizes to rigid `rigidProj` unifying with itself at definition site, and substituting `T ↦ concrete c` normalizes cleanly to `[u8; n]` | `[propext]` |
| `ce1_anonConst_defId_unification_rejects_commuted_add` | `695` | `N + 1` (`AnonDefId = 10`) and `1 + N` (`AnonDefId = 11`) satisfy `∀ n, evalGceChecked n eNPlus1 = evalGceChecked n e1PlusN` (via `Nat.add_comm`), yet `gceExprStructuralEq = false` and `gceAnonConstUnify tbl 10 11 = false` (`E0308`), while identical order `10` vs. `12` returns `true` | `[propext]` |
| `ce2_gce_unchecked_sub_passes_def_faults_at_zero_instantiation` | `717` | `N - 1` with `where [(); N - 1]:` passes `gceDefSiteEvaluatable = true`, faults at `N = 0` (`evalGceChecked 0 = .overflowErr`, `E0080`), and succeeds at `N = 1` (`.ok 0`) | `[propext]` |
| `ce3_cyclic_trivial_const_detected` | `729` | Mutual cycle `envAB` (`0 ↦ alias 1`, `1 ↦ alias 0`) yields `.cycleDetected` (`E0391`) from both entry points and admits `¬ ∃ rank, AcyclicTrivialEnv envAB rank` (by `Nat.lt_asymm`) | `[]` (no axioms) |

## Boundaries

### Not Examined
- **`gca_adts` (`#163420`), `gca_macroless_args` (`#159006`), `gca_macroless_items` (`#162540`), and `function_arg_const_generics` (`#163261`):** We verified their feature declarations and dependency edges in `compiler/rustc_feature/src/unstable.rs` and `removed.rs`, and inspected `DirectConstArgContext` flags in `compiler/rustc_ast_lowering/src/lib.rs`, but did not run an exhaustive execution matrix over struct/enum/array ADT const-arg constructors or macroless forms.
- **Inherent associated constants with lifetime-constrained `Self` headers (`InherentConstSelf` -> `InherentConstImpl`):** We inspected the next-solver implementation in `compiler/rustc_next_trait_solver/src/solve/project_goals/inherent.rs:47-118`, but did not empirically probe lifetime-equality side conditions during inherent const normalization.
- **Direct GCA mutual cycle (`const A: usize = core::gca!(B); const B: usize = core::gca!(A);`) on `1.102.0-nightly`:** We empirically observed `E0271` for `type const A = B; type const B = A;` under `-Znext-solver=globally` on `1.98.0-nightly`, and `E0391` for plain `const A = B; const B = A;` on both `1.98.0-nightly` and `1.102.0-nightly`; the exact diagnostic code (`E0271` vs. `E0275` vs. `E0391`) for a `core::gca!`-wrapped mutual cycle on `1.102.0-nightly` was not executed directly because the local host toolchain is `1.98.0-nightly`.
- **Interactions with `generic_const_parameter_types` (`#137626`), `generic_const_items` (`#113521`), and `const_trait_impl`:** Only their feature-gate cross-references in `wfcheck.rs:1323` and `unstable.rs` were inspected; multi-feature interactions were not empirically probed.
- **Full `std` `cargo miri` execution on `1.98.0-nightly`:** On the local offline `1.98.0-nightly` environment, `cargo miri` sysroot compilation for `std` was blocked by a vendored `cfg-if` lock mismatch (`1.0.4` locked vs. `1.0.5` vendored). Live Miri execution on `1.98.0-nightly` was therefore conducted directly via the `miri` driver on a self-contained `#![no_core]` harness under both Stacked Borrows and Tree Borrows, complemented by the full-`std` `1.102.0-nightly` Miri capture (`EXACT_LEN=4 FIRST=7 GLOBAL_LEN=5`).

### Unknown
- **Future algebraic equivalence in GCA (`#151972` Unresolved Questions):** Issue `#151972` explicitly leaves open whether future GCA revisions will introduce semantic/commutative equality without violating coherence, and how boundaries between opaque definitional equality and semantic equality will be specified. Because upstream design is still evolving, stability of opaque-vs.-semantic equality boundaries beyond `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` is unknown.
- **Removal timeline for `generic_const_exprs`:** Issue `#160895` states that `@rust-lang/project-const-generics` plans to remove `generic_const_exprs` once GCA covers its use cases, but no target Rust version for removal is specified in upstream source.

### Known Not to Apply
- **Arbitrary generic arithmetic inside `core::gca!(...)`:** Definitional normalization under `gca_min_const_items` + `gca_const_items` does **not** permit `core::gca!(T::N + 1)` directly as a const argument; `rustc_ast_lowering` rejects it at the definition site (`complex const arguments must be placed inside of a const block`), and placing generic parameters inside `const { T::N + 1 }` is likewise rejected by `ForbidParamUsesFolder`.
- **`trivial_const` optimization on generic constants or multi-block CTFE bodies:** `compiler/rustc_mir_transform/src/trivial_const.rs:79-112` explicitly returns `None` whenever `args` is non-empty, `basic_blocks.len() != 1`, `statements.len() != 1`, or `Const::Ty(..)` is encountered. Therefore, `acyclicTrivialConst_norm_total_no_post_mono_fault` applies strictly to parameterless single-block trivial constant chains and does **not** claim totality for arbitrary `const fn` CTFE bodies (which may panic, divide by zero, or overflow).
- **Combining `#![feature(generic_const_exprs)]` with `#![feature(gca_const_items)]` in a single crate:** Because `TyCtxt::next_trait_solver_globally()` returns `false` whenever `generic_const_exprs()` is enabled, the crate cannot execute under `-Znext-solver=globally` as required by `gca_const_items`.

### Unsupported
- **Using `generic_const_exprs` under `-Znext-solver=globally`:** Explicitly unsupported by upstream `rustc` (`solve/eval_ctxt/mod.rs:1072` panics on `ConstEquate`; `solve/mod.rs:237,260` `unimplemented!` on `ConstKind::Expr`; `#160895` forces automatic downgrade to `-Znext-solver=coherence`).
- **Using `gca_const_items` under the legacy trait solver (`-Znext-solver=coherence`):** Explicitly rejected by `check_features_requiring_new_solver` (`feature_gate.rs:763-783`) because the legacy trait solver lacks normalization obligations for free and inherent constants.
- **Capturing `[T; N]` array types or unevaluated const projections in current `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:** `Trusted.MirAst.MirTy` (`MirAst.lean:308-321`) and `Trusted.MirAst.Rvalue` (`MirAst.lean:612`) fail closed with `.unsupported`.

### Attractive Stronger Conclusions Not Established by the Evidence
- **Do not infer that GCA guarantees termination of all `rustc` const normalization:** While acyclic `trivial_const` chains are total and `core::gca!(...)` prevents inline unchecked arithmetic, direct `const_of_item` aliases can still form cycles (caught by the next-solver search graph) or reference concrete `const { ... }` blocks whose CTFE can fail with `E0080` at definition time or concrete instantiation time if `const_eval_resolve_for_typeck` encounters overflow/panic.
- **Do not infer that `support/GcaTrivialConstNormalizationSoundness.lean` formally verifies `rustc`'s Rust source code or `Trusted.MirSemantics`:** The Lean formalization verifies a faithful abstract operational model of `rustc`'s solver-gate predicate, `trivial_const` traversal, GCA `DirectConstTable` normalization, and GCE positional unification / checked subtraction. Fidelity between the Lean model and `rustc`'s Rust implementation rests on direct line-by-line source inspection and differential execution probes, not on a mechanized translation of `rustc` itself.

## Evidence

### 1. Primary GitHub Sources (`rust-lang/rust`, `joshlf/anneal`, `leanprover/lean4`)

All commit SHAs were resolved live via authenticated GitHub API queries on `2026-11-22`:

- **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`main`, `2026-11-22`):**
  - `compiler/rustc_feature/src/removed.rs:65-66, 170, 196-197, 201` — `1.100.0` removal of `min_generic_const_args` (`#132980`), `generic_const_args` (`#151972`), `macroless_generic_const_args` (`#159006`), `macroless_const_item_generic_const_args` (`#162540`), and `1.94.0` merge of `associated_const_equality` (`#92827`).
  - `compiler/rustc_feature/src/unstable.rs:123-129, 563-584, 878-912` — `Features::gca()`, active `gca_*` and `generic_const_exprs` declarations, `DEPENDENT_FEATURES` (`gca_const_items -> gca_min_const_items`).
  - `library/core/src/marker.rs:1078-1097` and `library/std/src/lib.rs:761-762` — `#[rustc_builtin_macro(gca)] macro_rules! gca!` declaration and `std::gca` re-export.
  - `compiler/rustc_builtin_macros/src/lib.rs:43, 90` and `compiler/rustc_builtin_macros/src/gca.rs:8-26` — `gca::expand` producing `ast::ExprKind::GcaMacro` and `ast::TyKind::GcaMacro`.
  - `compiler/rustc_ast_lowering/src/lib.rs:1466-1481, 1785-1788, 2754-2893, 3453-3485` — `lower_const_item_rhs` (`hir::ConstItemRhs::Direct` vs. `Body`), `can_lower_expr_to_const_arg_direct`, and `UnrepresentableConstArgError::emit` (`"complex const arguments must be placed inside of a const block"`).
  - `compiler/rustc_hir_analysis/src/hir_ty_lowering/mod.rs:420-456, 2394-2560` — `ForbidParamUsesFolder::error` (emitting `gca!` migration help) and `lower_const_arg`.
  - `compiler/rustc_hir_analysis/src/collect.rs:1844-1879` — `const_of_item` returning `Some` exclusively for `hir::ConstItemRhs::Direct`.
  - `compiler/rustc_hir_analysis/src/check/wfcheck.rs:1296-1348` — `check_const_item` enforcing `ConstParamTy`, parameter-free const types, and `ConstArgHasType`.
  - `compiler/rustc_session/src/config.rs:1071-1086` and `compiler/rustc_session/src/options.rs:2796-2797` — `NextSolverConfig::{Coherence, Globally}` and `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY`.
  - `compiler/rustc_middle/src/ty/context.rs:3150-3154, 3265-3268` — `TyCtxt::next_trait_solver_globally` (`&& !self.features().generic_const_exprs()`) and `TyCtxt::is_trivial_const`.
  - `compiler/rustc_ast_passes/src/diagnostics.rs:41-59` and `compiler/rustc_ast_passes/src/feature_gate.rs:512-515, 735-783` — `NextSolverDisabledForGenericConstExprs` (`#160895`), `warn_next_solver_and_gce`, and `check_features_requiring_new_solver`.
  - `compiler/rustc_type_ir/src/const_kind.rs:21-49, 108-149, 238-252, 294-306` — `ConstKind`, `AliasConstKind`, `ValTreeKind`, `AnonConstKind`.
  - `compiler/rustc_type_ir/src/relate/combine.rs:143-217` — `super_combine_consts` emitting `ProjectionClause` under `next_trait_solver()` vs. `PredicateKind::ConstEquate` under `generic_const_exprs()`.
  - `compiler/rustc_next_trait_solver/src/solve/project_goals/mod.rs:21-40`, `anon_const.rs:14-25`, `free_alias.rs:18-62`, `inherent.rs:18-118`, `normalizes_to.rs:95-159, 458-492`, `eval_ctxt/mod.rs:1068-1076, 1554-1695`, `solve/mod.rs:213-269` — complete next-solver const normalization, rigid `IsRigid::Yes` fallback under `gca_const_items`, and panic/unimplemented guards on GCE `ConstEquate`/`ConstKind::Expr`.
  - `compiler/rustc_middle/src/ty/consts/kind.rs:13-60`, `compiler/rustc_middle/src/ty/abstract_const.rs:37-79`, `compiler/rustc_middle/src/ty/relate.rs:101-124`, `compiler/rustc_trait_selection/src/traits/const_evaluatable.rs:26-229`, `compiler/rustc_trait_selection/src/traits/fulfill.rs:706-830` — GCE `Expr` positional representation, `expand_abstract_consts`, positional `Relate for ty::Expr`, `is_const_evaluatable` / `satisfied_from_param_env`, and `ConstEquate` fulfillment.
  - `compiler/rustc_mir_transform/src/trivial_const.rs:46-124`, `compiler/rustc_mir_transform/src/lib.rs:395-408, 440, 468, 502`, `compiler/rustc_const_eval/src/const_eval/eval_queries.rs:146-159, 371-388, 468-474`, `compiler/rustc_middle/src/queries.rs:304-308, 1389-1397, 2826-2830`, `compiler/rustc_const_eval/src/const_eval/valtrees.rs:83-292` — `trivial_const` fast-path, `mir_built` cycle coupling, `eval_to_const_value_raw` query description, and `eval_to_valtree`.
  - Upstream tracking issues & docs: `rust-lang/rust#132980`, `rust-lang/rust#151972`, `rust-lang/rust#160895`; `src/doc/unstable-book/src/language-features/{gca-min-const-items,gca-const-items,gca-macroless-items,generic-const-exprs}.md`; `tests/ui/const-generics/gca/{require-next-solver,assoc-const}.rs`.
- **`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`):**
  - Cross-checked `compiler/rustc_feature/src/removed.rs:65-66, 170, 196-197, 201` and `compiler/rustc_middle/src/ty/context.rs:2897-2901` (`next_trait_solver_globally` matches `main` verbatim).
- **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`):**
  - Cross-checked `compiler/rustc_feature/src/unstable.rs:568, 628, 634, 859-862` (pre-rename `min_generic_const_args` + `generic_const_args` + `mgca_type_const_syntax`), `compiler/rustc_session/src/options.rs:2480`, and `compiler/rustc_middle/src/ty/context.rs:2675-2677` (`next_trait_solver_globally` without GCE downgrade).
- **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`):**
  - `trusted/rustc-capture/src/driver.rs:25, 75-84, 131-151` — pinned `1.98.0-nightly` compiler driver and `after_analysis` / `Compilation::Continue` contract.
  - `trusted/lean/Trusted/MirAst.lean:77-92, 308-321, 492-520, 562-628, 883-943` — `noncomputable` TCB declaration hygiene, fail-closed `.unsupported` handling of `TyKind::Array` / `Rvalue::Repeat` / non-scalar constants, and `pointerWidthBits = 64` / `mirProfileVersion = 1` capture invariants.
- **`leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):**
  - Standalone kernel binary verifying `support/GcaTrivialConstNormalizationSoundness.lean`.

### 2. Preserved Execution Artifacts and Empirical Observations

1. **`support/probe_gca_const_items_vs_gce.py`:** Self-contained Python 3 probe harness (standard library only, zero hardcoded results) that auto-detects post-`1.100.0` GCA vs. pre-`1.100.0` MGCA toolchains and runs all 4 probe parts (`part_a` through `part_d`) under real `rustc` and `miri`.
2. **`support/capture_1_102_0_nightly_gca_vs_gce.json` (observed `2026-11-21` on `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, `x86_64-unknown-linux-gnu`, LLVM `23.1.5`):**
   - `part_a`: `compile_rc = 0`, `native_rc = 0` (`EXACT_LEN=4 FIRST=7 GLOBAL_LEN=5`), `miri_rc = 0` (`EXACT_LEN=4 FIRST=7 GLOBAL_LEN=5`).
   - `part_b`: `min_generic_const_args` fails `rc = 1` with `E0557` (`removed in 1.100.0`, `renamed to gca_min_const_items`); plain `const` in `[u8; PLAIN]` compiles `rc = 0`; bare `T::N` fails `rc = 1` suggesting `gca_const_items` + `gca!`.
   - `part_c`: `core::gca!(T::N + 1)` fails `rc = 1` (`reverted_next_solver = false`, `complex const arguments must be placed inside of a const block`); all three GCE cases set `reverted_next_solver = true` with the `#160895` warning (`gce_noncomm`: `rc = 1`, `E0308`; `gce_n_minus_1_uncalled`: `rc = 0`; `gce_n_minus_1_called_at_0`: `rc = 1`, `E0080`).
   - `part_d`: `pub const A: usize = B; pub const B: usize = A;` fails `rc = 1` with `E0391` (`cycle detected when checking if A is a trivial const` -> `building MIR for A` -> `checking if B is a trivial const` -> `building MIR for B` -> `checking if A is a trivial const`).
3. **`support/probe_1_98_0_nightly_results.json` (observed `2026-11-22` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` + `miri 0.1.0 (14210df0e2 2026-05-31)`, `x86_64-unknown-linux-gnu`, LLVM `22.1.6`):**
   - `part_a`: compiles `rc = 0` with `-Znext-solver=globally`, native `rc = 0` (`EXACT_LEN=4 FIRST=7 GLOBAL_LEN=5`), live `miri` `#![no_core]` passes under Stacked Borrows (`rc = 0`) and Tree Borrows (`-Zmiri-tree-borrows`, `rc = 0`) with mutated-value negative canary failing (`rc = 1`), and `--emit=mir` captures `<T as Tr>::SIZE` in polymorphic `make_buf` vs. `[u8; 4]`/`[u8; 5]` in `main`. Without `-Znext-solver=globally`, `generic_const_args` fails `rc = 1` (`requires -Znext-solver=globally`).
   - `part_b`: `min_generic_const_args` compiles (`rc = 0`, incomplete warning); `gca_min_const_items` fails `E0635` (unknown feature); plain `const PLAIN: usize = 3; [u8; PLAIN]` fails `rc = 1` (`not defined as type const`); bare `T::N` fails `rc = 1` (`not defined as type const`).
   - `part_c`: `T::N + 1` rejected at definition site (`rc = 1`, `complex const arguments must be placed inside of a const block`); GCE `N + 1` -> `N + 1` passes (`rc = 0`); GCE `N + 1` -> `1 + N` fails `E0308` (`expected 1 + N, found N + 1`); GCE + explicit `-Znext-solver=globally` fails with incompatibility error + 12 `E0275` overflow errors; GCE uncalled `N - 1` passes (`rc = 0`); GCE `sub_one::<0>()` fails `E0080` on both `{constant#0}` and `{constant#1}`.
   - `part_d`: plain `const A = B; const B = A;` fails `E0391` via identical 4-hop `trivial_const` -> `mir_built` cycle; direct `type const A = B; type const B = A;` under `-Znext-solver=globally` fails `E0271` (`type mismatch resolving B normalizes-to _`).

### 3. Preserved Lean `v4.34.1` Formalization and Audit Receipt

- **`support/GcaTrivialConstNormalizationSoundness.lean`** (`758` lines, `33,262` bytes, verified `2026-11-22`):
  - Checked with `LEAN_SYSROOT=~/.elan/toolchains/leanprover--lean4---v4.34.1 lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/GcaTrivialConstNormalizationSoundness.lean` -> exit code `0`, `0` warnings, `0` errors.
  - `#print axioms` output across all 10 top-level theorems: strictly subsets of `{propext, Quot.sound}` (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`); `ce3_cyclic_trivial_const_detected` uses `[]` (zero axioms).
  - Lean `MetaM` environment audit across `463` constants in `GcaTrivialConstNormalizationSoundness`: `0` `._unsafe_rec` declarations, `0` `partial`/`unsafe` definitions.
  - Source token scan outside comments: `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `_unsafe_rec`, `0` `noncomputable section`.

## Revalidation

To cheaply verify whether these findings still hold on a newer `rustc` nightly, `joshlf/anneal` revision, or Lean `v4` toolchain:

### 1. Re-run the Dual-Regime `rustc` + `Miri` Probe

Run the preserved standalone probe script against any nightly `rustc` toolchain (automatically selects `gca_min_const_items` + `gca_const_items` + `core::gca!(...)` on `>= 1.100.0` nightlies or `min_generic_const_args` + `type const` on pre-`1.100.0` nightlies):

```bash
python3 support/probe_gca_const_items_vs_gce.py --out /tmp/gca_probe_reval.json
```

Check four discriminating invariants in `/tmp/gca_probe_reval.json`:
1. `part_a`: `compile.rc == 0`, `native_stdout == "EXACT_LEN=4 FIRST=7 GLOBAL_LEN=5"`, and Miri returns `rc == 0` (with negative canary `rc == 1`).
2. `part_b`: On `>= 1.100.0`, `min_generic_const_args_feature_check.rc == 1` (`E0557`) and `plain_const_in_array_ty.rc == 0`.
3. `part_c`: `gce_noncomm_default_solver.rc == 1` (`E0308`), `gce_n_minus_1_uncalled_def.rc == 0`, `gce_n_minus_1_called_at_0.rc == 1` (`E0080`), `gca_generic_arith_rejected_at_def.rc == 1`, and on `>= 1.100.0` `reverted_next_solver == true` on all GCE cases (flip to `false` or removal error if upstream removes `generic_const_exprs` or enables next-solver GCE support).
4. `part_d`: `plain_const_cycle_e0391.rc == 1` with `E0391` naming `is a trivial const`.

### 2. Diff Narrow Upstream Implementation Regions in `rust-lang/rust`

Inspect targeted diffs against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` in six small regions:
- `compiler/rustc_feature/src/{removed.rs,unstable.rs}` (feature renames, stabilizations, or removal of `generic_const_exprs`);
- `compiler/rustc_middle/src/ty/context.rs` (`TyCtxt::next_trait_solver_globally`) and `compiler/rustc_ast_passes/src/feature_gate.rs` (`warn_next_solver_and_gce`, `check_features_requiring_new_solver`);
- `compiler/rustc_builtin_macros/src/gca.rs` and `compiler/rustc_ast_lowering/src/lib.rs` (`can_lower_expr_to_const_arg_direct`, `lower_const_item_rhs`);
- `compiler/rustc_next_trait_solver/src/solve/{normalizes_to.rs,eval_ctxt/mod.rs,project_goals/free_alias.rs,project_goals/inherent.rs}` (`const_of_item` normalization and `IsRigid::Yes` fallback);
- `compiler/rustc_middle/src/ty/relate.rs` (`impl Relate for ty::Expr`) and `compiler/rustc_trait_selection/src/traits/{const_evaluatable.rs,fulfill.rs}` (GCE commutativity or definition-site checking changes);
- `compiler/rustc_mir_transform/src/{trivial_const.rs,lib.rs}` (`trivial_const` cycle path in `mir_built`).

### 3. Re-check the Anneal Capture Boundary

Diff `joshlf/anneal` against `c131b320eeeb26ef692e5afd5ec8db49ee518613` in:
- `trusted/rustc-capture/src/driver.rs` (`COMPILER_VERSION` and whether `after_analysis` checks `tcx.features().generic_const_exprs()` or extracts monomorphized array lengths);
- `trusted/lean/Trusted/MirAst.lean` (`MirTy`, `ConstLit`, and `Rvalue` for any admission of `TyKind::Array` or `Rvalue::Repeat`).

### 4. Re-verify the Kernel-Checked Lean `v4.34.1` Formalization

```bash
LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
  lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/GcaTrivialConstNormalizationSoundness.lean
```

Confirm exit code `0`, zero warnings, and that every `#print axioms` line reports only `does not depend on any axioms`, `[propext]`, or `[Quot.sound]` (never `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler`).
