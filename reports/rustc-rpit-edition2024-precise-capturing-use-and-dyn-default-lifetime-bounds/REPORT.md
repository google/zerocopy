# Edition 2021 vs. 2024 RPIT Lifetime Capturing, RFC 3617 `use<...>` Precise Capturing, and Trait-Object Default Lifetime Bounds

## Summary

This report establishes primary-source (`rust-lang/rust` HIR lowering, bound-variable resolution, well-formedness checking, and trait-object lowering), empirical (`rustc 1.98.0-nightly`), and kernel-checked (`Lean v4.34.1`) ground truth for three tightly coupled lifetime-resolution mechanisms in the Rust compiler frontend:

1. **Edition 2021 to 2024 RPIT Lifetime Capture Transition (`compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs`):** The predicate `opaque_captures_all_in_scope_lifetimes` governs whether a return-position `impl Trait` (RPIT) opaque type captures every in-scope lifetime parameter or only lifetimes referenced in its bounds. For free functions and inherent methods (`OpaqueTyOrigin::FnReturn { in_trait_or_impl: None }`) lacking a `use<...>` bound, `opaque.span.at_least_rust_2024()` flips the rule from `false` (Edition 2021) to `true` (Edition 2024), aligning free RPITs with trait/impl RPITIT (`in_trait_or_impl.is_some()`), `async fn`, and type-alias `impl Trait` (`TyAlias`), all of which already capture all in-scope lifetimes even in Edition 2021. Consequently, identical source `fn capture_check(x: &u32) -> impl Sized { let _ = x; 42u32 }` compiles and executes cleanly in Edition 2021 (`RPIT_OK=42`), whereas Edition 2024 rejects dropping `local` while holding the returned value with borrowck `E0597`.
2. **RFC 3498 / RFC 3617 `use<...>` Precise Capturing (`compiler/rustc_ast_lowering/src/lib.rs`, `resolve_bound_vars.rs`, `check/check.rs`, `hir_ty_lowering/bounds.rs`):** Whenever an opaque type carries `hir::GenericBound::Use(..)`, `opaque_captures_all_in_scope_lifetimes` unconditionally returns `false` across all editions and origins, restricting direct captured lifetimes to those visited inside `use<...>` (plus explicit item bounds). `hir_ty_lowering::lower_bounds` ignores `GenericBound::Use(..)` because precise capturing constrains the synthetic `OpaqueTy` generic argument list (`tcx.opaque_captured_lifetimes` / `generics_of`) rather than emitting trait or outlives clauses. In stabilized `rustc`, `check_opaque_precise_captures` rejects argument-position `impl Trait` (`NoPreciseCapturesOnApit`), requires lifetimes before non-lifetime parameters (`LifetimesMustBeFirst`), forbids duplicates (`DuplicatePreciseCapture`), forbids omitting lifetimes mentioned in explicit bounds (`LifetimeNotCaptured`), and currently requires **all** in-scope type and const parameters (including trait `Self`) to appear in `use<...>`. Crucially, listing `T` in `use<'a, T>` enables excluding `'b` (permitting callers to drop `'b`'s referent immediately) while still transitively capturing any lifetime `'c` nested inside `T` when instantiated with `&'c u32`.
3. **Default Trait-Object Lifetime Elision and Scope-Stack Shadowing (`resolve_bound_vars.rs`, `hir_ty_lowering/dyn_trait.rs`, `traits/wf.rs`):** Omitted trait-object lifetime bounds (`dyn Debug`, `Box<dyn Debug>`, `&'a Box<dyn Debug>`) lower via `elided_dyn_bound` to `hir::LifetimeKind::ImplicitObjectLifetimeDefault`, distinct from explicit `+ '_` (`LifetimeKind::Infer`, which uses ordinary function-signature elision). During bound-variable resolution, `TyKind::Ref` pushes `Scope::ObjectLifetimeDefault(Some('a))` (`&'a dyn Debug` -> `'a`), while generic path segments compute per-parameter defaults from `object_lifetime_default` (`Empty`, `Static`, `Param`, `Ambiguous`). Because `Box<T, A>` (`library/alloc/src/boxed.rs`) has no `T: 'r` outlives bound, `object_lifetime_default` returns `Empty`, and `compute_object_lifetime_defaults` maps `Empty` to `Some(ResolvedArg::StaticLifetime)` outside function bodies (or `None` inside `Scope::Body` for region inference). Walking scopes innermost-outward, `resolve_object_lifetime_default` hits `Box<T>`'s inner `'static` default before any outer `&'a` scope, **shadowing** `&'a` so `&'a Box<dyn Debug>` resolves to `&'a Box<dyn Debug + 'static>` (independent of `'a`). Furthermore, trait supertrait bounds (`trait BoundTrait<'a>: 'a`) override `ObjectLifetimeDefault` via `compute_object_lifetime_bound` / `traits::wf::object_region_bounds` **only** when `'a` is early-bound (`!r.has_escaping_bound_vars()`), falling back to `Box`'s `'static` default when `'a` is late-bound on a function signature.
4. **Mechanized Soundness and Anneal TCB Boundary (`support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean`, `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** All four core properties—Edition 2024 capture monotonicity and caller borrowck monotonicity, exact `use<S>` callee-caller borrow soundness, outer-wrapper `ObjectLifetimeDefault` shadowing determinism, and lifetime well-formedness preservation—are verified in Lean `v4.34.1` with zero `sorry`, zero `Classical.choice`, zero `._unsafe_rec`, and zero solver/reflection axioms. Meanwhile, direct inspection of `joshlf/anneal` confirms that Anneal compiles its own crates and `rustc-capture` driver with `--edition=2024`, while `Trusted.MirAst` maps `TyKind::Dynamic`, `OpaqueCast`, `StatementKind::AscribeUserType`, and non-fieldless ADTs (`Box<T, A>`) to `.unsupported` (`FaultKind.unsupported`), placing these frontend rules squarely inside `rustc`'s assumed TCB (`THREAT_MODEL.md`).

## Applicability

### Subject Relationships

This report synthesizes evidence across six durable upstream subjects pinned in `REPORT.json`:

1. **Upstream compiler primary source (`rust-lang/rust` @ `20fe935d50367c0ff8872c2ebfa050c5c99d9201`):** Direct inspection of `compiler/rustc_ast_lowering/src/lib.rs`, `compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs`, `compiler/rustc_hir_analysis/src/collect/generics_of.rs`, `compiler/rustc_hir_analysis/src/check/check.rs`, `compiler/rustc_hir_analysis/src/hir_ty_lowering/bounds.rs`, `compiler/rustc_hir_analysis/src/hir_ty_lowering/dyn_trait.rs`, `compiler/rustc_hir_analysis/src/variance/mod.rs`, `compiler/rustc_hir_analysis/src/diagnostics.rs`, `compiler/rustc_trait_selection/src/traits/wf.rs`, and `library/alloc/src/boxed.rs`.
2. **Executed compiler toolchain (`rustc 1.98.0-nightly` @ `rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, host `x86_64-unknown-linux-gnu`, LLVM `22.1.6`):** Live compilation and binary execution of 27 discriminating probes via `support/probe_rpit_use_and_dyn_default_lifetime.py`, recorded verbatim with scrubbed paths in `support/probe_results.json`.
3. **Cross-revision diff verification (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` vs. `20fe935d50367c0ff8872c2ebfa050c5c99d9201`):** Every governing source file was diffed between the executed `2026-05-31` compiler revision and live `rust-lang/rust` `master` (`20fe935d5`, `2026-11-24`):
   - **Shared behavior across both revisions:** `opaque_captures_all_in_scope_lifetimes` (`323-332` at `14210df0e` vs. `322-331` at `20fe935d5`), `visit_opaque_ty`, `visit_precise_capturing_arg`, `check_opaque_precise_captures` (`check.rs:572` vs. `573`), `lower_bounds` skipping `GenericBound::Use(..)` (`bounds.rs:410` vs. `368`), `object_lifetime_default` (`Empty`/`Static`/`Param`/`Ambiguous`), `compute_object_lifetime_defaults`'s `in_body` vs. `StaticLifetime` distinction, `resolve_object_lifetime_default`'s innermost-first scope walk, `compute_object_lifetime_bound`, and `elided_dyn_bound` (`ImplicitObjectLifetimeDefault` vs. `Infer`) are semantically identical across both revisions.
   - **Refactoring delta (`20fe935d50367c0ff8872c2ebfa050c5c99d9201` only):**
     1. In `compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs`, the executed `14210df0e` revision computed `object_lifetime_defaults` inline inside `visit_ty` (`1725-1805`), handling `DefKind::TyParam` and `DefKind::ConstParam`; live `20fe935d5` extracts `eligible_container` (`1999-2076`), `compute_object_lifetime_defaults` (`2094-2191`), and `visit_path_segment_args` (`1807-1870`), additionally handling trait `Self` (`DefKind::Trait`/`TraitAlias`) and multi-segment qualified paths (`RevSegIdx`), and simplifies `TyKind::Ref` from `mt.ty` to `inner_ty` (`811-818`).
     2. In `compiler/rustc_hir_analysis/src/hir_ty_lowering/dyn_trait.rs`, `14210df0e` lowered the object lifetime inline inside `lower_trait_object_ty` (`449-460`), whereas `20fe935d5` extracts helper `lower_trait_object_lifetime` (`448-470`) with identical `compute_object_lifetime_bound` priority and `RegionInferReason` tagging.
     3. Diagnostic structs in `compiler/rustc_hir_analysis/src/diagnostics.rs` moved from `crate::errors` (`14210df0e`) to `crate::diagnostics` (`20fe935d5`), preserving identical diagnostic codes and semantics.
4. **Anneal TCB audit (`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Direct read-only inspection of `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/audit/TrustedBoundary.lean`, `trusted/rustc-capture/src/driver.rs`, `trusted/rustc-capture/Cargo.toml`, `trusted/cargo-anneal/Cargo.toml`, and `THREAT_MODEL.md`.
5. **Lean 4 formalization (`leanprover/lean4` `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`):** Standalone kernel verification of `support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean` (`1,570` lines) under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` plus MetaM axiom and `._unsafe_rec` inspection.
6. **Normative specifications (`rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** RFC 599 (`text/0599-default-object-bound.md`), RFC 1156 (`text/1156-adjust-default-object-bounds.md`), RFC 3498 (`text/3498-lifetime-capture-rules-2024.md`), RFC 3617 (`text/3617-precise-capturing.md`), and Rust Reference chapters `src/types/impl-trait.md` and `src/lifetime-elision.md`.

### Scope and Invocation Conditions

- **Language editions and feature stability:** Every empirical behavior verified in this report uses **stable** Rust syntax and semantics under `--edition=2021` and `--edition=2024` with default crate types (`bin` and `lib`) and zero `#![feature(...)]` gates.
- **Edition boundary:** The RPIT default-capture flip (`opaque.span.at_least_rust_2024()`) applies specifically to Edition 2024 (and later) on `OpaqueTyOrigin::FnReturn { in_trait_or_impl: None }` (free functions and inherent methods). `use<...>` precise capturing syntax is enabled in both Edition 2021 and Edition 2024. Default trait-object lifetime bounds (`ObjectLifetimeDefault`) operate identically across Edition 2021 and Edition 2024.
- **Spec-vs-implementation nuance:** The Rust Reference (`src/types/impl-trait.md:130`) and `rustc` (`check.rs:703-726`) enforce a stricter rule than RFC 3617's guide examples (`text/3617-precise-capturing.md:72, 88`): in current stabilized `rustc`, omitting an in-scope type or const parameter from `use<...>` is rejected (`impl Trait must mention all type parameters in scope in use<...>`), so `use<...>` currently selects among **lifetime** parameters while naming all in-scope type and const parameters. Similarly, the Rust Reference (`src/lifetime-elision.md:156-163`) illustrates `Box<dyn Bar<'a>>` defaulting to `'a` via a type alias where `'a` is early-bound, whereas in a free function signature with late-bound `'a`, `wf.rs:1343` skips `r.has_escaping_bound_vars()`, causing `Box<dyn Bar<'a>>` to fall back to `'static`.

## Findings

### 1. AST Lowering and HIR Desugaring for RPIT, `use<...>`, and `dyn Trait` Bounds

Basis: source (`rust-lang/rust@20fe935d50367c0ff8872c2ebfa050c5c99d9201`) + normative (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`).

`rustc` separates opaque-type capture syntax (`impl Trait + use<...>`) from trait-object lifetime defaults (`dyn Trait`) at the AST-to-HIR lowering boundary in `compiler/rustc_ast_lowering/src/lib.rs`:

1. **Lowering `TyKind::ImplTrait` (`lib.rs:1693-1739, 1869-1939`):**
   - When `itctx` is `ImplTraitContext::OpaqueTy { origin }` (return position of free functions, inherent methods, trait/impl methods, `async fn`, or TAITs), `lower_opaque_impl_trait` (`1869-1891`) preserves the AST `span` (preserving its Rust Edition tag for `opaque.span.at_least_rust_2024()`) wrapped in `DesugaringKind::OpaqueTy`, allocates a fresh `LocalDefId`, lowers the item's `bounds`, and returns `hir::TyKind::OpaqueDef(opaque_ty_def)`.
   - Any `ast::GenericBound::Use(args, span)` bound inside `bounds` is lowered by `lower_precise_capturing_args` (`1917-1939`, invoked at `2282-2285`) into `hir::GenericBound::Use(lowered_args, span)`, mapping each `PreciseCapturingArg::Lifetime(lt)` via `lower_lifetime(..., LifetimeSource::PreciseCapturing, lt.ident.into())` and each `PreciseCapturingArg::Arg(path, id)` into `hir::PreciseCapturingNonLifetimeArg { hir_id, ident, res }`.
   - When `itctx` is `ImplTraitContext::Universal` (argument-position `impl Trait`, or APIT), `lib.rs:1700-1705` scans `bounds` for any `ast::GenericBound::Use(_, span)` and immediately emits `diagnostics::NoPreciseCapturesOnApit` (`"use<...> precise capturing syntax not allowed in argument-position impl Trait"`), because APIT introduces an anonymous generic type parameter (`impl_trait_defs`) that cannot be named or re-scoped as an opaque return type.
2. **Lowering `TyKind::TraitObject` and Bare Trait Paths (`lib.rs:1653-1692, 3352-3396`):**
   - For explicit `dyn Trait` (`TyKind::TraitObject`), AST lowering (`1653-1692`) extracts the first `GenericBound::Outlives(lifetime)` if present via `lower_lifetime(lifetime, LifetimeSource::Other, lifetime.ident.into())`. If no outlives lifetime bound was written, `1689` calls `this.elided_dyn_bound(t.span)`.
   - For bare trait paths (`ty_path`, `3352-3380`), when `path.res` resolves to `Res::Def(DefKind::Trait | DefKind::TraitAlias, _)`, `ty_path` rewrites the path into `hir::TyKind::TraitObject` and likewise supplies `self.elided_dyn_bound(span)`.
   - Critically, `elided_dyn_bound` (`3386-3396`) sets:
     ```rust
     hir::Lifetime::new(
         self.next_id(),
         Ident::new(kw::UnderscoreLifetime, self.lower_span(span)),
         hir::LifetimeKind::ImplicitObjectLifetimeDefault,
         LifetimeSource::Other,
         LifetimeSyntax::Implicit,
     )
     ```
   - By contrast, when a programmer explicitly writes `+ '_` (e.g., `Box<dyn Debug + '_>`), AST lowering invokes `lower_lifetime` -> `new_named_lifetime` (`2314-2355`), which maps `LifetimeRes::Infer` to `hir::LifetimeKind::Infer` (`2330-2333`) or `LifetimeRes::Fresh`/`Param` to `hir::LifetimeKind::Param(param)` (`2324-2329`), **never** `ImplicitObjectLifetimeDefault`. That single enum-variant split in AST lowering is what separates RFC 599/1156 default object bounds from ordinary function-signature lifetime elision.
   - Writing `use<..>` on a `dyn Trait` (`GenericBound::Use` inside `TyKind::TraitObject`) is caught at `lib.rs:1683-1687` (`span_delayed_bug` after parser/syntax rejection).

### 2. Edition 2021 vs. Edition 2024 RPIT Capture Rules (`opaque_captures_all_in_scope_lifetimes`)

Basis: normative (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` RFC 3498) + source (`rust-lang/rust@20fe935d50367c0ff8872c2ebfa050c5c99d9201`) + execution (`rustc 1.98.0-nightly`) + derived (`support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean`).

During HIR bound-variable resolution (`compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs`), `BoundVarContext::visit_opaque_ty` (`527-618`) delegates the capture-all predicate to `opaque_captures_all_in_scope_lifetimes` (`322-331`):

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

Tracing every arm and its downstream consumers yields four exact invariants:

1. **Exact Edition 2021 vs. Edition 2024 Split:**
   - The first guard (`hir::GenericBound::Use(..) => false`) overrides edition and origin unconditionally.
   - `AsyncFn` (`async fn`) and `TyAlias` (TAIT / ATPIT) always return `true`, regardless of edition.
   - For `FnReturn { in_trait_or_impl, .. }`:
     - Trait and trait-impl methods (`in_trait_or_impl: Some(RpitContext::Trait | RpitContext::TraitImpl)`) return `true` even in Edition 2021 (`in_trait_or_impl.is_some() == true`), matching `ed21_rpitit_captures_all_in_scope_by_default_rejected` (`E0597`).
     - Free functions and inherent methods (`in_trait_or_impl: None`) return `false` in Edition 2021 and `true` in Edition 2024 (`opaque.span.at_least_rust_2024()`).
2. **How In-Scope Lifetimes Are Materialized (`resolve_bound_vars.rs:531-618`, `generics_of.rs:384-397`):**
   - When `capture_all_in_scope_lifetimes == true`, `visit_opaque_ty` walks the lexical `Scope` chain outward from `self.scope`:
     - Across each `Scope::Binder { bound_vars, scope_type, s, .. }`, every `DefKind::LifetimeParam` in `bound_vars` (iterated in `.rev()`) is shifted by `late_depth` and remapped via `remap_opaque_captures(&opaque_capture_scopes, def, ident)` into a fresh synthetic `DefKind::LifetimeParam` child def (`DefPathData::OpaqueLifetime(ident.name)`) owned by `opaque.def_id`.
     - Across `Scope::Opaque`, outer nested opaques are appended to `opaque_capture_scopes` and `late_depth` resets to `0`.
     - At `Scope::Root { opt_parent_item }`, every early-bound `GenericParamDefKind::Lifetime` across enclosing `parent_generics` is similarly remapped via `remap_opaque_captures`.
     - Finally `captures.borrow_mut().reverse()` restores declaration order, and `self.rbv.opaque_captured_lifetimes.insert(opaque.def_id, captures)` records the result.
   - Downstream, `generics_of` (`compiler/rustc_hir_analysis/src/collect/generics_of.rs:384-397`) populates the `OpaqueTy`'s `own_params` directly from `tcx.opaque_captured_lifetimes(def_id)` while inheriting all parent generics (`parent_count`, including all parent type, const, and early-bound lifetime parameters).
   - Meanwhile, `is_late_bound_map` (`resolve_bound_vars.rs:2601-2641`) runs `AllCollector::visit_opaque_ty` (`2798-2803`). When `has_fully_capturing_opaque` is `true`, all generic lifetime params on the function are added to `appears_in_output.regions` (`2604-2606`). If a lifetime does *not* appear in input parameter types (not in `constrained_by_input.regions`) and does not appear in where-clauses, line `2637-2641` promotes it from late-bound to **early-bound**; whereas lifetimes appearing in input types (such as `'a` in `fn capture_check<'a>(x: &'a u32) -> impl Sized`) remain late-bound (`Scope::Binder`) and are captured as `OpaqueLifetime` arguments by `visit_opaque_ty`.
3. **Why Identical `fn capture_check(x: &u32) -> impl Sized` Compiles in Edition 2021 and Fails `E0597` in Edition 2024:**
   - The elided input `&u32` introduces an anonymous lifetime parameter `'0` in the function's late-bound `Scope::Binder`.
   - In **Edition 2021**, `opaque_captures_all_in_scope_lifetimes` returns `false`, `'0` is not mentioned in `impl Sized`, so `opaque_captured_lifetimes` is empty (`[]`). Thus the return type `Opaque<>` contains no lifetime parameters: at the call site `let val = { let local = 10u32; capture_check(&local) };`, the borrow `&local` ends immediately after the call returns, permitting `local` to drop at `}` while `val` remains alive (`RPIT_OK=42`).
   - In **Edition 2024**, `opaque_captures_all_in_scope_lifetimes` returns `true`, capturing `'0` as an `OpaqueLifetime` argument of `Opaque<'0>`. Because `val` has type `Opaque<'0>` and stays live past the end of the inner block (`}`), borrowck requires `'0` to remain live past `}`, emitting `error[E0597]: 'local' does not live long enough` along with the Edition 2024 diagnostic note (`this call may capture more lifetimes than intended, because Rust 2024 has adjusted the impl Trait lifetime capture rules`) and structured suggestion `+ use<>`.
4. **Monotonicity Corollary:** Because `opaque_captures_all_in_scope_lifetimes(.ed2021, ...) == true` implies `opaque_captures_all_in_scope_lifetimes(.ed2024, ...) == true` (while strict separation holds on free RPITs), the Edition 2024 captured set is always a superset of the Edition 2021 captured set (`Captures(Ed21) <= Captures(Ed24)`), and every caller borrow pattern accepted under Edition 2024 is accepted under Edition 2021 (`ed24_caller_borrowck_accepted_implies_ed21_accepted`).

### 3. RFC 3617 `use<...>` Precise Capturing: Resolution, Validation, and Transitive Type-Parameter Capture

Basis: normative (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` RFC 3617; `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` `src/types/impl-trait.md`) + source (`rust-lang/rust@20fe935d50367c0ff8872c2ebfa050c5c99d9201`) + execution (`rustc 1.98.0-nightly`) + derived (`support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean`).

When an opaque type specifies `+ use<...>`, three passes cooperate across HIR resolution, bound lowering, and well-formedness checking:

1. **Resolution (`resolve_bound_vars.rs:659-699`):**
   `BoundVarContext::visit_precise_capturing_arg` resolves each argument inside `Scope::Opaque`:
   - `PreciseCapturingArg::Lifetime(lt)`: If `lt.kind` is `LifetimeKind::Param(def_id)` (covering both explicit `'a` and elided `'_` resolved to a fn input lifetime parameter), `self.resolve_lifetime_ref(def_id, lt)` remaps `'a` via `remap_opaque_captures` into `opaque_captured_lifetimes` (and returns `ResolvedArg::EarlyBound(opaque_lt_def_id)`). If `lt.kind` is `Static` (`'static`), `Infer` (unresolvable `'_`), or `ImplicitObjectLifetimeDefault`, `rustc` emits `diagnostics::BadPreciseCapture`.
   - `PreciseCapturingArg::Param(param)`: Type/const params (`DefKind::TyParam | DefKind::ConstParam`) and trait `Self` (`Res::SelfTyParam { trait_ }`) resolve via `self.resolve_type_ref`, while inherent/ADT `Self` (`Res::SelfTyAlias`) emits `diagnostics::PreciseCaptureSelfAlias`.
   - Any late-bound lifetime originating inside an outer `FnPtr`, `TraitObject`, or outer `OpaqueTy` (`for<'a>` HRTB) triggers `check_lifetime_is_capturable` (`1561-1608`) -> `E0657` (`OpaqueCapturesHigherRankedLifetime`) if referenced in `use<...>`.
2. **No-Op in Trait/Outlives Bound Lowering (`hir_ty_lowering/bounds.rs:368-370`):**
   ```rust
   hir::GenericBound::Use(..) => {
       // We don't actually lower `use` into the type layer.
   }
   ```
   `use<...>` produces zero `ty::Clause` bounds; its entire semantic effect flows through the opaque's generic parameters and `check_opaque_precise_captures`.
3. **Invariant and Completeness Enforcement (`compiler/rustc_hir_analysis/src/check/check.rs:573-730`):**
   `check_opaque_precise_captures` validates every opaque with a `GenericBound::Use(precise_capturing_args, ..)` bound:
   - **Ordering (`594-608`):** First tracks `prev_non_lifetime_param`. Any subsequent `PreciseCapturingArg::Lifetime` emits `LifetimesMustBeFirst` (`"lifetime parameter 'a must be listed before non-lifetime parameters"`).
   - **Uniqueness (`611-618`):** Normalizes identifiers (`ident.normalize_to_macros_2_0()`) in `seen_params`; collisions emit `DuplicatePreciseCapture`.
   - **Variance invariant (`650-657`):** Every parameter in `expected_captures` must have `variances[param.index] == ty::Invariant` (`variance_of_opaque` in `variance/mod.rs:150-226` initializes type/const params to `Invariant`, own `OpaqueLifetime` params to `Invariant`, and marks any referenced early-bound parent lifetime `Invariant` while leaving unreferenced parent lifetimes `Bivariant`).
   - **No hidden bound lifetimes (`667-701`):** Walks all ancestor generics (`opaque_def_id` up through parent items). For every `Lifetime` not in `expected_captures` (and not `shadowed_captures` from `Self`/`T::Assoc`), if `variances[param.index] == ty::Invariant` (meaning the lifetime was captured implicitly via another bound such as `+ 'a` or `+ Trait<'a>`), emits `LifetimeNotCaptured` or `LifetimeImplicitlyCaptured`. Thus `fn bad<'a>(x: &'a u32) -> impl Debug + 'a + use<>` is rejected even though `use<>` disabled capture-all.
   - **Mandatory inclusion of all in-scope type/const parameters (`703-727`):** For **every** `Type` (including trait `Self` -> `SelfTyNotCaptured`) and `Const` parameter in scope that is absent from `expected_captures`, `rustc` unconditionally emits `ParamNotCaptured` (`"impl Trait must mention all type parameters in scope in use<...>"`). Thus, while RFC 3617 proposed `use<U>` omitting `T`, stabilized `rustc` (`ref_impl_trait.md:130` and `check.rs:703-727`) currently restricts `use<...>` opt-out to **lifetime** parameters only!
4. **Why `use<'a, T>` Excludes `'b` Yet Still Captures Regions Inside `T`:**
   - In `fn pick<'a, 'b, T>(a: &'a u32, _b: &'b u32, _t: T) -> impl Sized + use<'a, T>`, `opaque_captured_lifetimes` contains only `'a` (not `'b`), while `generics_of(opaque)` inherits `T` (listed in `use<'a, T>`).
   - At the call site `pick(&long_a, &short_b, 0u8)`, `T = u8` contains zero regions and `'b` is absent from `Opaque<'a, u8>`, so `short_b` can drop immediately (`USE_A_T_EXCLUDES_B=77`). Dropping `short_a` fails with `E0597`.
   - At the call site `pick(&long_a, &long_b, &short_c)`, `T` is instantiated with `&'c u32`, so `Opaque<'a, &'c u32>` mentions `'c` through `T`: borrowck tracks all regions contained inside captured type parameters (`RFC 3498` / `use_exact_capture_iff`) and rejects dropping `short_c` with `E0597`.
   - At the callee definition site, `check_opaque_meets_bounds` (`check.rs:294-439`) equates the concrete hidden type against `OpaqueTy` instantiated with only the captured parameters; returning `&'a u32` under `use<>` fails with `E0700` (`"hidden type for impl Debug captures lifetime that does not appear in bounds"`, suggesting `+ use<'a>`).

### 4. Default Trait-Object Lifetime Elision, Container `ObjectLifetimeDefault`, and Scope-Stack Shadowing

Basis: normative (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` RFC 599, RFC 1156; `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` `src/lifetime-elision.md`) + source (`rust-lang/rust@20fe935d50367c0ff8872c2ebfa050c5c99d9201`) + execution (`rustc 1.98.0-nightly`) + derived (`support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean`).

When AST lowering produces `LifetimeKind::ImplicitObjectLifetimeDefault` on a `dyn Trait` object, `BoundVarContext::visit_ty` (`resolve_bound_vars.rs:777-818`) triggers `self.resolve_object_lifetime_default(lifetime)` (`795`). The resolved lifetime depends on a scope stack maintained by `Scope::ObjectLifetimeDefault { lifetime: Option<ResolvedArg>, s }` (`120-123`):

1. **How Reference Types Push Defaults (`visit_ty`, `resolve_bound_vars.rs:811-818`):**
   ```rust
   hir::TyKind::Ref(lifetime_ref, ref inner_ty, _) => {
       self.visit_lifetime(lifetime_ref);
       let scope = Scope::ObjectLifetimeDefault {
           lifetime: self.rbv.defs.get(&lifetime_ref.hir_id.local_id).copied(),
           s: self.scope,
       };
       self.with(scope, |this| this.visit_ty_unambig(inner_ty));
   }
   ```
   Entering `&'a T` visits `'a` first (recording `'a` in `self.rbv.defs`) and pushes `Scope::ObjectLifetimeDefault { lifetime: Some('a) }` around `T`. For `&'a dyn Debug`, no intervening container exists, so `resolve_object_lifetime_default` finds `Some('a)` and resolves `&'a dyn Debug` to `&'a (dyn Debug + 'a)`.

2. **How Generic Containers Compute Per-Parameter Defaults (`object_lifetime_default` & `compute_object_lifetime_defaults`, `resolve_bound_vars.rs:1181-1233, 1807-1862, 2094-2191`):**
   - For any eligible container path (`Struct`, `Enum`, `Union`, `Trait`, `TraitAlias`, `TyAlias`, `AssocTy`, `Variant` via `eligible_container`, `1999-2076`), `visit_path_segment_args` (`1818-1852`) first visits all lifetime arguments so their `rbv.defs` entries are populated, then invokes `compute_object_lifetime_defaults(generics, segs)`.
   - For each type parameter `T` (or trait `Self`), `object_lifetime_default` (`1181-1233`) collects every non-higher-ranked (`bound.bound_generic_params.is_empty()`) `GenericBound::Outlives(lt)` bound on `T` into a `Set1`:
     - `0` outlives bounds -> `ObjectLifetimeDefault::Empty`;
     - `1` bound `T: 'static` -> `ObjectLifetimeDefault::Static`;
     - `1` bound `T: 'param` -> `ObjectLifetimeDefault::Param(param_def_id)`;
     - `>= 2` distinct outlives bounds (e.g., `struct TwoBounds<'a, 'b, T: ?Sized + 'a + 'b>`) -> `ObjectLifetimeDefault::Ambiguous`.
   - `compute_object_lifetime_defaults` (`2099-2163`) first determines `in_body` by walking `self.scope` outward until hitting `Scope::Body` (`true`) or `Scope::Root` (`false`), then converts each `ObjectLifetimeDefault` via `set_to_region`:
     ```rust
     let set_to_region = |set: ObjectLifetimeDefault| match set {
         ObjectLifetimeDefault::Empty => {
             if in_body { None } else { Some(ResolvedArg::StaticLifetime) }
         }
         ObjectLifetimeDefault::Static => Some(ResolvedArg::StaticLifetime),
         ObjectLifetimeDefault::Param(param_def_id) => { /* resolve lifetime arg at arg_idx in segs */ }
         ObjectLifetimeDefault::Ambiguous => None,
     };
     ```
   - `visit_path_segment_args` (`1844-1852`) wraps every type argument `ty` in `Scope::ObjectLifetimeDefault { lifetime: lt, s: self.scope }`.

3. **Why `&'a Box<dyn Debug>` Shadows `&'a` to `'static` (`library/alloc/src/boxed.rs:308-311`, `resolve_bound_vars.rs:2290-2329`):**
   In `library/alloc/src/boxed.rs:308-311`:
   ```rust
   pub struct Box<
       #[rustc_assert_variance(covariant)] T: ?Sized,
       #[stable(feature = "allocator_api", since = "1.100.0")] A: Allocator = Global,
   >(BoxRaw<T>, A);
   ```
   `T` has **no** outlives bound, so `object_lifetime_default(Box::T)` is `ObjectLifetimeDefault::Empty`. Outside function bodies (`in_body == false`), `Box<...>` therefore pushes `Scope::ObjectLifetimeDefault { lifetime: Some(ResolvedArg::StaticLifetime) }`.
   When resolving `&'a Box<dyn Debug>`:
   1. Outer `&'a ...` pushes `Scope::ObjectLifetimeDefault { lifetime: Some('a) }`.
   2. Inner `Box<...>` pushes `Scope::ObjectLifetimeDefault { lifetime: Some(ResolvedArg::StaticLifetime) }` **on top of** the `&'a` frame.
   3. `resolve_object_lifetime_default` (`2290-2329`) walks `self.scope` **from innermost frame outward**:
      ```rust
      Scope::Root { .. } => break ResolvedArg::StaticLifetime,
      Scope::Body { .. } | Scope::ObjectLifetimeDefault { lifetime: None, .. } => return,
      Scope::ObjectLifetimeDefault { lifetime: Some(l), .. } => {
          break l.shifted(late_depth);
      }
      ```
   4. It hits `Box<T>`'s `Some(ResolvedArg::StaticLifetime)` frame immediately, returning `'static` and completely shadowing the enclosing `&'a`! (Implementing RFC 1156's amendment over RFC 599 so `Box<dyn Debug>` has the identical type inside `&'a Box<dyn Debug>` as standalone `Box<dyn Debug>`.)
   5. By identical stack mechanics:
      - `&'a &'b dyn Debug` pushes `Some('b)` inside `Some('a)`, resolving to `&'a &'b (dyn Debug + 'b)`.
      - `RefWrap<'b, dyn Debug>` (`struct RefWrap<'b, T: ?Sized + 'b>(&'b T)`) has `ObjectLifetimeDefault::Param('b)`, pushing `Some('b)`, so `&'a RefWrap<'b, dyn Debug>` shadows `'a` with `'b`.
      - `TwoBounds<'a, 'b, dyn Debug>` pushes `ObjectLifetimeDefault { lifetime: None }` outside bodies (`in_body == false`); `resolve_object_lifetime_default` returns at line `2306` without populating `rbv.defs`, causing HIR typeck/borrowck to emit **`E0228`** (`"cannot deduce the lifetime bound for this trait object type from context"`).
      - Inside a function body (`Scope::Body`), `Box<dyn Debug>` sees `in_body == true`, computes `None`, and returns at line `2306` without setting `'static`, deferring the lifetime to region inference (`RegionInferReason::ObjectLifetimeDefault`)—which is why `let b: Box<dyn Debug> = Box::new(&local);` compiles cleanly inside a block even though `fn f<'a>(r: &'a u32) -> Box<dyn Debug>` fails outside a body.
      - Writing `Box<dyn Debug + '_>` in a single-input function signature (`fn box_dyn(r: &u32) -> Box<dyn Debug + '_>`) produces `LifetimeKind::Param` / `LifetimeKind::Infer` rather than `ImplicitObjectLifetimeDefault`, bypassing `resolve_object_lifetime_default` and resolving via ordinary elision to `'a`.

### 5. Trait-Derived Bounds vs. Late-Bound Signature Lifetimes (`object_region_bounds` & `has_escaping_bound_vars`)

Basis: source (`rust-lang/rust@20fe935d50367c0ff8872c2ebfa050c5c99d9201`) + documentation (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`) + execution (`rustc 1.98.0-nightly`) + derived (`support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean`).

Both `rust-lang/reference` (`src/lifetime-elision.md:108-117, 156-163`) and `dyn_trait.rs:456-469` state that trait-derived region bounds take precedence over container `ObjectLifetimeDefault` rules when an object's lifetime bound is omitted (or `'_`). Specifically, `lower_trait_object_lifetime` (`compiler/rustc_hir_analysis/src/hir_ty_lowering/dyn_trait.rs:448-470`) checks:

```rust
if let hir::LifetimeKind::ImplicitObjectLifetimeDefault | hir::LifetimeKind::Infer =
    lifetime.kind
    && let Some(region) = self.compute_object_lifetime_bound(span, predicates)
{
    return region;
}
```

However, direct source inspection and live execution reveal a critical early-bound vs. late-bound boundary inside `compute_object_lifetime_bound` (`dyn_trait.rs:529-561`) -> `traits::wf::object_region_bounds` (`compiler/rustc_trait_selection/src/traits/wf.rs:1320-1361`):

```rust
match clause.kind().skip_binder() {
    ty::ClauseKind::TypeOutlives(ty::OutlivesClause(ref t, ref r)) => {
        if t == &erased_self_ty && !r.has_escaping_bound_vars() {
            Some(*r)
        } else {
            None
        }
    }
    ...
}
```

Empirical testing on `rustc 1.98.0-nightly` confirms an important sharp edge not illustrated in `src/lifetime-elision.md:156-163` (which only exhibits `type T1<'a> = Box<dyn Bar<'a>>`):
- When `'a` on `trait BoundTrait<'a>: 'a` is **early-bound**—for example in a `struct W<'a>(Box<dyn BoundTrait<'a>>)`, a type alias `type T1<'a> = Box<dyn BoundTrait<'a>>`, an inherent `impl<'a> S<'a>`, or a function with an explicit where-bound `fn mk<'a: 'a>(r: &'a u32) -> Box<dyn BoundTrait<'a>>`—`'a` lowers to `ty::RegionKind::ReEarlyParam`, satisfying `!r.has_escaping_bound_vars()`. Thus `object_region_bounds` returns `['a]`, `compute_object_lifetime_bound` returns `Some('a)`, and `Box<dyn BoundTrait<'a>>` expands to `Box<dyn BoundTrait<'a> + 'a>` (`TRAIT_EARLY_BOUND_DYN_A=6`).
- Conversely, in an unconstrained function signature `pub fn mk<'a>(r: &'a u32) -> Box<dyn BoundTrait<'a>>`, `'a` is **late-bound** (`ty::RegionKind::ReBound` inside the `fn` signature's `Binder`), so `r.has_escaping_bound_vars()` is **`true`**! Consequently `wf.rs:1343` filters out `'a`, `compute_object_lifetime_bound` returns `None`, and `lower_trait_object_lifetime` falls back to `RegionInferReason::ObjectLifetimeDefault`—inheriting `Box<T>`'s `'static` default and rejecting `Box::new(r)` with `returning this value requires that 'a must outlive 'static`!

### 6. Live Empirical Verification Matrices (`rustc 1.98.0-nightly`)

Basis: execution (`rustc 1.98.0-nightly (14210df0e 2026-05-31)` via `support/probe_rpit_use_and_dyn_default_lifetime.py`, recorded in `support/probe_results.json`).

#### 6.1 Edition 2021 vs. Edition 2024 RPIT and `use<...>` Precise Capturing (14 Probes)

| Probe Key | Edition | Signature / Pattern | `compile_rc` | `run_rc` / Error | Observed Semantics |
| :--- | :---: | :--- | :---: | :--- | :--- |
| `ed21_unannotated_rpit_does_not_capture_unused_ref` | `2021` | `fn capture_check(x: &u32) -> impl Sized { 42 }` | `0` | `rc=0` (`RPIT_OK=42`) | Unused `&local` lifetime not captured; inner block drop allowed |
| `ed24_unannotated_rpit_captures_all_in_scope_lifetimes_rejected` | `2024` | `fn capture_check(x: &u32) -> impl Sized { 42 }` | `1` | `E0597` (`Rust 2024` note + `+ use<>` help) | Unannotated Ed24 RPIT captures `&local` lifetime |
| `ed24_rpit_use_empty_opts_out_of_lifetime_capture` | `2024` | `fn capture_check(x: &u32) -> impl Sized + use<> { 42 }` | `0` | `rc=0` (`ED24_USE_EMPTY=42`) | `use<>` restores Edition 2021 non-capturing behavior |
| `ed24_rpit_use_a_t_excludes_b_ok` | `2024` | `fn pick<'a, 'b, T>(...) -> impl Sized + use<'a, T>` (`T=u8`, drop `short_b`) | `0` | `rc=0` (`USE_A_T_EXCLUDES_B=77`) | `'b` excluded; `short_b` drops safely before `r` |
| `ed24_rpit_use_a_t_still_captures_a_rejected` | `2024` | `fn pick<'a, 'b, T>(...) -> impl Sized + use<'a, T>` (`T=u8`, drop `short_a`) | `1` | `E0597` (`short_a` dropped while borrowed) | `'a` explicitly captured in `use<'a, T>` |
| `ed24_rpit_use_a_t_indirectly_captures_t_lifetime_rejected` | `2024` | `fn pick<'a, 'b, T>(...) -> impl Sized + use<'a, T>` (`T=&'c u32`, drop `short_c`) | `1` | `E0597` (`short_c` dropped while borrowed) | Capturing `T` transitively captures `'c` inside `T` |
| `ed24_rpit_use_omitting_in_scope_type_param_rejected` | `2024` | `fn bad<'a, T>(_a: &'a u32, _t: T) -> impl Sized + use<'a>` | `1` | `must mention all type parameters in scope` | Stabilized `rustc` forbids omitting in-scope `T` (`check.rs:712`) |
| `ed24_rpit_use_lifetime_after_type_param_rejected` | `2024` | `fn bad<'a, T>(...) -> impl Sized + use<T, 'a>` | `1` | `must be listed before non-lifetime parameters` | `LifetimesMustBeFirst` (`check.rs:601`) |
| `ed24_rpit_use_omitting_bound_lifetime_rejected` | `2024` | `fn bad<'a>(x: &'a u32) -> impl Debug + 'a + use<>` | `1` | `captures lifetime parameter, but it is not mentioned in use<...>` | `LifetimeNotCaptured` (`check.rs:677`) |
| `ed24_rpit_use_on_apit_rejected` | `2024` | `fn bad(_x: impl Sized + use<>)` | `1` | `not allowed in argument-position impl Trait` | `NoPreciseCapturesOnApit` (`lib.rs:1704`) |
| `ed24_rpit_use_elided_underscore_ok` | `2024` | `fn capture_elided(x: &u32) -> impl Sized + use<'_> { *x }` | `0` | `rc=0` (`USE_ELIDED_UNDERSCORE=99`) | Elided `'_` resolves to `LifetimeKind::Param` |
| `ed21_rpitit_captures_all_in_scope_by_default_rejected` | `2021` | `trait Maker { fn make(&self, x: &u32) -> impl Sized; }` | `1` | `E0597` (`local` dropped while borrowed) | Trait RPITIT captures all in-scope lifetimes in Ed21 (`in_trait_or_impl.is_some()`) |
| `ed21_rpit_use_optin_captures_ref_rejected` | `2021` | `fn capture_check(x: &u32) -> impl Sized + use<'_> { 42 }` | `1` | `E0597` (`local` dropped while borrowed) | `use<'_>` opts into capturing `'0` in Ed21 |
| `ed24_rpit_callee_returning_uncaptured_lifetime_rejected` | `2024` | `fn bad<'a>(x: &'a u32) -> impl Debug + use<> { x }` | `1` | `E0700` (`captures lifetime that does not appear in bounds`) | Callee hidden type cannot mention uncaptured `'a` |

#### 6.2 Trait-Object Default Lifetime Elision & Container Shadowing (13 Probes)

| Probe Key | Type / Pattern | `compile_rc` | `run_rc` / Error | Resolved Object Lifetime |
| :--- | :--- | :---: | :--- | :--- |
| `box_dyn_defaults_to_static_rejected_with_ref_a` | `fn box_dyn<'a>(r: &'a u32) -> Box<dyn Debug>` | `1` | `requires that 'a must outlive 'static` | `'static` (`Box` `Empty` outside body) |
| `box_dyn_explicit_plus_a_ok` | `fn box_dyn<'a>(r: &'a u32) -> Box<dyn Debug + 'a>` | `0` | `rc=0` (`BOX_DYN_A=1`) | `'a` (explicit `Param`) |
| `box_dyn_underscore_in_return_uses_ordinary_elision_ok` | `fn box_dyn(r: &u32) -> Box<dyn Debug + '_>` | `0` | `rc=0` (`BOX_DYN_UNDERSCORE=4`) | `'a` (`Infer` / ordinary fn elision) |
| `ref_a_dyn_defaults_to_a_ok` | `fn ref_dyn<'a>(d: &'a (dyn Debug + 'a)) -> &'a dyn Debug` | `0` | `rc=0` (`REF_DYN_A=2`) | `'a` (pushed by `&'a`) |
| `ref_a_box_dyn_inner_box_overrides_outer_ref_a_with_static_rejected` | `fn coerce<'a>(b: &'a Box<dyn Debug + 'a>) -> &'a Box<dyn Debug>` | `1` | `requires that 'a must outlive 'static` | `'static` (`Box` shadows outer `&'a`) |
| `ref_a_box_dyn_explicit_a_ok` | `fn coerce<'a>(b: &'a Box<dyn Debug + 'a>) -> &'a Box<dyn Debug + 'a>` | `0` | `rc=0` (`REF_BOX_DYN_EXPLICIT_A=5`) | `'a` (explicit bound overrides `Box`) |
| `struct_ref_a_dyn_defaults_to_a_ok` | `struct RefWrap<'a, T: ?Sized + 'a>(&'a T);` -> `RefWrap<'a, dyn Debug>` | `0` | `rc=0` (`STRUCT_DYN_A=3`) | `'a` (`ObjectLifetimeDefault::Param`) |
| `struct_two_bounds_ambiguous_dyn_rejected_e0228` | `struct TwoBounds<'a, 'b, T: ?Sized + 'a + 'b>` -> `TwoBounds<'a, 'b, dyn Debug>` | `1` | `E0228` (`cannot deduce the lifetime bound`) | `Ambiguous` (`None` outside body) |
| `trait_with_late_bound_lifetime_box_dyn_falls_back_to_static_rejected` | `trait BoundTrait<'a>: 'a {}` -> `fn mk<'a>(r: &'a u32) -> Box<dyn BoundTrait<'a>>` | `1` | `requires that 'a must outlive 'static` | `'static` (`wf.rs:1343` skips late-bound `'a`) |
| `trait_with_early_bound_lifetime_box_dyn_derives_a_ok` | `trait BoundTrait<'a>: 'a {}` -> `fn mk<'a: 'a>(r: &'a u32) -> Box<dyn BoundTrait<'a>>` | `0` | `rc=0` (`TRAIT_EARLY_BOUND_DYN_A=6`) | `'a` (`compute_object_lifetime_bound`) |
| `in_body_box_dyn_infers_non_static_lifetime_ok` | `let b: Box<dyn Debug> = Box::new(&local);` inside `main` | `0` | `rc=0` (`IN_BODY_BOX_DYN=7`) | Inferred (`in_body == true -> None`) |
| `nested_ref_a_ref_b_dyn_defaults_to_inner_b_ok` | `fn nested_ref<'a, 'b>(r: &'a &'b (dyn Debug + 'b)) -> &'a &'b dyn Debug` | `0` | `rc=0` (`NESTED_REF_DYN_B=8`) | `'b` (inner `&'b` shadows outer `&'a`) |
| `ref_a_of_refwrap_b_dyn_shadows_outer_a_with_b_ok` | `fn ref_of_wrap<'a, 'b>(w: &'a RefWrap<'b, dyn Debug + 'b>) -> &'a RefWrap<'b, dyn Debug>` | `0` | `n/a` (lib crate) | `'b` (`RefWrap<'b, _>` shadows outer `&'a`) |

### 7. Kernel-Checked Lean 4 (`v4.34.1`) Soundness Formalization

Basis: derived + execution (`leanprover/lean4` `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`, `support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean`, `1,570` lines).

`support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean` formalizes the complete RPIT capture, `use<...>` validation, `ObjectLifetimeDefault` scope-stack resolution, and lifetime well-formedness contracts inside namespace `RustcRpitUseAndDynDefaultLifetimeSoundness`. All definitions are explicitly `noncomputable def` without `deriving`, `partial`, `sorry`, `Classical.choice`, `omega`, `bv_decide`, or `native_decide`, yielding **`537`** elaborated constants, **`0` `._unsafe_rec`** declarations, **`0` `isPartial` / `isUnsafe` / custom `axiom`** declarations, and **0 errors / 0 warnings** under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

| Theorem (in `RustcRpitUseAndDynDefaultLifetimeSoundness`) | Statement Summary | `#print axioms` |
| :--- | :--- | :--- |
| `directCaptured_iff_use_of_valid` | Under `preciseCapturesValid`, direct captured lifetimes equal `useLifetimeIds args` regardless of edition or origin | `[propext]` |
| `edition2024_direct_capture_monotone` | `directCapturedLifetimes .ed21 ⊆ directCapturedLifetimes .ed24` across all origins, bounds, and `use<...>` | `[]` |
| `edition2024_effective_capture_monotone` | `effectiveCapturedLifetimes .ed21 ⊆ effectiveCapturedLifetimes .ed24` including type-parameter regions | `[]` |
| `ed24_caller_borrowck_accepted_implies_ed21_accepted` | Every caller borrow context accepted in Edition 2024 is accepted in Edition 2021 | `[]` |
| `opaque_callee_caller_soundness` | Callee hidden-type WF + caller borrowck acceptance implies UAF-free caller execution (`callerOpaqueSafe`) | `[]` |
| `use_exact_capture_iff` | Exact characterization: `l` is captured iff `l ∈ useLifetimeIds args` or `∃ tp ∈ useTypeParamIds args, l ∈ inst tp` | `[propext]` |
| `use_permits_caller_drop_of_uncaptured_borrow` | Caller may drop any uncaptured borrow before opaque drop while preserving `callerBorrowckAccepts` | `[propext]` |
| `witness_ed21_vs_ed24_capture_check_and_use_empty` | Strict Ed21 vs. Ed24 separation + `use<>` opt-out + Ed21 RPITIT parity | `[propext]` |
| `witness_pick_use_a_t_selective_and_indirect_capture` | `use<'a, T>` excludes `'b`, captures `'a`, and transitively captures `'c` inside `T = &'c u32` | `[propext]` |
| `witness_precise_capture_validation_boundaries` | Rejects missing `T`, `use<T, 'a>`, missing bound `'a`, APIT `use<>`, and uncaptured hidden `'a` | `[propext]` |
| `stack_push_concrete_default_shadows_outer` | Innermost `objectLifetimeDefault (some lt)` overrides all enclosing scope frames | `[]` |
| `ref_box_dyn_shadows_outer_ref_to_static` | `&'a Box<dyn Debug>` resolves to `.staticLt` outside bodies, independent of `'a` | `[]` |
| `ref_box_dyn_independent_of_outer_lifetime` | `&'a₁ Box<dyn Debug>` and `&'a₂ Box<dyn Debug>` resolve identically to `.staticLt` | `[]` |
| `nested_ref_shadows_outer_ref` / `ref_of_refwrap_shadows_outer_ref` | `&'a &'b dyn Debug` and `&'a RefWrap<'b, dyn Debug>` shadow `'a` with `'b` | `[]` |
| `witness_all_dyn_default_lifetime_probes` | Exact agreement across all 13 empirical `dyn Trait` resolution cases | `[]` |
| `dyn_ctx_floor_always_matches_resolved` | `ctxOutlivesFloor` equals `evalResolvedLt` on the resolved `dyn` lifetime | `[]` |
| `dyn_wf_implies_referent_outlives_floor` / `dyn_wf_outer_ref_sound` | `DynTypeWF` guarantees every enclosing `&'a` / `RefWrap<'a, _>` bound outlives concrete referent | `[]` |
| `ce_ref_box_dyn_fails_wf_for_finite_borrow_while_explicit_a_succeeds` | `&'a Box<dyn Debug>` fails `DynTypeWF` for finite borrow `'a`, while `&'a Box<dyn Debug + 'a>` succeeds | `[]` |
| `ambiguous_container_always_fails_wf` | `TwoBounds<'a, 'b, dyn Debug>` fails `DynTypeWF` outside bodies (`E0228`) | `[]` |
| `frontend_rpit_and_dyn_soundness` | Combined end-to-end soundness of RPIT capture + `dyn` default resolution | `[]` |
| `ed21_to_ed24_use_migration_preserves_captures_when_no_bounds` | Migrating unbound Ed21 RPIT to Ed24 `+ use<T...>` preserves exact effective captures | `[propext]` |

### 8. Implications for Verified `rustc` Typechecking and Anneal's Trusted Computing Base

Basis: source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) + derived.

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes the exact boundary between these frontend lifetime contracts and Anneal's current verification pipeline:

1. **Edition 2024 Inside Anneal Tooling (`trusted/audit/Cargo.toml:12`, `trusted/cargo-anneal/Cargo.toml:14`, `trusted/rustc-capture/Cargo.toml:12`, `trusted/rustc-capture/tests/compiler_session.rs:33`):** Anneal's own Rust binaries and `rustc-capture` integration tests invoke `rustc` with `--edition=2024`. Any unannotated `-> impl Trait` helper added to Edition 2024 Rust crates compiled under Anneal is subject to `opaque_captures_all_in_scope_lifetimes == true` and may require `+ use<...>` to avoid `E0597` over-capturing.
2. **Current Fail-Closed MIR Admission (`trusted/lean/Trusted/MirAst.lean:304-321, 461-470, 641-662, 753-795`):**
   - `MirTy` erases lifetime parameters on `.ref mutability pointee` (`TyKind::Ref(_, pointee, mutability)`) and maps all non-fieldless ADTs (`Box<T, A>`, `RefWrap<'a, T>`), `FnPtr`, `Dynamic` (`dyn Trait`), and `Opaque` (`impl Trait`) types to `.unsupported`, failing closed with `FaultKind.unsupported` (`MirSemantics.lean:49-52, 82-105`).
   - `ProjectionElem::OpaqueCast`, `StatementKind::AscribeUserType(..., ty::Variance)`, `TerminatorKind::Drop`, and indirect `Call` (including `dyn Trait` dispatch) likewise map to `.unsupported`.
   - In `trusted/rustc-capture/src/driver.rs:75-84, 145-150`, `AnalysisCallbacks` confirms clean `rustc` analysis (`tcx.dcx().has_errors().is_none()`) prior to MIR extraction.
3. **Requirements for Future Frontend Verification or Anneal Type-System Expansion (`THREAT_MODEL.md:99-105`):** Because `MirAst` relies on `rustc`'s frontend type-checking and borrow-checking (`THREAT_MODEL.md:99-105`), any verified `rustc` frontend or future extension of Anneal that admits `impl Trait` (`Opaque`) or `dyn Trait` (`Dynamic`) before region erasure must:
   - Implement `opaque_captures_all_in_scope_lifetimes` keyed on `GenericBound::Use`, `OpaqueTyOrigin`, and Edition `2024`, tracking *both* direct captured lifetimes and indirect lifetimes inside captured type parameters `T` (`use_exact_capture_iff`);
   - Enforce `check_opaque_precise_captures` invariants (explicit-bound lifetime inclusion and mandatory type/const parameter listing) and callee hidden-type region containment (`E0700`);
   - Implement the innermost-first `Scope::ObjectLifetimeDefault` stack (assigning `Box<T>` `Empty -> 'static` outside bodies to shadow outer `&'a`, distinguishing `ImplicitObjectLifetimeDefault` from `Infer`, and guarding trait-derived bounds with `!r.has_escaping_bound_vars()`).

## Boundaries

- **Known not to apply:**
  - **`&'a Box<dyn Debug>` does NOT default the inner trait object to `'a`.** Under RFC 1156 and `resolve_bound_vars.rs:2120-2125, 2290-2310`, `Box<T>` pushes `ObjectLifetimeDefault::Empty -> 'static` on top of `&'a`'s scope, shadowing `'a` (`ref_a_box_dyn_inner_box_overrides_outer_ref_a_with_static_rejected`).
  - **Trait-derived supertrait bounds (`trait Bar<'a>: 'a`) do NOT override `Box`'s `'static` default when `'a` is late-bound on a `fn`.** Because `wf.rs:1343` checks `!r.has_escaping_bound_vars()`, late-bound `'a` in `fn mk<'a>(r: &'a u32) -> Box<dyn Bar<'a>>` is skipped and falls back to `'static`, unlike early-bound `struct W<'a>(Box<dyn Bar<'a>>)` or `fn mk<'a: 'a>`.
  - **Edition 2021 free-function RPIT rules do NOT apply to Edition 2021 trait/impl RPITIT, `async fn`, or TAIT.** `opaque_captures_all_in_scope_lifetimes` captures all in-scope lifetimes in Edition 2021 whenever `in_trait_or_impl.is_some()` or `origin` is `AsyncFn`/`TyAlias`.
  - **RFC 3617 `use<...>` in stabilized `rustc` does NOT permit omitting in-scope type or const parameters.** `check_opaque_precise_captures` (`check.rs:703-727`) rejects `fn bad<'a, T>(...) -> impl Sized + use<'a>` (`ParamNotCaptured`), even though RFC 3617 discussed future type-parameter omission.
  - **`Box<dyn Debug>` outside a function body (`'static`) does NOT apply inside a function body.** Inside `Scope::Body`, `compute_object_lifetime_defaults` sets `in_body == true`, returning `None` so region inference infers a non-`'static` local borrow (`IN_BODY_BOX_DYN=7`).
  - **`Box<dyn Debug + '_>` does NOT use `ObjectLifetimeDefault`.** AST lowering assigns `+ '_` `LifetimeKind::Infer` or `LifetimeKind::Param`, using ordinary function-signature elision (`BOX_DYN_UNDERSCORE=4`).
- **Not examined:**
  - **Nested `impl Trait` inside `impl Trait` or closures returning `impl Trait`:** Interaction of `Scope::Opaque` stacking with `Scope::Binder` (`late_depth = 0`) and `OpaqueCapturesHigherRankedLifetime` (`E0657`) was audited in source (`resolve_bound_vars.rs:577-610, 1561-1608`) but not probed empirically or mechanized in Lean.
  - **`use<'static>` and `use<Self>` / `use<const N: usize>` inside trait RPITITs and `impl` blocks:** `SelfTyNotCaptured`, `BadPreciseCapture` (`'static`), and const-generic `PreciseCapturingArg::Param` were observed in `resolve_bound_vars.rs:669-697` and `check.rs:703-727` by source inspection only.
  - **Trait aliases (`DefKind::TraitAlias`) and associated type projection containers (`eligible_container` `rev_seg_idx == 1`) for `ObjectLifetimeDefault`:** Observed in `resolve_bound_vars.rs:2026-2051` at `20fe935d5`, not separately probed via `rustc`.
  - **RPIT auto-trait leakage interaction with `use<...>`:** Whether uncaptured lifetimes in hidden types can still affect auto-trait bounds (`Send`/`Sync`) was outside this report's scope.
- **Unsupported:**
  - **`use<...>` on argument-position `impl Trait` (`ImplTraitContext::Universal`) and on `dyn Trait`:** Explicitly rejected by `rustc` (`ast_lowering/src/lib.rs:1683-1687, 1700-1705`, verified via `ed24_rpit_use_on_apit_rejected`).
  - **Anneal `Trusted.MirAst` / `Trusted.MirSemantics` (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Explicitly does not support `Dynamic` (`dyn Trait`), `Opaque` / `OpaqueCast`, `Box<T, A>`, `Drop`, or `AscribeUserType` (all fail closed to `.unsupported`). Consequently, `support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean` is a standalone formalization rather than an import of `Trusted.MirSemantics`.
- **Unknown / attractive stronger claims NOT established:**
  - **Refinement between Lean model and `rustc`'s Rust source:** Our Lean 4 development proves soundness and counterexamples over a faithful structural model of `rustc`'s HIR capture, `ObjectLifetimeDefault`, and borrowck lifetime rules; it is not a verified extraction or refinement proof of the `rustc_hir_analysis` / `rustc_borrowck` Rust implementation itself.

## Evidence

### 1. Upstream `rust-lang/rust` Primary Sources (`20fe935d50367c0ff8872c2ebfa050c5c99d9201` and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`)

Observed `2026-11-24`:

- **AST lowering (`compiler/rustc_ast_lowering/src/lib.rs` at `20fe935d5`):**
  - `1653-1692` (`TyKind::TraitObject` lowering, calling `elided_dyn_bound` when outlives lifetime is omitted, rejecting `GenericBound::Use` in `dyn` types).
  - `1693-1739` (`TyKind::ImplTrait` lowering; `1700-1705` emits `NoPreciseCapturesOnApit`).
  - `1869-1939` (`lower_opaque_impl_trait`, `lower_opaque_inner`, `lower_precise_capturing_args`).
  - `2314-2355` (`new_named_lifetime`, mapping explicit `'_` to `LifetimeKind::Infer` or `LifetimeKind::Param`, never `ImplicitObjectLifetimeDefault`).
  - `3352-3396` (`ty_path` turning trait paths into `TyKind::TraitObject` and `elided_dyn_bound` emitting `LifetimeKind::ImplicitObjectLifetimeDefault`).
- **Bound-variable resolution (`compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs` at `20fe935d5`):**
  - `80-169` (`enum Scope`, including `Binder`, `Body`, `ObjectLifetimeDefault`, `Opaque`, `LateBoundary`, `Root`).
  - `322-331` (`opaque_captures_all_in_scope_lifetimes`).
  - `527-618` (`visit_opaque_ty`, collecting late-bound and early-bound parent lifetimes when `capture_all_in_scope_lifetimes` is `true`).
  - `659-699` (`visit_precise_capturing_arg`, rejecting `'static`/`'_` non-param lifetimes with `BadPreciseCapture` and `Res::SelfTyAlias` with `PreciseCaptureSelfAlias`).
  - `777-818` (`visit_ty` arms for `TyKind::TraitObject` and `TyKind::Ref`, pushing `Scope::ObjectLifetimeDefault`).
  - `1181-1233` (`object_lifetime_default` query computing `Empty`, `Static`, `Param`, `Ambiguous`).
  - `1354-1608` (`resolve_lifetime_ref`, `check_lifetime_is_capturable`, `OpaqueCapturesHigherRankedLifetime`).
  - `1634-1669` (`remap_opaque_captures` creating `DefPathData::OpaqueLifetime` synthetic child defs).
  - `1807-1862` (`visit_path_segment_args` pushing container `object_lifetime_defaults`).
  - `1999-2191` (`eligible_container` and `compute_object_lifetime_defaults`, mapping `Empty` -> `None` if `in_body` else `Some(StaticLifetime)`).
  - `2290-2329` (`resolve_object_lifetime_default` walking `self.scope` innermost-outward).
  - `2587-2651, 2786-2805` (`is_late_bound_map`, `AllCollector::visit_opaque_ty` promoting unused fn lifetimes to early-bound under fully capturing opaques).
- **Opaque generics, variance, bound lowering, and precise-capture checking (`20fe935d5`):**
  - `compiler/rustc_hir_analysis/src/collect/generics_of.rs:384-397` (populating `OpaqueTy` `own_params` from `tcx.opaque_captured_lifetimes(def_id)`).
  - `compiler/rustc_hir_analysis/src/variance/mod.rs:97-227` (`variance_of_opaque`, initializing type/const params `Invariant` and parent lifetimes `Bivariant` unless referenced in bounds).
  - `compiler/rustc_hir_analysis/src/check/check.rs:573-730` (`check_opaque_precise_captures`: `LifetimesMustBeFirst`, `DuplicatePreciseCapture`, `LifetimeNotCaptured`, `ParamNotCaptured`, `SelfTyNotCaptured`).
  - `compiler/rustc_hir_analysis/src/hir_ty_lowering/bounds.rs:319-373` (`lower_bounds`; `368-370` skips `hir::GenericBound::Use(..)`).
- **Trait-object lifetime lowering & `Box<T, A>` (`20fe935d5`):**
  - `compiler/rustc_hir_analysis/src/hir_ty_lowering/dyn_trait.rs:443-470, 529-561` (`lower_trait_object_lifetime`, `compute_object_lifetime_bound`).
  - `compiler/rustc_trait_selection/src/traits/wf.rs:1320-1361` (`object_region_bounds`; `1343` filters `!r.has_escaping_bound_vars()`).
  - `library/alloc/src/boxed.rs:308-311` (`pub struct Box<T: ?Sized, A: Allocator = Global>` with zero outlives bounds on `T`).

### 2. Anneal TCB Sources (`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Observed `2026-11-24`:

- `trusted/audit/Cargo.toml:12`, `trusted/cargo-anneal/Cargo.toml:14`, `trusted/rustc-capture/Cargo.toml:12`, `trusted/rustc-capture/tests/compiler_session.rs:33` (`edition = "2024"` / `--edition=2024`).
- `trusted/rustc-capture/src/driver.rs:75-84, 145-150` (`AnalysisCallbacks` requiring clean `rustc` analysis).
- `trusted/lean/Trusted/MirAst.lean:304-321, 461-470, 641-662, 753-795` (`MirTy`, `ProjectionElem`, `StatementKind`, `TerminatorKind` failing closed on `Dynamic`, `OpaqueCast`, `AscribeUserType`, `Drop`, and non-fieldless ADTs).
- `trusted/lean/Trusted/MirSemantics.lean:49-52, 82-105` (`FaultKind.unsupported` vs. `FaultKind.undefined`).
- `trusted/audit/TrustedBoundary.lean:1604-1637` (`sorryAx` and forbidden compiler-reflection checks).
- `THREAT_MODEL.md:99-105` (explicit inclusion of `rustc` frontend assumptions in TCB audit log).

### 3. Normative Specifications

- `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/0599-default-object-bound.md`, `text/1156-adjust-default-object-bounds.md`, `text/3498-lifetime-capture-rules-2024.md`, `text/3617-precise-capturing.md`.
- `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/types/impl-trait.md`, `src/lifetime-elision.md`.

### 4. Preserved Support Artifacts

1. **`support/probe_rpit_use_and_dyn_default_lifetime.py`:** Standalone Python 3.10+ probe harness executing 27 total `rustc` checks (14 Edition 2021/2024 RPIT + `use<...>` checks and 13 `dyn Trait` default-lifetime checks) inside `tempfile.TemporaryDirectory`, scrubbing host paths and validating all assertions.
2. **`support/probe_results.json`:** Recorded `2026-11-24T01:04:57Z` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`), exit status `0`.
3. **`support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean`:** `1,570`-line standalone Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) formalization verified `2026-11-24` with exit code `0`, `0` warnings under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, `537` elaborated declarations, `0` `._unsafe_rec`, `0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`, and `0` forbidden tactics.

## Revalidation

### 1. Re-run Live `rustc` Empirical Probes

```bash
python3 support/probe_rpit_use_and_dyn_default_lifetime.py --out /tmp/reval_rpit_dyn_results.json
```

Requires only a stable or nightly `rustc` toolchain supporting Edition `2024` (`rustc >= 1.85`). Exit code `0` confirms all 14 RPIT / `use<...>` and 13 `dyn Trait` default-lifetime probes behave identically.

### 2. Re-verify Lean 4 Formalization and Zero-`._unsafe_rec` / Axiom Hygiene

```bash
LEAN_BIN="$(which lean)" # Lean v4.34.1 or newer
"$LEAN_BIN" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean
```

To re-verify `#print axioms` and `0` `._unsafe_rec` constants via Lean MetaM:

```bash
cp support/RpitPreciseCapturingAndDynDefaultLifetimeSoundness.lean /tmp/reval_rpit_dyn_audit.lean
cat >> /tmp/reval_rpit_dyn_audit.lean <<'EOF'
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.directCaptured_iff_use_of_valid
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.edition2024_direct_capture_monotone
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.edition2024_effective_capture_monotone
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.ed24_caller_borrowck_accepted_implies_ed21_accepted
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.opaque_callee_caller_soundness
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.use_exact_capture_iff
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.use_permits_caller_drop_of_uncaptured_borrow
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.ref_box_dyn_shadows_outer_ref_to_static
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.dyn_wf_implies_referent_outlives_floor
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.ce_ref_box_dyn_fails_wf_for_finite_borrow_while_explicit_a_succeeds
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.frontend_rpit_and_dyn_soundness
#print axioms RustcRpitUseAndDynDefaultLifetimeSoundness.ed21_to_ed24_use_migration_preserves_captures_when_no_bounds
EOF
"$LEAN_BIN" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false /tmp/reval_rpit_dyn_audit.lean
rm -f /tmp/reval_rpit_dyn_audit.lean
```

### 3. Narrow Upstream Source Diff Checks

When revalidating against newer `rust-lang/rust` or `joshlf/anneal` revisions, inspect diffs strictly on the governing files:

```bash
gh api "repos/rust-lang/rust/compare/20fe935d50367c0ff8872c2ebfa050c5c99d9201...HEAD" --jq \
  '.files[].filename | select(test("rustc_ast_lowering/src/lib\\.rs|rustc_hir_analysis/src/(collect/resolve_bound_vars\\.rs|collect/generics_of\\.rs|check/check\\.rs|hir_ty_lowering/(bounds|dyn_trait)\\.rs|variance/mod\\.rs)|rustc_trait_selection/src/traits/wf\\.rs|library/alloc/src/boxed\\.rs"))'

gh api "repos/joshlf/anneal/compare/c131b320eeeb26ef692e5afd5ec8db49ee518613...HEAD" --jq \
  '.files[].filename | select(test("trusted/(lean/Trusted/(MirAst|MirSemantics)\\.lean|rustc-capture/src/driver\\.rs)"))'
```
