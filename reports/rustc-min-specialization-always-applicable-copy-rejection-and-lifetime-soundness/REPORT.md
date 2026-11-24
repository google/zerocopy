# rustc `min_specialization` Soundness (`check_always_applicable`), `Copy` Rejection vs. Specialization Traits, Lifetime-Erasure Invariance, and `default type` Separation

## Summary

Rust's post-monomorphization codegen erases all lifetimes (`ReErased`), whereas trait-bound verification and borrow checking run prior to region erasure. Under unrestricted `#![feature(specialization)]` (RFC 1210), dispatching on traits, associated types, `'static` bounds, or repeated parameters whose applicability can depend on concrete lifetimes creates a fatal soundness hole: a caller with generic type parameters or erased regions can dispatch to a specialized `impl` whose lifetime-dependent preconditions (such as `OnlyStaticCopy<'a>: Copy`, which holds only for `'a = 'static`) do **not** hold at runtime. `#![feature(min_specialization)]` eliminates that gap for safe Rust via a two-layer compile-time enforcement architecture paired with associated-item feature gating:

1. **Two-Layer Compiler Enforcement (`specialize` + `check_min_specialization`):**
   - **Layer 1 (`specialization_graph::Children::insert` & `tcx.specializes`):** Whenever two impls overlap (`traits::overlapping_trait_impls`), `Children::insert` omits specialization comparisons only for `#[marker]` traits (`ImplOverlapKind::Permitted`). Otherwise it computes `le = tcx.specializes((impl_def_id, possible_sibling))` and `ge = tcx.specializes((possible_sibling, impl_def_id))`, emitting **`E0119`** whenever `le == ge`—both in non-chain diamond conflicts (`[u8; N]` vs. `[T; 4]`, `le = ge = false`) and whenever **region-blind** `specializes` (`TypingMode::non_body_analysis()` without `resolve_regions`) collapses lifetime distinctions (`(&'a u8, &'b u8)` vs. `(&'a u8, &'a u8)` and `T` vs. `T: 'static`, `le = ge = true`). Conversely, because `specializes` skips region resolution, generalizing lifetimes across the inheritance edge (`impl<T: 'static> Tr for T` specialized by `impl<'a> Tr for &'a i32`) silently passes Layer 1 (`le = true, ge = false`).
   - **Layer 2 (`compiler/rustc_hir_analysis/src/impl_wf_check/min_specialization.rs`):** Note the path correction from older secondary summaries: `min_specialization.rs` lives in `rustc_hir_analysis::impl_wf_check`, not `rustc_trait_selection`. Called from `impl_wf_check::check_type_wf` whenever `of_trait && tcx.features().min_specialization()`, `check_min_specialization` invokes `parent_specialization_node` and `check_always_applicable`. Unlike Layer 1, `get_impl_args` explicitly invokes `ocx.resolve_regions_and_report_errors` (stopping `impl<T: 'static>` -> `impl<'a> &'a i32` with **`E0477`**) before checking four predicates: non-empty items (`check_has_items`), zero `'static` in unconstrained parent args (`check_static_lifetimes`), zero repeated unconstrained parameters (`check_duplicate_params`, using `unconstrained_parent_impl_args` to exempt parent params uniquely determined by non-self `Projection` bounds such as `<I as Iterator>::Item = T`), and clause admissibility (`check_predicates` / `check_specialization_on`). For traits marked `TraitSpecializationKind::AlwaysApplicable`, `parent_specialization_node` returns `Some(Node::Trait)` even for root impls, forcing every impl of a `#[rustc_specialization_trait]` to pass `check_always_applicable` against empty `impl2_clauses`.

2. **Why `Copy` Is Rejected While `Sized`/`TrustedStep` and `TrustedLen`/`TrivialClone` Succeed (`collect.rs`, `check_specialization_on`, `library/core`):**
   - `rustc_hir_analysis::collect::trait_def` assigns `TraitSpecializationKind` per trait: `AlwaysApplicable` for `#[rustc_specialization_trait]`, `Marker` for `#[rustc_unsafe_specialization_marker]` (renamed `#[unsafe(rustc_allow_lifetime_dependent_specialization)]` by `49d734536222bf28bb6d07d885b3a81d145981da` and preserved on `058c701055c4b6f60f622d616afc0349911c38c3`), and `None` otherwise.
   - `Copy` (`pub trait Copy: Clone`) and `Clone` carry `TraitSpecializationKind::None`, and safe Rust explicitly allows lifetime-dependent `Copy` impls (`impl Copy for OnlyStaticCopy<'static> {}`). Because `check_predicates` elaborates `impl1`'s clauses via `traits::elaborate`, specializing `impl<T> Tr for T` with `impl<T: Copy> Tr for T` expands into **both** `T: Copy` and `T: Clone`, emitting **two** errors (`cannot specialize on trait Copy` and `cannot specialize on trait Clone`).
   - `Sized` / `MetaSized` / `PointeeSized` (and experimental `Forget` / `Move` on `058c70105`), `TrustedFused`, `InPlaceIterable`, `TrustedStep: Step + Copy`, and `BytewiseEq<Rhs = Self>: PartialEq<Rhs> + Sized` carry `#[rustc_specialization_trait]` (`AlwaysApplicable`). `check_predicates` elaborates supertraits of `AlwaysApplicable` traits directly into `impl2_clauses`; combined with `#[rustc_deny_explicit_impl]` (`Sized`) or concrete global/type-checked impls (`TrustedStep` implemented only on concrete primitive/scalar/address types in `core::iter::range`), specializing on `TrustedStep` admits `Copy` as an elaborated supertrait safely without opening `Copy` to arbitrary specialization. `BytewiseEq<Rhs>` demonstrates why root `AlwaysApplicable` impls must avoid duplicate parameters: its separate `Rhs` parameter avoids repeating `Self`, and `[T; N]` still cannot be made const-generic because `[T; N]: BytewiseEq<[U; N]>` repeats `N` in root `parent_args`.
   - `TrustedLen`, `FusedIterator`, and `TrivialClone` carry `TraitSpecializationKind::Marker` (`#[rustc_unsafe_specialization_marker]` on `14210df0e`; `#[unsafe(rustc_allow_lifetime_dependent_specialization)]` on `49d734536` / `058c70105`). `Marker` clauses pass `check_specialization_on` **directly**, **without** elaborating their supertraits (`Iterator`, `Clone`) into `impl2_clauses`. Consequently, `impl<I: TrustedLen> Tr for I` fails (`cannot specialize on trait Iterator`) unless the parent impl already requires `I: Iterator` (matching `alloc::vec::spec_extend::SpecExtend`), and `impl<T: TrivialClone>` requires `T: Clone` on its parent impl.

3. **`default type` / `default impl` Separation & Polymorphic Projection Opacity (`feature_gate.rs`, `project.rs`, `instance.rs`):**
   - `rustc_ast_passes::feature_gate` limits `#![feature(min_specialization)]` strictly to `default fn` items (`self.features.specialization() || (is_fn && self.features.min_specialization())`), rejecting `default type Assoc`, `default const`, and `default impl` with **`E0658`**.
   - Full `#![feature(specialization)]` permits `default type` (`c03`, `FULL_SPEC_ASSOC=42,8`) and `default impl`, while `traits::project` and `ty_utils::instance` keep non-final associated types opaque (`E0308`, `eligible = false`) in `TypingMode::{Typeck, PostTypeckThroughBorrowck, Reflection, PostBorrowck}` until `TypingMode::{PostAnalysis, Codegen}` with `!trait_ref.still_further_specializable()`. Combined with lifetime-erased dispatch, `#![feature(specialization)]` permits unsoundness in safe Rust (modulo the unstable feature gate): live probes `c05b` and `c06` compile cleanly via generic indirection and dispatch `"copy"` plus project `[u64; 4]` (32 bytes) onto non-`Copy` `OnlyStaticCopy<'local>`.

4. **Empirical Execution & Kernel-Checked Mechanization:**
   - All **35** live `rustc 1.98.0-nightly (14210df0e 2026-05-31)` compilation/execution scenarios (`support/probe_min_specialization_soundness.py` -> `support/probe_results.json`, including 4 `-Znext-solver=globally` differential checks) confirm every compiler diagnostic and dispatch behavior listed above.
   - A standalone **2,409-line, 217-theorem** Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) formalization (`support/MinSpecializationAlwaysApplicableAndLifetimeSoundness.lean`, zero `sorry`, zero `Classical.choice`, zero `Quot.sound`, zero `Lean.ofReduceBool`, zero `omega`/`bv_decide`/`native_decide`, zero `partial def`, zero `._unsafe_rec`) kernel-checks: (a) bi-directional equivalence between surface typeck dispatch and lifetime-erased monomorphization dispatch (`min_specialization_surface_equals_monomorphization`), yielding the **Lifetime-Erasure Invariance Theorem** (`lifetime_erasure_invariance_theorem`) and **Zero Soundness Gap** (`zero_typeck_monomorphization_soundness_gap`); (b) specialization-chain acyclicity (`spec_chain_acyclic`) and most-specific-impl uniqueness (`most_specific_impl_unique`); (c) `Copy`/`Clone`/`TrustedLen`/`TrustedStep`/`Sized`/`'static`/(T, T)/constrained-projection decision faithfulness; and (d) counterexamples for `'static` unsoundness, `OnlyStaticCopy<'local>` generic bypass (`c05b`/`c06`), and `default type` typeck opacity necessity (`default_type_typeck_opacity_necessity`).

## Applicability

### Upstream Subjects and Relationships

This report characterizes specialization soundness across seven durable upstream artifacts recorded in `REPORT.json`:

1. **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, commit date `2026-05-31`, LLVM `22.1.6`, host `x86_64-unknown-linux-gnu`):** Examined via direct inspection of compiler and standard-library sources AND live execution of all 35 scenarios in `support/probe_min_specialization_soundness.py` (`support/probe_results.json`).
2. **`rust-lang/rust` at `49d734536222bf28bb6d07d885b3a81d145981da` (commit date `2026-09-11`):** Audited at compiler and core trait-marker sources to track the transition from `#[rustc_unsafe_specialization_marker]` to `#[unsafe(rustc_allow_lifetime_dependent_specialization)]`.
3. **`rust-lang/rust` at `058c701055c4b6f60f622d616afc0349911c38c3` (`main`, commit date `2026-11-24`):** Audited side-by-side against `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` across `min_specialization.rs`, `impl_wf_check.rs`, `collect.rs`, `feature_gate.rs`, `check.rs`, `wfcheck.rs`, `coherence/mod.rs`, `specialize/mod.rs`, `specialization_graph.rs`, `project.rs`, `instance.rs`, `select/mod.rs`, `rustc_next_trait_solver/src/solve/assembly/mod.rs`, `library/core`, and `library/alloc`.
4. **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`main`, commit date `2026-11-19`):** Inspected at `trusted/rustc-capture/src/driver.rs` (pinned toolchain `"1.98.0-nightly (f8a08b688 2026-05-30)"`, `after_analysis` capture gate) and `trusted/lean/Trusted/MirAst.lean` (`noncomputable` TCB discipline and erased-region `MirTy`) to determine which compiler guarantees enter Anneal's MIR capture boundary.
5. **`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`master`, commit date `2026-11-17`):** Checked at `src/items/implementations.md` and `src/glossary.md` to confirm that neither `specialization` nor `min_specialization` is specified in the normative language reference yet.
6. **`rust-lang/rfcs` at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`:** Consulted at `text/1210-impl-specialization.md` for the original `default` item, `default impl`, typeck opacity, and lifetime-blind dispatch design motivations.
7. **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, commit date `2026-09-24`):** Used to kernel-check `support/MinSpecializationAlwaysApplicableAndLifetimeSoundness.lean` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

### Shared Behavior vs. Revision Deltas Across `14210df0e`, `49d734536`, and `058c70105`

The core specialization pipeline—`check_min_specialization` invocation in `impl_wf_check.rs`, all four sub-checks in `check_always_applicable` (`check_has_items`, `check_static_lifetimes`, `check_duplicate_params`, `check_predicates` / `check_specialization_on`), `unconstrained_parent_impl_args` projection filtering, `specializes` omitting `resolve_regions` in Layer 1, `Children::insert` `le == ge` overlap rejection, `feature_gate` separation between `min_specialization` (`default fn` only) and `specialization` (`default type`, `default const`, `default impl`), and non-final associated-type opacity prior to `TypingMode::PostAnalysis`—holds identically across all three `rust-lang/rust` snapshots. Five concrete differences were directly observed in source diffs:

1. **Attribute Rename (`#[rustc_unsafe_specialization_marker]` -> `#[unsafe(rustc_allow_lifetime_dependent_specialization)]`):**
   - `14210df0e` (`2026-05-31`): `collect.rs` L940 checks `find_attr!(attrs, RustcUnsafeSpecializationMarker)`; `trait_def.rs` L94, `min_specialization.rs` L58, `library/core/src/clone.rs` L278 (`TrivialClone`), and `library/core/src/iter/traits/marker.rs` L28 (`FusedIterator`), L65 (`TrustedLen`) use `#[rustc_unsafe_specialization_marker]`.
   - `49d734536` (`2026-09-11`) & `058c70105` (`2026-11-24`): `collect.rs` (`49d734536` L1132 / `058c70105` L1154) checks `find_attr!(attrs, RustcAllowLifetimeDependentSpecialization)`; `check_attr.rs` (`058c70105` L310) validates `AttributeKind::RustcAllowLifetimeDependentSpecialization`; and `core` defines `FusedIterator`, `TrustedLen`, and `TrivialClone` with `#[unsafe(rustc_allow_lifetime_dependent_specialization)]` (`library/core/src/iter/traits/marker.rs` L28, L65; `library/core/src/clone.rs` L278). `TraitSpecializationKind::Marker` semantics and non-elaboration of supertraits remain unchanged.
2. **Additional `AlwaysApplicable` Standard-Library Auto Traits (`Forget`, `Move`):**
   - On `058c70105`, `library/core/src/marker.rs` annotates two unstable auto traits with `#[rustc_specialization_trait]`: `Forget` (L1412–1422, `#[unstable(feature = "forget_trait", issue = "165370")]`) and `Move` (L1439–1449, `#[unstable(feature = "move_trait", issue = "149607")]`), alongside `Sized` (L151), `MetaSized` (L171), and `PointeeSized` (L188) present on both `14210df0e` and `058c70105`. Both `Forget` and `Move` are `unsafe auto trait`s with zero methods whose compiler-synthesized structural auto-impls do not introduce lifetime preconditions.
3. **`rustc_hir_analysis` Typing / Clause API Refactors Inside `min_specialization.rs`:**
   - Diffing `14210df0e` (476 lines) vs. `058c70105` (477 lines) shows purely mechanical API migrations without logic changes: `tcx.predicates_of` -> `tcx.clauses_of` (`unconstrained_parent_impl_args`, `check_predicates`), `GenericArgsRef` -> `GenericArgs`, `!errors.is_empty()` -> `if let TraitErrors::HasErrors(errors) = errors`, `infcx.fully_resolve` -> `infcx.deeply_resolve_via_region_graph`, `ty::TraitPredicate`/`ProjectionPredicate` -> `ty::TraitClause`/`ProjectionClause`, `.emit()` -> `.emit_err()`, `crate::errors` -> `crate::diagnostics`, and an added `ty::ClauseKind::CompressedTrait(..) => unreachable!()` arm in `trait_specialization_kind` (L475).
4. **Const-Trait & Experimental `TrustedStep` / `BytewiseEq` / `TrivialClone` Signatures:**
   - On `14210df0e`, `TrustedStep` is `pub unsafe trait TrustedStep: Step + Copy {}` (`iter/traits/marker.rs` L118); on `058c70105` (`L119`), `TrustedStep` is `pub const unsafe trait TrustedStep: [const] Step + Copy {}` (matching `[const] PartialEq<Rhs> + Sized` on `BytewiseEq` at `library/core/src/cmp/bytewise.rs` L20–21 and `pub const unsafe trait TrivialClone: [const] Clone {}` at `clone.rs` L283).
5. **TypingMode Names & Next-Solver `filter_specialized_impls` Refactor:**
   - In `traits::project` and `ty_utils::instance`, `14210df0e` matches `TypingMode::Analysis { .. } | Borrowck { .. }` (`project.rs` L953–972, `instance.rs` L158–164), whereas `058c70105` renames these variants to `TypingMode::Typeck { .. } | PostTypeckThroughBorrowck { .. } | Reflection | PostBorrowck` while preserving identical opacity until `TypingMode::PostAnalysis | Codegen` (`project.rs` L1056–1077, `instance.rs` L163–172).
   - Meanwhile, `rustc_trait_selection/src/traits/select/mod.rs` (`14210df0e` L2091–2108; `058c70105` L1956–1973) `prefer_lhs_over_victim` mirrors `rustc_next_trait_solver/src/solve/assembly/mod.rs` (`058c70105` L1085–1128) `filter_specialized_impls`, verifying parity under `-Znext-solver=globally`.

### Configuration and Compilation Scope

- All 35 live probes in `support/probe_min_specialization_soundness.py` compiled with `--edition=2024` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `x86_64-unknown-linux-gnu`.
- Parts A (`a01`–`a07`), B (`b01`–`b15`, except `b05b`), and D (`d01`–`d04`, using `-Znext-solver=globally`) exercise `#![feature(min_specialization)]` (with `#![feature(rustc_attrs)]` only for defining custom `#[rustc_specialization_trait]` / `#[rustc_unsafe_specialization_marker]` traits `a04`, `a05`, `b07`, `b08`, and `b08b`'s defining crate, and unstable stdlib features `trusted_step`/`trusted_len`/`trivial_clone` in `a03`/`a07`).
- Part C (`c01`–`c06`) directly contrasts `#![feature(min_specialization)]` (`c01`–`c02`) against `#![feature(specialization)]` (`c03`–`c06`).

## Findings

### 1. Architecture of Rust's Two-Layer Specialization Check

Basis: normative (RFC 1210, `rust-lang/rfcs`) + source (`rustc_trait_selection`, `rustc_hir_analysis`) + execution + derived (Lean mechanization)

Rust splits specialization validation across two distinct compiler phases so that trait selection and coherence remain well-founded even before `#![feature(min_specialization)]`'s stricter soundness pass runs:

```text
  overlapping trait impls (I1, I2)
       │
       ├──[impls_are_allowed_to_overlap -> Permitted (e.g. #[marker])]──▶ skip specialization check
       │
       ▼
  Layer 1: specialization_graph::Children::insert + tcx.specializes (region-BLIND)
       ├── le = tcx.specializes((I1, I2)), ge = tcx.specializes((I2, I1))
       ├── le == ge  ──▶ E0119 (conflict: diamond overlap OR lifetime-only distinction!)
       └── le && !ge ──▶ parent(I1) := I2 in trait specialization tree
                                 │
                                 ▼
  Layer 2: impl_wf_check::check_type_wf -> min_specialization::check_min_specialization
       ├── exempts trait_def.is_marker; checks root impls iff TraitSpecializationKind::AlwaysApplicable
       ├── get_impl_args: translates params & RESOLVES REGIONS (E0477 catches lifetime generalization!)
       └── check_always_applicable:
             1. check_has_items (not empty)
             2. check_static_lifetimes (no 'static in unconstrained parent args)
             3. check_duplicate_params (unconstrained params of impl1 linear, <= 1 occurrence)
             4. check_predicates / check_specialization_on (only parent bounds / WF / global / ConstArgHasType /
                                                           AlwaysApplicable [+ elaborated sups] / Marker [- sups])
```

#### 1.1 Layer 1: `Children::insert` and Region-Blind `specializes` (`specialization_graph.rs`, `specialize/mod.rs`)

In `compiler/rustc_trait_selection/src/traits/specialize/specialization_graph.rs` (`14210df0e` & `058c70105` L76–193), inserting `impl_def_id` under a trait's specialization tree iterates over existing children (`filtered_children`) and queries `traits::overlapping_trait_impls(tcx, possible_sibling, impl_def_id, traits::SkipLeakCheck::Yes, overlap_mode)` (L140–146). If two impls overlap and `tcx.impls_are_allowed_to_overlap` does not permit overlap (i.e., the trait is not `#[marker]`), `Children::insert` computes:

```rust
let le = tcx.specializes((impl_def_id, possible_sibling));
let ge = tcx.specializes((possible_sibling, impl_def_id));

if le == ge { report_overlap_error(overlap, last_lint_mut) } else { Ok((le, ge)) }
```

(`specialization_graph.rs` L158–161). Only four outcomes exist:
- `le && !ge`: `impl_def_id` strictly specializes `possible_sibling` (`Inserted::ShouldRecurseOn`, L164–171).
- `ge && !le`: `impl_def_id` strictly generalizes `possible_sibling` (`Inserted::ReplaceChildren`, L172–179).
- `le == ge == false`: non-chain diamond overlap (neither impl specializes the other, e.g., `[u8; N]` vs. `[T; 4]` intersecting at `[u8; 4]`) -> `report_conflicting_impls` -> **`E0119`**.
- `le == ge == true`: mutual subset modulo regions (e.g., `(&'a u8, &'b u8)` vs. `(&'a u8, &'a u8)`, or `T` vs. `T: 'static`) -> `report_conflicting_impls` -> **`E0119`**.

Why does `le == ge == true` occur whenever two impls differ solely in lifetimes? Inside `compiler/rustc_trait_selection/src/traits/specialize/mod.rs` (`14210df0e` L239–388; `058c70105` L234–376), `specializes(tcx, (specializing_impl, parent_impl))` runs in `TypingMode::non_body_analysis()`, instantiates fresh inference/placeholder args for `parent_impl`, equates the two trait refs via `ocx.eq`, registers `parent_impl`'s predicates via `predicates_for_generics`, and runs `ocx.evaluate_obligations_error_on_ambiguity()`. **Crucially, `specializes` never calls `infcx.resolve_regions` or region outlives verification.** Trait selection ignores region constraints when deciding subset ordering (`must_apply_modulo_regions()` in `select/mod.rs`, matching RFC 1210's modulo-region dispatch invariant), so Layer 1 sees `impl<'a> Tr for (&'a u8, &'a u8)` and `impl<'a, 'b> Tr for (&'a u8, &'b u8)` as indistinguishable, AND sees `impl<T: 'static> Tr for T` as specializing `impl<T> Tr for T` while `impl<T> Tr for T` equally specializes `impl<T: 'static> Tr for T`. Both pairs immediately hit **`E0119`** in Layer 1, **under both `min_specialization` and full `specialization`**.

Conversely, this exact omission of `resolve_regions` in `specializes` creates the asymmetric leak targeted by upstream Rust issue `#79457` (probe `b04`): given `impl<T: 'static> Tr for T` (parent) and `impl<'a> Tr for &'a i32` (child):
- `specializes((child, parent))` (`le`): equates `&'a i32` with `?T`, registers `?T: 'static`, which is a region-outlives obligation skipped by `specializes` -> returns **`true`**!
- `specializes((parent, child))` (`ge`): cannot unify generic `T` with `&'a i32` -> returns **`false`**!
Layer 1 therefore accepts `impl<'a> Tr for &'a i32` as a strict child of `impl<T: 'static> Tr for T`—leaving it to Layer 2's `get_impl_args` to enforce region outlives and emit **`E0477`**.

#### 1.2 Layer 2: `check_min_specialization` Entry, Root Checks, and `get_impl_args` (`min_specialization.rs`)

`compiler/rustc_hir_analysis/src/impl_wf_check.rs` (`14210df0e` & `058c70105` L71–73) runs `check_min_specialization(tcx, impl_def_id)` as part of `check_type_wf` whenever `of_trait && tcx.features().min_specialization()`. Inside `min_specialization.rs` (`058c70105` L83–198):

1. **`parent_specialization_node` (L93–110):** Looks up `trait_def.ancestors(tcx, impl1_def_id)?.nth(1)?`:
   - If `trait_def.is_marker` (`#[marker]`), returns `None` (no specialization check—overlapping marker impls carry zero associated items).
   - If `impl2_node.is_from_trait()` (root impl directly under the trait rather than under a parent impl), returns `None` **UNLESS** `trait_def.specialization_kind == TraitSpecializationKind::AlwaysApplicable` (`#[rustc_specialization_trait]`), in which case it **returns `Some(Node::Trait)`**! Consequently, every impl of a `#[rustc_specialization_trait]`—even a root impl—must itself pass `check_always_applicable` against empty `impl2_clauses = Vec::new()` (L334–337).
2. **`get_impl_args` (`058c70105` L164–198; `14210df0e` L166–200):** Unlike Layer 1's `specializes`, `get_impl_args` creates an `ObligationCtxt` over `param_env = tcx.param_env(impl1_def_id)`, calls `translate_args_with_cause(..., impl1_args, impl2_node, ...)`, checks fulfillment (`evaluate_obligations_error_on_ambiguity`), and **actively resolves and checks regions**:
   ```rust
   let assumed_wf_types = ocx.assumed_wf_types_and_report_errors(param_env, impl1_def_id)?;
   ocx.resolve_regions_and_report_errors(impl1_def_id, param_env, assumed_wf_types)?;
   let Ok(impl2_args) = infcx.deeply_resolve_via_region_graph(impl2_args) else { ... };
   ```
   (`058c70105` L190–196; `14210df0e` uses `infcx.fully_resolve(impl2_args)` at L194). If `impl2` imposes `'static` (e.g. `impl<T: 'static> Tr for T`) while `impl1` supplies non-`'static` `&'a i32`, `resolve_regions_and_report_errors` fails with **`E0477`** (`the type &'a i32 does not fulfill the required lifetime; note: type must satisfy the static lifetime`), closing the Layer 1 loophole (`b04`).
3. **`unconstrained_parent_impl_args` (`14210df0e` L210–248; `058c70105` L208–247):** Scans `impl2`'s predicates (`clauses_of` / `predicates_of`) for `ClauseKind::Projection(proj)` where `proj.projection_term.trait_ref(tcx) != impl_trait_ref`. Generic parameter indices appearing in `proj.term` that are NOT already in `unconstrained_parameters` (collected from projection trait args) are recorded in `constrained_params` and stripped from `impl2_args` before `check_static_lifetimes` and `check_duplicate_params`.
   - **Why this matters (`SpecExtend` / `a02`):** Given parent `impl<T, I: Iterator<Item = T>> SpecCollect<T> for I`, `T` appears twice in `impl2_args = [T, IntoIter<T>]` for child `impl<T> SpecCollect<T> for IntoIter<T>`. Because `T` is constrained by `<I as Iterator>::Item = T`, `unconstrained_parent_impl_args` strips index 0 (`T`), leaving `parent_args = [IntoIter<T>]`, in which `T` occurs **once**. Notice the order of `min_specialization.rs` L229–237: parameters in `proj.projection_term` (`I`) are added to `unconstrained_parameters` first, then free parameters in `proj.term` (`T`) not already marked unconstrained become `constrained_params`, and then parameters in `proj.term` are added to `unconstrained_parameters` for subsequent clauses (`Impl` parameter scoping handles chaining cleanly when projections are ordered accordingly).

#### 1.3 The Four Checks in `check_always_applicable` (L131–135)

`check_always_applicable` runs all four checks with `.and(...)` (so multiple errors aggregate rather than short-circuiting after the first):

1. **`check_has_items` (L137–150):** When `impl2_node` is `Node::Impl(impl2_id)`, rejects specializing impls with zero associated items (`tcx.associated_item_def_ids(impl1_def_id).is_empty()`, yielding `"specialization impl does not specialize any associated items"`, live probe `b12`). Allowing empty specializations without overriding any item creates an ambiguous middle node without behavioral specialization. Note that `Node::Trait` root impls of marker-like `#[rustc_specialization_trait]` traits with no items (`BytewiseEq`, `TrustedFused`, `TrustedStep`) are exempt because `Node::Trait` does not match `if let Node::Impl(impl2_id) = impl2_node`.
2. **`check_static_lifetimes` (L295–304):** Checks `tcx.any_free_region_meets(parent_args, |r| r.is_static())`, rejecting direct `'static` in unconstrained parent arguments with `"cannot specialize on 'static lifetime"` (`StaticSpecialize`, live probe `b03`). Notice `'static` in a constrained position (if forced solely via an unconstrained type whose projection resolves `'static`, or `'static` outside `parent_args`) is governed cleanly by `unconstrained_parent_impl_args` + region checking.
3. **`check_duplicate_params` (L269–285):** Calls `cgp::parameters_for(tcx, parent_args, true)` (collecting every type, lifetime, and const generic parameter index recursively inside `parent_args`, including `rNamed` regions!), sorts the vector, and checks `partition_dedup()`. Any duplicate parameter triggers `"specializing impl repeats parameter \`{param}\`"`—catching BOTH repeated type parameters `impl<T> Tr for (T, T)` (`b09`), repeated lifetime parameters `impl<'a> Tr for (&'a u8, &'a u8)` over `impl<T> Tr for T` (`b10`), AND repeated const parameters `impl<T, U, const N: usize> BytewiseEq<[U; N]> for [T; N]` (`bytewise.rs` L82–84)! Why must linearity hold? Because `(T, T)` and `(&'a u8, &'a u8)` assert equality of two independent sub-positions of `impl2`'s arguments; for `(&'a u8, &'a u8)` over `T`, lifetime erasure strips `'a != 'b`, making `(&'local_1 u8, &'local_2 u8)` indistinguishable from `(&'a u8, &'a u8)` after monomorphization! Even `(T, T)` over `U` indirectly equates any lifetimes embedded inside `T` across both tuple elements (or forces cross-component equality that can interact subtly with variance and region subtyping—for example `(&'a u8, &'b u8)` unifying only up to `'b: 'a` or common sub-region). Linear unconstrained pattern headers guarantee bijective pattern-lifting across region erasure.
4. **`check_predicates` & `check_specialization_on` (L317–457):** Verified below in Section 2.

**Companion HIR/Check Guards:** Outside `min_specialization.rs`, `check/check.rs` enforces:
- `check_specialization_validity` (`14210df0e` L1170–1229; `058c70105` L1227–1286): every parent item overridden by a child impl (or inherited without `default impl` forwarding) must be marked `default`, otherwise emitting **`E0520`** (`b13`).
- `check_impl_items_against_trait` (`14210df0e` L1388–1415; `058c70105` L1445–1472): `default async fn` and `RPITIT` methods in specializing impls are explicitly disallowed (`"async method in trait cannot be specialized"`, `b14` + `E0053`), because lowering generates hidden opaque GATs whose interaction with specialization is unstable.

---

### 2. Why `Copy` Is Rejected While `Sized`/`TrustedStep` and `TrustedLen`/`TrivialClone` Succeed

Basis: source (`rustc_hir_analysis`, `rustc_middle`, `library/core`, `library/alloc`) + execution + derived (Lean mechanization)

This distinction is one of the sharpest structural seams in `rustc` and directly determines what `core` and `alloc` optimizations can use `#![feature(min_specialization)]` safely.

#### 2.1 The Three `TraitSpecializationKind` Tiers (`trait_def.rs`, `collect.rs`)

In `compiler/rustc_middle/src/ty/trait_def.rs` (L89–104) and `compiler/rustc_hir_analysis/src/collect.rs` (`14210df0e` L940–946; `058c70105` L1154–1160):

| `TraitSpecializationKind` | Source Attribute | Root Impl Checked by `check_always_applicable`? | Supertraits Elaborated into `impl2_clauses`? | Soundness Status under `min_specialization` | Concrete `library/core` Examples |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`None`** | *(default)* | No | No | Rejected unless implied by `impl2` or global | **`Copy`**, **`Clone`**, `Default`, `PartialEq`, `Iterator`, `Step` |
| **`AlwaysApplicable`** | `#[rustc_specialization_trait]` | **Yes** (`parent_specialization_node` returns `Some(Node::Trait)`) | **Yes** (`elaborate(tcx, always_applicable_traits)`) | **Sound** (every impl of trait itself proven always-applicable, and feature-gated for manual impls) | **`Sized`**, `MetaSized`, `PointeeSized`, `Forget`, `Move` (`058c70105`), **`TrustedStep`**, `TrustedFused`, `InPlaceIterable`, **`BytewiseEq`** |
| **`Marker`** | `#[rustc_unsafe_specialization_marker]` (`14210df0e`) / `#[unsafe(rustc_allow_lifetime_dependent_specialization)]` (`49d734536`, `058c70105`) | No | **No** | **Explicitly Unsound Shortcut** for item-free marker traits (`min_specialization.rs` L58–66; cannot contain methods, relies on unsafe contract) | **`TrustedLen`**, **`FusedIterator`**, **`TrivialClone`** |

Note also the feature gate in `coherence/mod.rs` `enforce_trait_manually_implementable` (`14210df0e` & `058c70105` L93–102): manually writing an `impl` of any `AlwaysApplicable` trait without `#![feature(specialization)]` or `#![feature(min_specialization)]` fails coherence with `"implementing rustc_specialization_trait traits is unstable"` (verified live in `b08b`), preventing unverified external crates from smuggle-implementing an `AlwaysApplicable` trait with lifetime preconditions!

#### 2.2 Exact Tracing of `check_predicates` and Why `Copy` Emits TWO Errors

Examine `min_specialization.rs` L325–457 step-by-step:

1. **`impl1_clauses` (L325–332):** `traits::elaborate(tcx, tcx.clauses_of(impl1_def_id).instantiate(tcx, impl1_args))` transitively expands every explicit bound on `impl1` to include all its supertrait bounds.
   - For `impl<T: Copy> Tr for T` (`b05`): since `Copy: Clone` (`library/core/src/marker.rs` L454/L455) and `Clone: Sized` (`library/core/src/clone.rs` L194), `impl1_clauses` contains:
     `{ T: Copy, T: Clone, T: Sized, T: MetaSized, T: PointeeSized }`.
2. **`impl2_clauses` (L334–392):** Built from **three** sources:
   - (a) Elaborated clauses of `impl2` (or `Vec::new()` if `impl2_node.is_from_trait()`), instantiated with `impl2_args` (L334–347). For `impl<T> Tr for T`, this gives `{ T: Sized, T: MetaSized, T: PointeeSized }`.
   - (b) Well-formed (`wf::obligations`) clauses of `impl1`'s own trait args (L377–391).
   - (c) **Crucial Always-Applicable Supertrait Rule (L365–392):**
     ```rust
     let always_applicable_traits = impl1_clauses
         .iter().copied()
         .filter(|&(clause, _)| matches!(trait_specialization_kind(tcx, clause), Some(TraitSpecializationKind::AlwaysApplicable)))
         .map(|(c, _)| c);
     ...
     impl2_clauses.extend(traits::elaborate(tcx, always_applicable_traits));
     ```
     Notice `always_applicable_traits` filters **only** for `AlwaysApplicable`, **NOT** `Marker`!
3. **Residual Clause Check (`check_specialization_on`, L395–457):** For every `(clause1, span)` in `impl1_clauses` not equal (`==`) to some `clause2` in `impl2_clauses`, `check_specialization_on` admits ONLY:
   - `clause.is_global()` (ground traits such as `u32: Copy` or `u32: Default`, L412),
   - `TraitSpecializationKind::Marker` (`TrustedLen`, `FusedIterator`, `TrivialClone`, L418–420),
   - `ty::ClauseKind::ConstArgHasType(..)` (`const N: usize`, L441–450 — flagged by upstream `FIXME(min_specialization), FIXME(const_generics)`).
   Everything else—including `TraitSpecializationKind::None` (`"cannot specialize on trait ..."`), `Projection` (`"cannot specialize on associated type ... == ..."`, `b11`), `RegionOutlives` (`T: 'a`), and `TypeOutlives`—is **rejected**.

Applying this exact dataflow yields all four observed behaviors immediately:
- **Why `impl<T: Copy> Tr for T` Fails (`b05`) with TWO Errors:** `Copy` is `TraitSpecializationKind::None` (not `AlwaysApplicable`, not `Marker`), so `always_applicable_traits` skips `T: Copy`, and `impl2_clauses` has only `{ T: Sized, ... }`. When the loop inspects `impl1_clauses`, **both** `T: Copy` and `T: Clone` fail `check_specialization_on`—producing `error: cannot specialize on trait Copy` **and** `error: cannot specialize on trait Clone` (`b05`)!
- **Why `Copy` MUST Be Rejected (`b05b`):** In safe Rust, without any unstable features, a user can write `struct OnlyStaticCopy<'a>(&'a u8); impl Copy for OnlyStaticCopy<'static> {} impl Clone for OnlyStaticCopy<'static> { ... }` (verified cleanly in `b05b`, `compile_rc = 0`, `STATIC_COPY=9,9`). Because `Copy` satisfaction genuinely depends on concrete lifetime `'static` vs. `'local`, admitting `Copy` under `min_specialization` would replicate the `c05b`/`c06` generic bypass in safe Rust!
- **Why `Sized` and `TrustedStep` Pass (`a03`, `a04`):** `Sized` (`#[rustc_specialization_trait]`) is `AlwaysApplicable`, and all its compiler-synthesized builtin impls check structural size independent of lifetimes. More surprisingly, `TrustedStep: Step + Copy` (`library/core/src/iter/traits/marker.rs` L117–119) ALSO has `#[rustc_specialization_trait]`, even though its supertraits `Step` and `Copy` are both `TraitSpecializationKind::None`! That succeeds cleanly for two complementary reasons:
  1. **Consumers (`impl<I: TrustedStep>` over `impl<I>`)**: Because `TrustedStep` is `AlwaysApplicable`, line 365–392 puts `TrustedStep` into `always_applicable_traits`, so `traits::elaborate` adds `I: TrustedStep`, `I: Step`, and **`I: Copy`** (plus `I: Clone`, `I: PartialOrd`, etc.) into `impl2_clauses`! Thus `check_specialization_on` never rejects the elaborated `Copy` bound on the *consumer* impl!
  2. **Producers (Impls of `TrustedStep`)**: Because `parent_specialization_node` returns `Some(Node::Trait)` for every impl of `TrustedStep`, any blanket impl `impl<T: Copy> TrustedStep for T` is checked against empty `impl2_clauses` and **rejected** (`b08` witnesses the exact same rule on `impl<T: Default> SpecMarker for T`: `error: cannot specialize on trait Default`). Instead, `library/core/src/iter/range.rs` (L11–22) implements `TrustedStep` strictly for concrete non-generic scalar/address/char/NonZero types (`u8`..`usize`, `i8`..`i128`, `char`, `AsciiChar`, `Ipv4Addr`, `Ipv6Addr`, `NonZero<...>`), whose `Step` and `Copy` obligations are **global clauses** (`clause.is_global() == true` at L412) independent of any lifetime!
- **Why `TrustedLen` / `FusedIterator` / `TrivialClone` Discriminate Parent Bounds (`a03`, `a07`, `b07`):** Because `Marker` traits (`#[rustc_unsafe_specialization_marker]` / `#[unsafe(rustc_allow_lifetime_dependent_specialization)]`) are **excluded** from `always_applicable_traits` (L370–372), `TrustedLen`'s supertrait `Iterator` (`clone.rs`: `TrivialClone`'s supertrait `Clone`) is **not** added to `impl2_clauses`. Therefore:
  - `impl<I: TrustedLen> Tr for I` over `impl<I> Tr for I` **fails** with `error: cannot specialize on trait Iterator` (`b07`)!
  - `impl<I: TrustedLen> Tr for I` over **`impl<I: Iterator> Tr for I`** **succeeds** (`a03`, `GEN_ITER=iter TL_ITER=trusted_len FUSED=fused`) because `I: Iterator` is already in `impl2_clauses`! This matches production `library/alloc/src/vec/spec_extend.rs` (L13–29, L42–61), where `TrustedLen<Item = T>` specializes `I: Iterator<Item = T>`, and `T: TrivialClone` specializes `T: Clone`. Notice the compiler comment in `min_specialization.rs` L60–66 explicitly marks `Marker` as *"unsound, in the sense that the specialized impl may be used when it doesn't apply, but we allow it in the short term since it can't cause use after frees with purely safe code in the same way as specializing on traits with methods can"*—while `library/core/src/clone.rs` L273–277 documents an extra `SAFETY` invariant on `TrivialClone` specifically noting that `clone` cannot be lifetime-dependent if `Clone` already holds.

---

### 3. `default type` / `default impl` Separation and Projection Opacity

Basis: normative (RFC 1210, `rust-lang/rfcs`) + source (`rustc_ast_passes`, `rustc_trait_selection`, `rustc_ty_utils`) + execution + derived (Lean mechanization)

Under RFC 1210 and `rustc`, `default fn`, `default type`, `default const`, and `default impl` behave asymmetrically across `#![feature(min_specialization)]` and `#![feature(specialization)]`:

#### 3.1 Syntactic Feature Gating (`feature_gate.rs`)

In `compiler/rustc_ast_passes/src/feature_gate.rs`:
1. **`default impl` (`14210df0e` L226–228; `058c70105` L173–175):** Unconditionally gated behind `sym::specialization` (`gate!(self, specialization, i.span, "specialization is experimental")`). Attempting `default impl<T> Tr for T` under `#![feature(min_specialization)]` emits **`E0658`** (`c02`).
2. **Associated `default` items (`14210df0e` L446–455; `058c70105` L392–401):**
   ```rust
   if let ast::Defaultness::Default(_) = i.kind.defaultness() {
       // Limit `min_specialization` to only specializing functions.
       gate_alt!(
           &self,
           self.features.specialization() || (is_fn && self.features.min_specialization()),
           sym::specialization,
           i.span,
           "specialization is experimental"
       );
   }
   ```
   Thus `default fn` passes `#![feature(min_specialization)]`, whereas **`default type Assoc`** and **`default const`** are strictly rejected with **`E0658`** under `min_specialization` (`c01`).

#### 3.2 Projection Opacity Across `TypingMode`s (`project.rs`, `instance.rs`)

Why must associated types marked `default type` remain un-normalizable during type checking, and why do even `#![feature(min_specialization)]` impls fail `E0308` when using `default type` inside generic bodies? Both `compiler/rustc_trait_selection/src/traits/project.rs` (`14210df0e` L939–979; `058c70105` L1042–1084) and `compiler/rustc_ty_utils/src/instance.rs` (`14210df0e` L150–176; `058c70105` L155–176) resolve `specialization_graph::assoc_def(...)` and gate normalization/resolution on `node_item.is_final()` (`leaf_def.is_final()`, i.e., `finalizing_node.is_some()` in `specialization_graph.rs` L378–382):
- If `!node_item.is_final()` (`default type` or `default fn`), projection/resolution is **disabled (`eligible = false`)** during `TypingMode::Coherence`, `TypingMode::Typeck` (`Analysis` on `14210df0e`), `TypingMode::PostTypeckThroughBorrowck` (`Borrowck`), `TypingMode::Reflection`, and `TypingMode::PostBorrowck`.
- It becomes eligible **only** in `TypingMode::PostAnalysis | TypingMode::Codegen` AND **only when `!poly_trait_ref.still_further_specializable()`** (all specialization-discriminating parameters are monomorphically rigid).

The direct consequences (proven necessary in Lean theorem `default_type_typeck_opacity_necessity`) are verified cleanly in `c01`, `c03`, `c04`, and `c06`:
- Inside `impl<T> Tr for T { default type Assoc = (); default fn get(&self) -> Self::Assoc {} }`, typechecking the body sees `Self::Assoc` as **opaque** (`!<T as Tr>::Assoc`), rejecting `()` with **`E0308`** under **both** `min_specialization` (`c01`, emitting `E0658` + `E0308`) and full `specialization` (`c04`, emitting `E0308` with upstream note referencing issue `#152409`, while `-Znext-solver=globally` `d04` emits `E0271` alongside `E0308` + `E0658`).
- Under `#![feature(specialization)]`, concrete monomorphic queries in `PostAnalysis` / codegen (`u8::ASSOC` where `u8` overrides `type Assoc = u64` over `default type Assoc = u32`) **do** project once `!still_further_specializable()` holds (`c03`, `FULL_SPEC_ASSOC=42,8`).
- Under `OnlyStaticCopy<'local>` indirection (`c06`), full `#![feature(specialization)]` uses lifetime-erased dispatch at `PostAnalysis`, selects the specialized `impl<T: Copy> AssocTag for T` (`type Assoc = [u64; 4]`) over `impl<T> AssocTag for T` (`default type Assoc = u16`), and projects `size_of::<T::Assoc>()` to **`32` bytes** (`FULL_SPEC_ASSOC_BYPASS=32`) rather than **`2` bytes** (`u16`), demonstrating why full `specialization`'s lifetime-dependent `default type` projection breaks type preservation after erasure!

#### 3.3 Why Full `#![feature(specialization)]` Fails Type Soundness via Generic Indirection (`c05a`/`c05b`/`c06`)

Under `#![feature(specialization)]`:
- Calling `l_ref.kind()` directly on `let l_ref = OnlyStaticCopy(&local);` triggers **`E0597`** (`local does not live long enough`, `c05a`), because method resolution knows the concrete type `OnlyStaticCopy<'local>` and checks `T: Copy` against `'local`.
- Passing `&l_ref` to `fn dispatch_generic<T: Tag>(x: &T)` (where `impl<T> Tag for T` applies unconditionally for every `T`) requires ONLY `OnlyStaticCopy<'local>: Tag` at the call site, which succeeds with **zero** `Copy` obligation! At monomorphization (`select/mod.rs` / `assembly/mod.rs`), specialization compares `impl<T: Copy> Tag for T` against `impl<T> Tag for T` using erased lifetimes (`ReErased`), concludes `OnlyStaticCopy<ReErased>: Copy` holds (via `impl Copy for OnlyStaticCopy<'static>`), and dispatches to `"copy"` (`c05b`: `FULL_SPEC_BYPASS=static:copy,local:copy`). Blocking `Copy` in `min_specialization` (plus blocking `'static`, `(T, T)`, `default type`, and `TypeOutlives`) is therefore *strictly necessary* to prevent arbitrary lifetime-gated traits from creating this generic dispatch bypass.

---

### 4. Empirical Live `rustc` Probe Matrix (35 Cases, `14210df0e`)

Basis: execution (`support/probe_min_specialization_soundness.py` + `support/probe_results.json`)

Every case below executed cleanly inside `tempfile.TemporaryDirectory()` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`LLVM 22.1.6`, `x86_64-unknown-linux-gnu`):

#### 4.1 Part A: Valid `#![feature(min_specialization)]` Admissions (`a01`–`a07`)

| Case ID | Scenario | `compile_rc` | Verified `stdout` | Compiler Rule Exercised |
| :--- | :--- | ---: | :--- | :--- |
| `a01` | `impl<T>` -> `impl u32` & `impl<T> Vec<T>` (generic + monomorphic dispatch) | `0` | `SPEC_GEN=generic SPEC_U32=u32 SPEC_VEC=vec MONO_GEN=generic MONO_U32=u32` | Linear patterns `[T]`, `u32`, `Vec<T>`, non-empty item |
| `a02` | `impl<T, I: Iterator<Item = T>>` -> `impl<T> SpecCollect<T> for vec::IntoIter<T>` | `0` | `SPEC_EXTEND=iter,into_iter` | `unconstrained_parent_impl_args` eliminates `T` via `Item = T` |
| `a03` | `I: TrustedLen`, `I: FusedIterator` over `I: Iterator`; `T: TrustedStep` & `impl<T>` over `?Sized` | `0` | `GEN_ITER=iter TL_ITER=trusted_len FUSED=fused BOOL_STEP=any U32_STEP=trusted_step UNSIZED=1 SIZED=2` | `Marker` over parent `Iterator`; `AlwaysApplicable` `TrustedStep`, `Sized` |
| `a04` | Custom `#[rustc_specialization_trait] trait AlwaysSup: Copy + Default` + concrete `impl AlwaysSup for i32` | `0` | `ALWAYS_SUP=0,15` | `AlwaysApplicable` supertraits elaborated into `impl2_clauses` |
| `a05` | Custom `#[rustc_specialization_trait] trait MyBytewiseEq<Rhs = Self>: PartialEq<Rhs>` | `0` | `BYTEWISE=true` | Distinct `Rhs` parameter keeps root impl linear (`BytewiseEq` pattern) |
| `a06` | Const-generic chain `[T; N]` -> `[u8; N]` -> `[u8; 4]` | `0` | `CONST_ARR=generic_arr,u8_arr,u8_len4_arr` | `ConstArgHasType` admitted (`min_specialization.rs` L441–450) |
| `a07` | `impl<T: TrivialClone>` over `impl<T: Clone>` | `0` | `TRIVIAL_CLONE=clone,trivial_clone` | `Marker` trait `TrivialClone` valid when parent provides `T: Clone` |

#### 4.2 Part B: Layer 1 & Layer 2 Rejections + `Copy` Counterexample (`b01`–`b15`)

| Case ID | Scenario | `compile_rc` | Error / Output | Enforcing Mechanism |
| :--- | :--- | ---: | :--- | :--- |
| `b01` | `impl<'a, 'b> (&'a u8, &'b u8)` + `impl<'a> (&'a u8, &'a u8)` | `1` | `E0119` | Layer 1 `Children::insert` (`le = ge = true`, region-blind `specializes`) |
| `b02` | `impl<T>` + `impl<T: 'static>` | `1` | `E0119` | Layer 1 `Children::insert` (`le = ge = true`, region-blind `specializes`) |
| `b03` | `impl<T>` -> `impl &'static i32` | `1` | `error: cannot specialize on 'static lifetime` | Layer 2 `check_static_lifetimes` (`min_specialization.rs` L295–304) |
| `b04` | `impl<T: 'static>` -> `impl<'a> &'a i32` (`#79457`) | `1` | `E0477` (`must satisfy the static lifetime`) | Layer 2 `get_impl_args` `resolve_regions_and_report_errors` (`L191`) |
| `b05` | `impl<T>` -> `impl<T: Copy>` | `1` | `cannot specialize on trait Copy` + `cannot specialize on trait Clone` | Layer 2 `traits::elaborate` expands `Copy: Clone`; both `None` (`L325–432`) |
| `b05b` | `struct OnlyStaticCopy<'a>(&'a u8); impl Copy for OnlyStaticCopy<'static>` | `0` | `STATIC_COPY=9,9` | Proves `Copy` can depend on `'static` in safe Rust |
| `b06` | `impl<T>` -> `impl<T: Clone>` | `1` | `cannot specialize on trait Clone` | Layer 2 `Clone` is `TraitSpecializationKind::None` |
| `b07` | `impl<T>` (no `Iterator` bound) -> `impl<T: TrustedLen>` | `1` | `cannot specialize on trait Iterator` | `Marker` does **not** elaborate `TrustedLen: Iterator` (`L365–392`) |
| `b08` | `#[rustc_specialization_trait] trait SpecMarker` with `impl<T: Default>` | `1` | `cannot specialize on trait Default` | Root impl of `AlwaysApplicable` checked with empty `impl2_clauses` |
| `b08b` | Cross-crate manual `impl AuxSpecTrait for Local` without feature gate | `1` | `implementing rustc_specialization_trait traits is unstable` | `coherence/mod.rs` `enforce_trait_manually_implementable` (`L93–102`) |
| `b09` | `impl<T> Tr for T` -> `impl<T> Tr for (T, T)` | `1` | `specializing impl repeats parameter T` | Layer 2 `check_duplicate_params` (`L269–285`) |
| `b10` | `impl<T> Tr for T` -> `impl<'a> Tr for (&'a u8, &'a u8)` | `1` | `specializing impl repeats parameter 'a` | Layer 2 `cgp::parameters_for(..., true)` catches repeated `'a` |
| `b11` | `impl<I, V: Id<This = (I,)>>` | `1` | `cannot specialize on associated type <V as Id>::This == (I,)` | Layer 2 `check_specialization_on` rejects `ClauseKind::Projection` (`L434`) |
| `b12` | `impl<T> Tr for T` -> `impl Tr for u32 {}` | `1` | `specialization impl does not specialize any associated items` | Layer 2 `check_has_items` (`L137–150`) |
| `b13` | `impl<T> Tr for T { fn f }` (no `default`) -> `impl Tr for u32` | `1` | `E0520` | `check_specialization_validity` (`check.rs` L1170–1229 / `058c` L1227–1286) |
| `b14` | `trait AsyncTr { async fn f }` with `default async fn` | `1` | `E0053` + `async method in trait cannot be specialized` | `check.rs` (`L1388–1415` / `058c` `L1445–1472`) |
| `b15` | `impl<const N: usize> ArrTag for [u8; N]` + `impl<T> ArrTag for [T; 4]` | `1` | `E0119` (`conflicting implementations ... for [u8; 4]`) | Layer 1 `Children::insert` diamond (`le = ge = false`) |

#### 4.3 Part C & Part D: `default type` Separation, Full Specialization Exploit, and `-Znext-solver=globally`

| Case ID | Scenario & Mode | `compile_rc` | Error / Output | Rule Verified |
| :--- | :--- | ---: | :--- | :--- |
| `c01` | `default type Assoc = ()` + `fn get() -> Self::Assoc {}` under `min_specialization` | `1` | `E0658`, `E0308` | `feature_gate.rs` rejects `default type` + `project.rs` hides non-final projection |
| `c02` | `default impl<T> Tr for T` under `min_specialization` | `1` | `E0658` | `feature_gate.rs` L226/L173 restricts `default impl` to `specialization` |
| `c03` | `default type Assoc = u32` overridden by `type Assoc = u64` under `specialization` | `0` | `FULL_SPEC_ASSOC=42,8` | Full `specialization` resolves rigid `PostAnalysis` projections |
| `c04` | `impl<T> Tr for T { default type Assoc = (); fn get() -> Self::Assoc {} }` under `specialization` | `1` | `E0308` | Non-final `default type` remains opaque during `Typeck` (`#152409`) |
| `c05a` | Direct `l_ref.kind()` on `OnlyStaticCopy(&local)` (`specialization`) | `1` | `E0597` | Concrete borrowck requires `'static` when resolving directly |
| `c05b` | Generic `dispatch_generic(&l_ref)` (`specialization`) | `0` | `FULL_SPEC_BYPASS=static:copy,local:copy` | Dispatches `Copy` impl onto non-`Copy` `OnlyStaticCopy<'local>` after region erasure |
| `c06` | Generic `AssocTag` size bypass via `OnlyStaticCopy(&local)` (`specialization`) | `0` | `FULL_SPEC_ASSOC_BYPASS=32` | Projects `[u64; 4]` (`32` bytes) instead of `u16` (`2` bytes) onto non-`Copy` type |
| `d01` | Valid `min_specialization` (`a01`) under `-Znext-solver=globally` | `0` | `NS_VALID=generic,u32` | Next solver matches legacy solver selection (`assembly/mod.rs` L1085) |
| `d02` | `impl<T: Copy>` under `-Znext-solver=globally` | `1` | `cannot specialize on trait Copy` + `Clone` | `check_min_specialization` identical |
| `d03` | `(&'a u8, &'b u8)` vs. `(&'a u8, &'a u8)` under `-Znext-solver=globally` | `1` | `E0119` | Next solver Layer 1 specialization check matches legacy |
| `d04` | `default type` (`c01`) under `-Znext-solver=globally` | `1` | `E0658`, `E0308`, `E0271` | Next solver adds `E0271` type mismatch on opaque projection |

---

### 5. Kernel-Checked Lean `v4.34.1` Formalization

Basis: derived (`support/MinSpecializationAlwaysApplicableAndLifetimeSoundness.lean`) + execution (Lean `v4.34.1` kernel)

`support/MinSpecializationAlwaysApplicableAndLifetimeSoundness.lean` (`2,409` lines, `97,922` bytes, `846` local constants, `484` `noncomputable def`s, `217` proved theorems) mechanizes the specialization-graph DAG, `check_always_applicable`, lifetime-erased dispatch, and counterexamples using strictly constructive kernel logic (`ALL_AXIOMS_USED=[propext]`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `sorry`, `0` `Lean.ofReduceBool`, `0` `omega`/`bv_decide`/`native_decide`, `0` `partial def`, `0` `._unsafe_rec`).

#### 5.1 Pattern-Lifting & `StrictAlwaysApplicableImpl` Equivalence

1. **Commutativity (`instTy_erase_commutes`, L568):** For all ground substitutions `σ : Subst` and surface type patterns `t : Ty`, region erasure commutes unconditionally with instantiation:
   `eraseRegions (instTy σ t) = instErasedPat (eraseSubst σ) (erasePatRegions t)`.
2. **Constructive Linearity + `'static`-Freedom Soundness (`linearNoStaticCheck_sound` & `linearNoStatic_lift_subst_exact`, L680, L1166):** Whenever `LinearNoStaticPat p` holds (no `'static`, no duplicate type vars `NoDup (collectTyVars p)`, no duplicate named region vars `NoDup (collectRegVars p)`, and no duplicate const vars `NoDup (collectConstVars p)`), if `erasePatRegions p` matches `eraseRegions g` under an erased substitution `τ`, then there exists a ground substitution `σ` matching `instTy σ p = g` whose erased variable assignments equal `τ.tySubst v` for every `VarId` `v`. Intuitively, because each variable position in `p` is independent (no shared constraints between subtrees) and every region parameter is unconstrained and distinct, any ground lifetime occurring in `g` can be lifted back into `σ.regSubst` and `σ.tySubst` without conflict.
3. **Bi-Directional Impl Applicability (`strict_impl_surface_iff_erased` & `strict_impl_applicability_erasure_invariant`, L1431, L1462):** Under `SoundAlwaysApplicableRegistry reg` (requiring `.alwaysApplicable` traits and their elaborated supertraits to depend strictly on `eraseRegions g`), any `StrictAlwaysApplicableImpl` satisfies:
   - `ImplAppliesSurface reg imp g ↔ ImplAppliesErased reg imp (eraseRegions g)`, and
   - `eraseRegions g₁ = eraseRegions g₂ → (ImplAppliesSurface reg imp g₁ ↔ ImplAppliesSurface reg imp g₂)`.

#### 5.2 Specialization-Graph Ordering & Flagship Erasure-Invariance Theorems

1. **Preorder, Strict Antisymmetry, and Chain Acyclicity (L1479–1678):** Defining `SpecializesModuloRegions` (`∀ e, ImplAppliesErased reg i₁ e → ImplAppliesErased reg i₂ e`) and `StrictSpec` (`SpecializesModuloRegions i₁ i₂ ∧ ¬ SpecializesModuloRegions i₂ i₁`), Lean proves `strictSpec_irrefl`, `strictSpec_asymm`, `specializes_trans`, `strictSpec_trans_left`, `spec_chain_acyclic`, and **`most_specific_impl_unique`** (any two maximal applicable impls in an `IsSpecializationChain` must be equal).
2. **`Children::insert` Conflict Theorems (L1523–1625, L2354):**
   - `lifetime_eq_pairs_trigger_e0119` (`b01`) and `static_bound_triggers_e0119` (`b02`): both yield mutual `SpecializesModuloRegions` (`le = ge = true`) -> `.conflictE0119`.
   - `diamond_non_chain_conflict_e0119` (`b15`): `[u8; N]` (`implArrU8N`) and `[T; 4]` (`implArrT4`) both apply to `[u8; 4]`, yet neither specializes the other (`¬ SpecializesModuloRegions implArrU8N implArrT4 ∧ ¬ SpecializesModuloRegions implArrT4 implArrU8N`) -> `.conflictE0119`.
   - `issue_79457_generalize_lifetimes_layer1_blind_layer2_reject` (`b04`): proves `implRefA` (`&'a i32`) satisfies `SpecializesModuloRegions stdRegistry implRefA implBlanketStaticBound` (passing Layer 1 modulo regions!) while violating `groundTyAllStatic (&'local_1 i32) = false`.
3. **Flagship Theorem (`min_specialization_surface_equals_monomorphization`, L1741) & `lifetime_erasure_invariance_theorem` (L1772):** Across any `AllStrictAlwaysApplicable reg chain`:
   - `DispatchesSurface reg fallback chain g res ↔ DispatchesErased reg fallback chain (eraseRegions g) res`,
   - Any two ground types `g₁, g₂` sharing `eraseRegions g₁ = eraseRegions g₂` produce **identical** dispatch tags `r₁ = r₂`, and
   - `zero_typeck_monomorphization_soundness_gap` (L1789): whenever monomorphization selects an `AlwaysApplicable` specializing impl `imp` on `eraseRegions g`, all surface bounds and header matches of `imp` genuinely hold on the pre-erasure type `g`.

#### 5.3 Formal Standard-Library Classification & Unsoundness Counterexamples

- **`copy_and_clone_rejected_under_min_specialization` (L1978):** Proves `checkAlwaysApplicableBool stdRegistry [] true implCopySpec = false`, and both `.traitVar tidCopy 0` and `.traitVar tidClone 0` fail `checkClauseAllowed`.
- **`sized_and_trusted_step_admitted` (L1990):** Proves `checkAlwaysApplicableBool stdRegistry [] false implSizedSpec = true` and `checkAlwaysApplicableBool stdRegistry [] false implTrustedStepSpec = true`, faithfully modeling supertrait elaboration of `TrustedStep`'s `Step + Copy` bounds.
- **`trusted_len_marker_supertrait_discrimination` (L2000):** Proves `implTrustedLenSpec` and `implTrivialCloneSpec` **fail** against `parentBounds = []` (`b07`) and **pass** when the parent supplies `[.traitVar tidIterator 0]` / `[.traitVar tidClone 0]` (`a03`, `a07`).
- **`layer2_rejection_and_constrained_projection_witnesses` (L2079):** Proves rejection of `(T, T)`, `(&'a u8, &'a u8)`, `&'static i32`, and empty `{}` impls, plus admission of constrained-projection `IntoIter<T>`.
- **`ce_static_specialization_unsound_after_erasure` (L2097):** Proves ¬∃ `f : ErasedTy → Nat` factoring `[implStaticRef, implBlanket]` surface dispatch through `eraseRegions`, since `&'static i32` dispatches to `32` while `&'local_1 i32` dispatches to `10` with identical `eraseRegions`.
- **`ce_only_static_copy_generic_bypass_unsound` (L2143) & `full_spec_default_type_lifetime_copy_bypass_witness` (L2385):** Formalizes live probes `c05b` and `c06`: `OnlyStaticCopy<'local_1>` violates `Copy`, yet `DispatchesErased` selects `implCopySpec` (`20`) and `resolveAssocSize .postAnalysis implCopySpec false` projects `[u64; 4]` (`some 32`) while `resolveAssocSize .typeck implDefaultTypeBlanket false = none`.
- **`default_type_and_impl_rejected_under_min_specialization` (L2214) & `default_type_typeck_opacity_necessity` (L2260):** Proves no polymorphic typeck resolver assigning `some 2` to `implDefaultTypeBlanket` can agree with child `implCopySpec` (`some 32`), forcing `typeckGuess = none`.

---

### 6. Implications for Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Basis: source (`joshlf/anneal`, `rust-lang/rust`) + derived

1. **Capture Boundary Placement (`trusted/rustc-capture/src/driver.rs` L25, L75–84, L145–150):** Anneal pins `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"`, hooks `Callbacks::after_analysis`, and fails closed unless `tcx.dcx().has_errors().is_none()` and `rustc_driver::run_compiler` finishes without fatal/late errors. Because `check_min_specialization` runs inside `impl_wf_check::check_type_wf` and `specialization_graph_of` runs inside `coherent_trait`—both before `after_analysis` yields an error-free crate—any crate compiling cleanly under `#![feature(min_specialization)]` satisfies Layer 1 and Layer 2 checks before Anneal's MIR capture begins.
2. **Marker-Trait Escape Hatch Sensitivity:** Under `#![feature(min_specialization)]`, crates utilizing stdlib traits carrying `TraitSpecializationKind::Marker` (`TrustedLen`, `FusedIterator`, `TrivialClone`—whose safety rests on `#[rustc_unsafe_specialization_marker]` / `#[unsafe(rustc_allow_lifetime_dependent_specialization)]` rather than mechanical always-applicability) **can** pass `check_min_specialization` even if a hypothetical manual impl depended on lifetimes. However, as `min_specialization.rs` L58–66 notes, `Marker` traits cannot carry methods (`impl` bodies can only exist inside `rustc`-internal `core`/`alloc` crates for `TrustedLen`/`TrivialClone`, all gated by `unsafe trait` safety contracts).
3. **Full `#![feature(specialization)]` Exclusion (`trusted/lean/Trusted/MirAst.lean` L75–92, L304–321):** Because `MirTy` intentionally erases lifetimes (`MirTy.ref (regionless)`), capturing crates that enable unrestricted `#![feature(specialization)]` (`c05b`/`c06`) would inherit `rustc`'s region-erasure dispatch unsoundness (`OnlyStaticCopy<'local>` dispatching `Copy`). Requiring verified targets to forbid `#![feature(specialization)]` (admitting only stable coherence or `#![feature(min_specialization)]` strictly constrained to `AlwaysApplicable` traits) preserves the `zero_typeck_monomorphization_soundness_gap` property across `MirTy` region erasure.

## Boundaries

Negative space is documented explicitly under `reference-corpus/1`:

1. **`#![feature(min_specialization)]` Soundness Proof Status in Upstream `rustc` (`unknown` beyond modeled subset / `not examined` for `const` generic parameter types):** As documented verbatim at `compiler/rustc_hir_analysis/src/impl_wf_check/min_specialization.rs` L441–450, allowing all `ClauseKind::ConstArgHasType(..)` clauses carries an open upstream `FIXME(min_specialization), FIXME(const_generics)` warning regarding generic const parameter types (`<T, const N: T>`). Additionally, `check_predicates` assumes any trait carrying `#[rustc_specialization_trait]` is globally always-applicable; our Lean theorem proves erasure invariance conditional on `SoundAlwaysApplicableRegistry` (which assumes standard-library unsafe contracts on `TrustedStep`, `Sized`, etc., hold soundly). Interaction with `#![feature(min_specialization)]` + `#![feature(generic_const_exprs)]` or `adt_const_params` was **not examined**.
2. **`TraitSpecializationKind::Marker` Escape Hatch Soundness (`known not to apply` to `StrictAlwaysApplicableImpl`):** As `min_specialization.rs` L58–66 states explicitly, `TraitSpecializationKind::Marker` (`#[rustc_unsafe_specialization_marker]` / `#[unsafe(rustc_allow_lifetime_dependent_specialization)]`) intentionally bypasses lifetime-dependence soundness in `check_specialization_on` (`min_specialization.rs` L415–420) for item-free marker traits (`FusedIterator`, `TrustedLen`, `TrivialClone`). Therefore our flagship `lifetime_erasure_invariance_theorem` holds for `StrictAlwaysApplicableImpl` (`allowMarker = false`) and is **known not to apply** to arbitrary user-defined `Marker` impls with lifetime bounds.
3. **Live Binary Execution on `49d734536` and `058c70105` (`not examined` by execution):** All 35 live probes ran against `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)`. Behavior of `49d734536` and `058c70105` (specifically the attribute rename to `#[unsafe(rustc_allow_lifetime_dependent_specialization)]` and `Forget`/`Move` markers) is established via direct source inspection (`source`) rather than executing a `2026-09` or `2026-11` nightly binary.
4. **Other Specialized Standard-Library Containers (`Vec::spec_from_elem`, `slice::SpecOrd`, `Rc::from`, `TrustedRandomAccess`) (`not examined` by execution):** While `SpecExtend` (`a02`), `TrustedLen`/`FusedIterator`/`TrustedStep`/`Sized` (`a03`), `BytewiseEq` (`a05`), and `TrivialClone` (`a07`) were executed directly or modeled from `library/core` and `library/alloc`, runtime codegen/benchmarking of other stdlib internal specializations (e.g., `TrustedRandomAccessNoCoerce`, `SpecArrayEq`, `Pin`) was **not examined**.
5. **Const Evaluation (`const fn` Specialization / `[const]` Trait Bounds on `058c70105`) (`not examined`):** Although `specializes` checks `tcx.is_conditionally_const` (`specialize/mod.rs` L348–380 on `14210df0e`) and `058c70105` makes `TrustedStep` and `TrivialClone` `const unsafe trait`s, specializing `const fn` trait methods under `#![feature(const_trait_impl)]` + `#![feature(min_specialization)]` was **not examined** in live probes or Lean proofs.
6. **Negative Impls (`!Trait`) Interaction with Specialization and `default const` Execution (`not examined` / `unsupported` in `min_specialization`):** `default const` is gated symmetrically with `default type` in `feature_gate.rs` L393/L447 (`E0658`, verified by source), while explicit `default const` probes and negative impl (`with_negative_coherence`) interactions inside specialization trees were **not examined**.
7. **Stand-Alone Lean Formalization Boundaries (`known not to apply` to full Rust IR):** `support/MinSpecializationAlwaysApplicableAndLifetimeSoundness.lean` is a standalone model (it does not import `joshlf/anneal`'s `Trusted.MirAst`) focusing on linear patterns, `Subst`/`ErasedSubst`, `Clause` subsets, `SpecializesModuloRegions` DAGs, and associated-type opacity across `TypingMode::typeck` vs. `postAnalysis`. It does not formalize higher-ranked lifetimes (`for<'a>`), variance/subtyping lattices, associated-type normalization cycles, or `impl_restriction` visibility rules. Moreover, the normative `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`) still treats specialization as **unsupported** (absent from `items/implementations.md`).

## Evidence

All primary-source inspections, live `rustc` executions, and Lean `v4.34.1` kernel checks recorded below were acquired and verified on `2026-11-24`.

### 1. Upstream Primary Sources (Pinned 40-Hex Commits)

#### `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `49d734536222bf28bb6d07d885b3a81d145981da`, `058c701055c4b6f60f622d616afc0349911c38c3`)

| File Path | Key Symbols & Findings | `14210df0e` Lines | `49d734536` Lines | `058c70105` Lines |
| :--- | :--- | :--- | :--- | :--- |
| `compiler/rustc_hir_analysis/src/impl_wf_check.rs` | `check_type_wf` calls `check_min_specialization(tcx, impl_def_id)` when `of_trait && tcx.features().min_specialization()` | L13, L60–75 | — | L13, L60–75 |
| `compiler/rustc_hir_analysis/src/impl_wf_check/min_specialization.rs` | `check_min_specialization`, `parent_specialization_node` (checks root impls of `AlwaysApplicable`), `check_always_applicable`, `check_has_items`, `get_impl_args` (`resolve_regions_and_report_errors`), `unconstrained_parent_impl_args`, `check_duplicate_params`, `check_static_lifetimes`, `check_predicates`, `check_specialization_on`, `trait_specialization_kind` | L1–476 (spec: L85–475; `Marker` comment: L58–66; `ConstArgHasType` `FIXME`: L441–450) | L1–478 (`rustc_allow_lifetime_dependent_specialization`) | L1–477 (API refactor `clauses_of` / `GenericArgs` / `TraitClause`) |
| `compiler/rustc_trait_selection/src/traits/specialize/specialization_graph.rs` | `Children::insert` (`impls_are_allowed_to_overlap`, `le`/`ge`, `if le == ge`), `assoc_def` (`LeafDef`, `finalizing_node`) | L76–193, L352–410 | L76–193, L352–410 | L76–193, L352–410 |
| `compiler/rustc_trait_selection/src/traits/specialize/mod.rs` | `specializes` (`TypingMode::non_body_analysis()`, skips region resolution, `is_conditionally_const`), `report_conflicting_impls` (`E0119`) | L239–388, L472–598 | L237–379, L520–620 | L234–376, L517–617 |
| `compiler/rustc_hir_analysis/src/collect.rs` | `trait_def` collects `TraitSpecializationKind::{Marker, AlwaysApplicable, None}` | L940–946 | L1132–1138 | L1154–1160 |
| `compiler/rustc_hir_analysis/src/coherence/mod.rs` | `enforce_trait_manually_implementable` rejects manual `AlwaysApplicable` impls without feature gate | L44, L93–102 | L44, L93–102 | L44, L93–103 |
| `compiler/rustc_hir_analysis/src/check/check.rs` | `check_specialization_validity` (`E0520`), `default async fn` / `RPITIT` ban | L1170–1229, L1388–1415 | L1204–1265, L1410–1445 | L1227–1286, L1445–1472 |
| `compiler/rustc_hir_analysis/src/check_attr.rs` | Validates `AttributeKind::RustcAllowLifetimeDependentSpecialization` and `RustcSpecializationTrait` | — | — | L310, L385 |
| `compiler/rustc_ast_passes/src/feature_gate.rs` | `default impl` gated to `specialization`; `default` assoc items gated to `specialization() \|\| (is_fn && min_specialization())` | L226–228, L446–455 | — | L173–175, L392–401 |
| `compiler/rustc_middle/src/ty/trait_def.rs` | `enum TraitSpecializationKind { None, Marker, AlwaysApplicable }` | L89–104 | L89–104 | L89–104 |
| `compiler/rustc_trait_selection/src/traits/project.rs` | Projection eligibility for `!node_item.is_final()`: hidden in `Typeck`/borrowck, enabled in `PostAnalysis` if `!still_further_specializable()` | L939–979 | L1025–1065 | L1042–1084 |
| `compiler/rustc_ty_utils/src/instance.rs` | Associated-item resolution eligibility for `!leaf_def.is_final()`, `defaultness.is_final()` | L150–176, L243 | — | L155–176, L250 |
| `compiler/rustc_trait_selection/src/traits/select/mod.rs` | `prefer_lhs_over_victim` (`must_apply_modulo_regions()` + `tcx.specializes`) | L2091–2108 | L2044–2061 | L1956–1973 |
| `compiler/rustc_next_trait_solver/src/solve/assembly/mod.rs` | `filter_specialized_impls` (`has_only_region_constraints` + `impl_specializes`) | — | — | L1085–1132 |
| `library/core/src/marker.rs` | `Sized` (`AlwaysApplicable`), `MetaSized`, `PointeeSized`, `Copy: Clone` (`None`), plus `Forget` & `Move` (`AlwaysApplicable` on `058c70105`) | L150–193, L452–456 | L150–194, L453–457 | L151–194, L453–457, L1412–1449 |
| `library/core/src/clone.rs` | `Clone: Sized` (`None`), `TrivialClone: [const] Clone` (`Marker` + `#[marker]`, attribute rename) | L194, L273–283 | L194, L273–283 | L194, L273–283 |
| `library/core/src/iter/traits/marker.rs` | `TrustedFused`, `FusedIterator`, `TrustedLen` (`Marker` attribute rename), `InPlaceIterable`, `TrustedStep: Step + Copy` (`AlwaysApplicable`) | L11–13, L27–32, L64–67, L90–92, L116–118 | L11–13, L27–32, L64–67, L90–92, L116–118 | L11–13, L27–32, L64–67, L90–92, L117–119 |
| `library/core/src/iter/range.rs` | `unsafe_impl_trusted_step!` instantiates `TrustedStep` only on concrete scalar/char/`NonZero`/IP types | — | — | L11–22 |
| `library/core/src/cmp/bytewise.rs` | `BytewiseEq<Rhs = Self>` (`#[rustc_specialization_trait]`) doc comment on separate `Rhs` and const-generic `[T; N]` duplicate-param rejection | — | — | L10–23, L74–85 |
| `library/alloc/src/vec/spec_extend.rs` | `SpecExtend` specializations using `Iterator<Item = T>`, `TrustedLen<Item = T>`, `IntoIter<T>`, `Clone`, and `TrivialClone` | — | — | L9–61 |

#### `joshlf/anneal`, `rust-lang/reference`, `rust-lang/rfcs`, and `leanprover/lean4`

- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/rustc-capture/src/driver.rs` L25 (`COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"`), L75–84 (`Callbacks::after_analysis`, `tcx.dcx().has_errors().is_none()`), L137–150 (`run_compiler` gate); `trusted/lean/Trusted/MirAst.lean` L75–92 (`noncomputable` TCB requirement suppressing `._unsafe_rec`), L312–321 (`MirTy`, erasing region lifetimes).
- `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/items/implementations.md` L142–174 (`items.impl.trait.coherence`—specialization unspecified); `src/special-types-and-traits.md` L92–198 (`Copy`, `Clone`, `Sized`).
- `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/1210-impl-specialization.md` L256–355 (`Hazard: interactions with type checking`), L992–1297 (`Interaction with lifetimes` / modulo-region dispatch), L1298–1423 (`Default impls`).
- `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`): strict single-file kernel verification of the Lean formalization (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, exit code `0`).

### 2. Preserved Package Support Artifacts

1. **`support/probe_min_specialization_soundness.py`** (`913` lines, `26,955` bytes): Self-contained Python probe runner executing inside `tempfile.TemporaryDirectory()` using `--edition=2024`, compiling an auxiliary `aux_spec_trait` rlib for cross-crate `rustc_specialization_trait` gating (`b08b`) and compiling/running all 35 scenarios across Parts A, B, C, and D (`-Znext-solver=globally`), scrubbing temporary working directories, home paths, and compiler sysroots before writing JSON.
2. **`support/probe_results.json`** (`240` lines, `21,804` bytes): Recorded live output of `probe_min_specialization_soundness.py` executed against `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65 2026-05-31)` (LLVM `22.1.6`, `x86_64-unknown-linux-gnu`), `total_cases = 35`.
3. **`support/MinSpecializationAlwaysApplicableAndLifetimeSoundness.lean`** (`2,409` lines, `97,922` bytes): Standalone kernel-checked Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) formalization verified with exit code `0`, zero warnings, `846` local constants, `484` `noncomputable def` declarations, `217` proved theorems, `0` `sorry`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`, `0` `omega`/`bv_decide`/`native_decide`, `0` `partial def`, and `0` `._unsafe_rec` constants (`ALL_AXIOMS_USED=[propext]` in Lean MetaM audit).

## Revalidation

To test whether these compiler behaviors and formal invariants still hold on a newer `rustc` toolchain, another host target, or a newer Lean 4 release:

### 1. Re-Run the 35-Case Live `rustc` Probe (~4 seconds)

From this package directory:

```bash
python3 support/probe_min_specialization_soundness.py --out /tmp/min_spec_reval.json
```

Verify these key discriminators against `support/probe_results.json`:
- `a01`–`a07`: all exit `0` (`compile_rc == 0`, `run_rc == 0`, matching stdout tags).
- `b01`, `b02`, `b15`: all fail `compile_rc == 1` with `E0119` (Layer 1 specialization graph).
- `b03`, `b04`, `b05`, `b06`, `b07`, `b08`, `b08b`, `b09`, `b10`, `b11`, `b12`: all fail `compile_rc == 1` (`b04` -> `E0477`; `b05` -> 2 errors mentioning `Copy` and `Clone`; `b07` -> `Iterator`; `b09`/`b10` -> `specializing impl repeats parameter`).
- `b05b`: exits `0` (`STATIC_COPY=9,9`), confirming lifetime-dependent `Copy` remains valid in safe Rust.
- `c01` (`E0658`, `E0308`), `c02` (`E0658`), `c03` (`FULL_SPEC_ASSOC=42,8`), `c04` (`E0308`), `c05a` (`E0597`), `c05b` (`FULL_SPEC_BYPASS=static:copy,local:copy`), `c06` (`FULL_SPEC_ASSOC_BYPASS=32`).
- `d01`–`d04` (`-Znext-solver=globally`): `d01` (`NS_VALID=generic,u32`), `d02` (Copy + Clone), `d03` (`E0119`), `d04` (`E0271`, `E0308`, `E0658`). Note that `#![feature(rustc_attrs)]` helper probes (`a04`, `a05`, `b07`, `b08`, `b08b`) in newer compilers after `49d734536` require `#[unsafe(rustc_allow_lifetime_dependent_specialization)]` if custom `Marker` traits are added.

### 2. Re-Verify the Lean `v4.34.1` Formalization (~3 seconds)

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/MinSpecializationAlwaysApplicableAndLifetimeSoundness.lean
```

Exit code `0` with empty output confirms all 217 theorems and 484 definitions kernel-check cleanly without warnings, `sorry`, or non-constructive axioms.

### 3. Diff Primary Upstream Compiler Seams Before Upgrading

When advancing `rust-lang/rust` past `058c701055c4b6f60f622d616afc0349911c38c3` or updating `joshlf/anneal`'s pinned nightly, diff:
- `compiler/rustc_hir_analysis/src/impl_wf_check/min_specialization.rs` (especially `parent_specialization_node`, `get_impl_args`, `unconstrained_parent_impl_args`, `check_predicates`, `check_specialization_on`, and `FIXME(min_specialization)` on `ConstArgHasType`),
- `compiler/rustc_trait_selection/src/traits/specialize/{specialization_graph.rs, mod.rs}` (`Children::insert`, `specializes`),
- `compiler/rustc_trait_selection/src/traits/project.rs` & `compiler/rustc_ty_utils/src/instance.rs` (non-final `is_final()` / `still_further_specializable()` gates), and
- `library/core/src/{marker.rs, clone.rs, iter/traits/marker.rs, cmp/bytewise.rs}` (any trait adding `#[rustc_specialization_trait]` or `#[unsafe(rustc_allow_lifetime_dependent_specialization)]`).
