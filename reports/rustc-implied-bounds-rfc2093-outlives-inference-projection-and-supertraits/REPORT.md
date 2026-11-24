# Implied Bounds, RFC 2093 Outlives Inference, Supertrait Elaboration, and Projection Normalization in `rustc`

## Summary

`rustc` resolves lifetime and trait obligations across generics through four tightly coupled, sharply partitioned subsystems whose boundaries explain why superficially similar declarations either compile silently or fail with `E0310`, `E0309`, `E0277`, or `E0284`:

1. **Function/impl implied bounds vs. RFC 2093 item-header outlives inference are distinct mechanisms with disjoint lifetime filters and item coverage.**
   - **Implied bounds** (`rustc_ty_utils::implied_bounds::assumed_wf_types` feeding `compute_implied_outlives_bounds_inner`) assume well-formedness (`TyWF`) for `inputs_and_output` of `Fn`/`AssocFn`, `trait_ref.args.types()` of trait `Impl`s, and `[Self]` of inherent `Impl`s, while returning empty lists for `Struct`/`Enum`/`Union`/`Trait`/`TraitAlias`/normal `TyAlias` and forwarding only the parent impl's assumed-WF types for non-RPITIT `AssocTy` (omitting the associated type's own RHS `= &'a T`). Crucially, `implied_bounds_from_components` extracts **both** early-bound regions and `'static` (`ty::ReStatic`) without applying `is_free_region`, while discarding all non-outlives clauses such as `ClauseKind::Trait` (`E0277` on `struct NeedEq<T: PartialEq>(T); impl<T> NeedEq<T>`).
   - **RFC 2093 implicit outlives inference** (`rustc_hir_analysis::outlives::inferred_outlives_of`) applies **only** to local `Struct`, `Enum`, `Union`, checked `TyAlias` (`type_alias_is_lazy` under `14210df0e` / `type_alias_is_checked` under `058c70105`), and `AnonConst` param defaults under `generic_const_exprs`. It iterates to a fixed point guarded by `tcx.recursion_limit()` over **unnormalized** field types (`skip_norm_wip()`), consulting `GlobalInferredOutlives` plus explicit ADT/trait bounds, decomposing `push_outlives_components`, and filtering RHS **and** region LHS targets through `is_free_region` (`outlives/utils.rs`). Because `is_free_region` returns `true` **only** for `ty::ReEarlyParam(_)` and `false` for **both** `ty::ReStatic` (`'static`) and `ty::ReBound(..)` (`for<'b>`), `fn f<T>(&'static T)` and `impl<T> Tr for &'static T` infer `T: 'static` via implied bounds whereas `struct StaticRef<T>(&'static T)` infers nothing (`[]`) and fails WF checking with `E0310`.
   - Furthermore, RFC 2093 emits `<T as Trait>::Assoc: 'a` for `Component::Alias` inside `&'a <T as Trait>::Assoc` rather than descending into `T: 'a` (`E0309` if `T: 'a` is subsequently needed), drops projections containing escaping late-bound regions (`Component::EscapingAlias`), and never normalizes field projections through trait `impl`s (causing RFC 2093 Example 4, `struct Holder<'a, T>(<Vec<T> as MakeRef<'a>>::Type)`, to fail with `E0309`).

2. **Supertrait elaboration filters trait-header predicates by `PredicateFilter::SelfAndAssociatedTypeBounds`, excluding non-`Self` type-parameter outlives bounds (`trait Tr<'a, T: 'a>`).**
   - `rustc_type_ir::elaborate::Elaborator` (`elaborate.rs`) expands only **positive** `ClauseKind::Trait` obligations (leaving negative bounds, `RegionOutlives`, `Projection`, and `WellFormed` unelaborated; decomposing `TypeOutlives` via `push_outlives_components`; and suppressing `Sized` expansion unless `.elaborate_sized()` is set).
   - When `Filter::All` is active on a normal `trait` item, `explicit_implied_predicates_of` (`predicates_of.rs:637-650` in `14210df0e`) / `explicit_implied_clauses_of` (`clauses_of.rs:625-638` in `058c70105`) passes `PredicateFilter::SelfAndAssociatedTypeBounds`, NOT `PredicateFilter::All` (which is reserved for `trait Alias<'a, T: 'a> = ...`). Consequently, `trait Tr<'a>: 'a` (`Self: 'a`) and `trait Tr<'a> { type Assoc: 'a; }` elaborate `X: 'a` and `X::Assoc: 'a` into generic callers `X: Tr<'a>`, whereas `trait Tr<'a, T: 'a> {}` does **not** elaborate `T: 'a` into `fn caller<'a, T, X: Tr<'a, T>>` (`E0309`). Switching `Tr` to a trait alias `trait Alias<'a, T: 'a> = ...` compiles cleanly.

3. **Associated-type projection normalization enforces a total candidate priority order (`ParamEnv > TraitDef > Object > Impls`) and deduplicates identical `ParamEnv` candidates.**
   - `opt_normalize_projection_term` -> `project` (`rustc_trait_selection/src/traits/project.rs`) assembles `ProjectionCandidateSet` in strict priority order. Identical candidates in `ProjectionCandidateSet::Single` deduplicate (`if current == &candidate { return false; }` at `project.rs:106`), so consistent diamond supertraits (`trait Both: Left + Right` where both bound `Base<Item = u32>`) normalize deterministically to `u32`. Conflicting `ParamEnv` bounds (`Base<Item = u32>` vs `Base<Item = i32>`) collapse to `ProjectionCandidateSet::Ambiguous`, yielding `ProjectionError::TooManyCandidates` -> `Ok(None)` -> deferred inference variable -> `E0284`. Deep normalization runs *before* `compute_implied_outlives_bounds_inner`, enabling normalized function inputs (e.g., `<T as Id>::Out` when `T: Id<Out = &'a U>`) to supply implied outlives (`U: 'a`).

4. **Upstream source drift from `14210df0e` (`2026-05-31`) to `058c70105` (`2026-11-24`), classic-vs-`-Znext-solver` differential checks (`39/39` live `rustc` cases), and a zero-`sorry`, zero-`._unsafe_rec` Lean `v4.34.1` mechanization (`2,519` LOC, `120` theorems) confirm all invariants.**
   - Downstream consumer `joshlf/anneal` (`c131b320e`, `Trusted/MirAst.lean:304-321`) captures post-cleanup monomorphic MIR after all outlives checking, region inference, and projection normalization have discharged and erased region variables; therefore Anneal's soundness relies on `rustc`'s front-end typeck/borrowck discharge rather than re-modeling un-erased lifetimes in MIR.

Basis: source + execution + derived + normative + documentation

---

## Applicability

This report documents the behavior, invariants, failure modes, and formal properties of the following pinned systems and revisions (all six immutable 40-hex commit pins and all 36 cited file paths plus 4 path-move negative controls verified against upstream repositories via `support/verify_pins.py`):

| Subject | Repository | Immutable Revision | Role in Report |
| :--- | :--- | :--- | :--- |
| Installed `rustc` & source baseline | `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly 2026-05-31`) | Primary line-level source audit target and live execution host for all 39 empirical compiler probes (classic solver and `-Znext-solver`). |
| Upstream `rust-lang/rust` snapshot | `rust-lang/rust` | `058c701055c4b6f60f622d616afc0349911c38c3` (`2026-11-24`) | Differential source audit verifying renames (`Predicate -> Clause`, `lazy -> checked_type_aliases`, `clauses_of.rs`, moved `implied_outlives_bounds.rs`), dyn-compatibility pre-checks, and structural preservation of core semantics. |
| Language & trait RFCs | `rust-lang/rfcs` | `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | Normative/design baseline for RFC 2093 (`text/2093-infer-outlives.md`) and RFC 1214 (`text/1214-projections-lifetimes-and-wf.md`). |
| Rust Reference | `rust-lang/reference` | `ad35aca481751a06afeb23820a672b0f3b11a476` (submodule pin at `14210df0e`) | Surface documentation cross-check for trait bounds, lifetime elision, and associated items. |
| Anneal verifier trusted computing base | `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`) | Downstream consumer boundary (`Trusted.MirAst` region erasure and `TrustedBoundary` axiom/syntax constraints; pinned nightly string `1.98.0-nightly (f8a08b688 2026-05-30)` in `driver.rs:25`). |
| Lean 4 proof checker & kernel | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel verification toolchain checking `support/ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness.lean` and MetaM `.olean` auditor `support/ImpliedBoundsRfc2093Audit.lean`. |

Scope conditions and qualifications:
- **Both old solver (default) and `-Znext-solver`**: All primary source analyses explicitly distinguish paths shared across both solvers (`inferred_outlives_of`, `assumed_wf_types`, `Elaborator`, `compute_implied_outlives_bounds_inner`, `explicit_implied_clauses_of`) from classic-solver normalization machinery (`opt_normalize_projection_term` asserts `!selcx.infcx.next_trait_solver()` at `project.rs:306`) and differential `-Znext-solver` diagnostics tested directly on `rustc 1.98.0-nightly (14210df0e)`.
- **Unstable feature flags**: Behavior specific to `#![feature(lazy_type_alias)]` (renamed `checked_type_aliases` in `058c70105`), `#![feature(trait_alias)]`, `#![feature(rustc_attrs)]` (`#[rustc_dump_inferred_outlives]`), `#![feature(generic_const_exprs)]`, and `-Znext-solver` is explicitly labeled; default stable compilation excludes unchecked type aliases from both `inferred_outlives_of` and `enter_wf_checking_ctxt` false-global-bound checking (`wfcheck.rs:170-171`).
- **Lean mechanization fidelity**: The Lean `v4.34.1` formalization is a pure, constructive (`[Quot.sound, propext]`, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`) AST and operational model mirroring `rustc`'s data structures and control flow; it verifies mathematical soundness, completeness, separation, and confluence theorems over that modeled calculus rather than compiling and running inside `rustc` itself.

Basis: source + execution + documentation

---

## Findings

### Architectural Partition: Where Outlives and Trait Bounds Originate

`rustc` splits generic well-formedness assumptions into two mechanisms that run on **disjoint** `DefKind` sets, apply **different** lifetime filters, and handle **non-outlives** bounds asymmetrically. Misinterpreting one mechanism as an instance of the other produces the signature `E0310`, `E0309`, `E0277`, and `E0284` diagnostics observed in real crates.

```
                     +-----------------------------------------------+
                     | HIR Item (DefId) during rustc_hir_analysis    |
                     +-----------------------+-----------------------+
                                             |
          +----------------------------------+----------------------------------+
          |                                                                     |
          v                                                                     v
DefKind::Struct | Enum | Union |                                   DefKind::Fn | AssocFn | Impl
checked TyAlias | AnonConst (GCE)                                  | AssocTy(RPITIT) | AssocTy(plain)
          |                                                                     |
          v                                                                     v
[RFC 2093] inferred_outlives_of                                    [WF Implied Bounds] assumed_wf_types
- Walks UNNORMALIZED field tys                                     - Fn/AssocFn: inputs_and_output
- Fixed-point iter over crate                                      - Trait Impl: trait_ref.args.types()
- Uses is_free_region():                                           - Inherent Impl: [Self]
    ReEarlyParam => true                                           - Plain AssocTy: parent only (NO RHS!)
    ReStatic     => FALSE (E0310!)                                 - Deeply normalized BEFORE extraction
    ReBound      => FALSE                                          - Keeps TypeOutlives & RegionOutlives
- Emits <T as Tr>::Assoc: 'a for                                     ONLY (keeps ReStatic -> no E0310!)
  Component::Alias (NOT T: 'a)                                     - Drops ClauseKind::Trait -> E0277
```

The complete per-`DefKind` matrix across both mechanisms (combining `compiler/rustc_hir_analysis/src/outlives/mod.rs:11-47`, `compiler/rustc_ty_utils/src/implied_bounds.rs:23-163`, and `compiler/rustc_hir_analysis/src/collect/predicates_of.rs:619-650` / `clauses_of.rs:607-638`) is:

| Item / `DefKind` | `inferred_outlives_of` (RFC 2093) | `assumed_wf_types` (Implied WF Types) | Outlives / Trait Clauses Propagated to Definition or Callers | Live Probe Outcome |
| :--- | :--- | :--- | :--- | :--- |
| `Struct` / `Enum` / `Union` | **Active** (`outlives/mod.rs:16-19`) | `&[]` (`implied_bounds.rs:134-139`) | Infers `T: 'a`, `'b: 'a`, `<T as Tr>::Assoc: 'a` for `ReEarlyParam`; **excludes** `ReStatic` (`E0310`) & `ReBound`; trait bounds `T: PartialEq` are **never** inferred into impls. | `struct_ref_rfc2093_ok` PASS; `struct_static_ref_no_outlives_e0310` `E0310`; `struct_where_not_implied_in_impl_e0277` `E0277` |
| `TyAlias` (default / `#[rustc_unchecked_type_alias]`) | `&[]` (`mod.rs:20`, `type_of.rs:520-537` / `572-600`) | `&[]` (`implied_bounds.rs:139`) | Neither RFC 2093 inference nor `check_false_global_bounds` (`wfcheck.rs:170-171`) runs on the alias definition itself; `'static` / missing bounds are ignored until instantiation. | `type_alias_unchecked_ok` PASS; `type_alias_unchecked_static_ok` PASS |
| `TyAlias` (`lazy_type_alias` / `checked_type_aliases` or TAIT `OpaqueDef`) | **Active** (`mod.rs:20-23`) | `&[]` | Infers `T: 'a` for `&'a T`; rejects `&'static T` without `T: 'static` via `E0310`. | `type_alias_lazy_checked_early_ok` PASS; `type_alias_lazy_checked_static_e0310` `E0310` |
| `Fn` | `&[]` | `liberated_sig.inputs_and_output` (`implied_bounds.rs:26-33`) | Signature **inputs and return type** supply implied `TypeOutlives` / `RegionOutlives` including `ReStatic` (normalized first via `deeply_normalize`). | `fn_implied_ref_ok`, `fn_implied_return_ok`, `fn_implied_static_ref_ok` PASS |
| `AssocFn` | `&[]` | `parent` assumed WF types `++ inputs_and_output` (`implied_bounds.rs:34-44`) | Inherits parent `impl`/`trait` assumed-WF types plus its own signature types. | `struct_ref_impl_inherits_rfc2093_ok` PASS |
| `Impl { of_trait: false }` (Inherent `impl`) | `&[]` | `[Self]` (`implied_bounds.rs:51-53`) | Normalizes `[Self]`, queries `wf::unnormalized_obligations(Self)`, collects `TypeOutlives`/`RegionOutlives` (including RFC 2093 inferred bounds on `Self`!), discards `ClauseKind::Trait`. | `struct_ref_impl_inherits_rfc2093_ok` PASS; `struct_where_not_implied_in_impl_e0277` `E0277` |
| `Impl { of_trait: true }` (Trait `impl`) | `&[]` | `trait_ref.args.types()` (`implied_bounds.rs:48-50`) | `Self` and all trait type arguments (e.g., `&'static T` in `impl<T> Tr for &'static T`) supply implied outlives, including `T: 'static`. | `trait_impl_for_ref_requires_wf_ok`, `impl_for_static_ref_ok` PASS |
| `AssocTy` (plain non-RPITIT) | `&[]` | `assumed_wf_types(local_parent(def_id))` (`implied_bounds.rs:127-129`) | **Does NOT include its own RHS** (`type Out = &'a T;`): without `T: 'a` in impl/trait header, RHS WF check fails with `E0309`. | `assoc_type_ref_missing_outlives_e0309` `E0309` |
| `AssocTy` (RPITIT `opt_rpitit_info` Some) | `&[]` | Trait: `assumed_wf_types(fn_def_id)` with `ReLateParam -> ReEarlyParam`; Impl: rebased RPITIT + `impl` assumed WF types (`implied_bounds.rs:58-126`) | Remaps liberated late-bound regions from the trait method onto the synthesized opaque GAT so RPITIT bounds mirror fn signatures. | Observed in source (`implied_bounds.rs:58-126`) |
| `Trait` | `&[]` | `&[]` (`implied_bounds.rs:137`) | Header type params do not imply `T: 'a` via `assumed_wf_types`; callers elaborate ONLY `PredicateFilter::SelfAndAssociatedTypeBounds` (`predicates_of.rs:647` / `clauses_of.rs:635`), excluding `T: 'a` on non-`Self` parameters! | `trait_method_caller_missing_implied_e0309` `E0309`; `trait_param_bound_not_implied_by_filter_e0309` `E0309`; `trait_self_outlives_elaborates_ok`, `trait_assoc_outlives_elaborates_ok` PASS |
| `TraitAlias` | `&[]` | `&[]` (`implied_bounds.rs:138`) | Uses `PredicateFilter::All` (`predicates_of.rs:645` / `clauses_of.rs:633`), so `T: 'a` on `trait Alias<'a, T: 'a> = ...` **does** elaborate to callers. | `trait_alias_all_filter_elaborates_ok` PASS |
| `AnonConst` (`generic_const_exprs` param default) | Delegates to parent `inferred_outlives_of` (`mod.rs:24-44`) | `&[]` (`implied_bounds.rs:132`) | Forwards parent ADT outlives bounds so const default body ParamEnv sees `'b: 'a`. | Observed in source (`outlives/mod.rs:24-44`) |

Basis: source + execution + normative

---

### RFC 2093 Implicit Outlives Inference (`rustc_hir_analysis::outlives`)

#### Crate-Wide Fixed-Point Algorithm and Terminating Bound

`inferred_outlives_of` (`compiler/rustc_hir_analysis/src/outlives/mod.rs:11-47`) queries `inferred_outlives_crate`, which runs `implicit_infer::infer_predicates` (`implicit_infer.rs:12-108`) in `14210df0e` (renamed `infer_clauses` in `058c70105`). Key algorithmic properties directly observed in `implicit_infer.rs`:

1. **Initialization & Iteration (`implicit_infer.rs:17-87`)**: Allocates a mutable `ExplicitPredicatesMap` (`explicit.rs:8-64`) and an empty `global_inferred_outlives: FxIndexMap<DefId, EarlyBinder<'_, RequiredPredicates<'_>>>`. In an unbounded loop `for i in 0..` (`L23`), it scans every `id in tcx.hir_free_items()` (`L27`), recomputing `item_required_predicates` for each `Struct`/`Enum`/`Union` field (`adt_def.all_fields()`, `L38`) and each checked `TyAlias` (`L59`), calling `insert_required_predicates_to_be_wf` (or `insert_required_clauses_to_be_wf`).
2. **Monotone Growth & Recursion-Limit Guard (`L79-105`)**: An item enters `predicates_added` (`clauses_added`) iff `item_required_predicates.len() > item_predicates_len` (`L82`). If `predicates_added.is_empty()` (`L89`), the fixed point is reached (`break`). Otherwise, `tcx.recursion_limit().value_within_limit(i)` (`L92`) aborts with `"overflow computing implied lifetime bounds"`.
3. **Why Non-Termination Would Be Unbounded Otherwise**: Because `insert_required_predicates_to_be_wf` runs `ty.walk()` and instantiates inferred bounds into nested ADT instantiations (`Ref<'a, &'b T>` or nested wrapper chains that double or nest lifetimes), without a type-size cap or recursion limit an infinitely growing wrapper chain adds fresh inferred obligations; our Lean formalization explicitly models both this finite-universe convergence theorem (`rfc2093_fixpoint_terminates`) and the syntactic depth-growth counterexample (`nestedRefChain_size`).

Note an important architectural detail in `explicit.rs:30-60`: `ExplicitPredicatesMap` populates **only** explicit `ClauseKind::TypeOutlives` and `ClauseKind::RegionOutlives` predicates (`L33-51`) filtered through `insert_outlives_predicate`, explicitly ignoring `ClauseKind::{Trait, Projection, ConstArgHasType, WellFormed, ConstEvaluatable, UnstableFeature, HostEffect}` (`L52-58`). This is the root syntactic reason that `struct Outer<U>(Inner<U>)` where `struct Inner<U: 'static>` propagates `U: 'static` during check (`check_explicit_predicates` does run `insert_outlives_predicate`, which then drops `ReStatic`!), whereas `Trait` bounds never propagate at all.

Basis: source + derived

#### Field Traversal Rules and Absence of Normalization

`insert_required_predicates_to_be_wf` (`implicit_infer.rs:110-228`) walks **unnormalized** `field_ty = tcx.type_of(field_def.did).instantiate_identity().skip_norm_wip()` (`L46`, note NO `deeply_normalize` call!) via `ty.walk()` (`L118`):

- **Lifetimes & Consts (`L124`)**: `GenericArgKind::Lifetime(_) | GenericArgKind::Const(_)` are skipped directly (`continue`); `ty.walk()` still visits constituent types inside constants if any.
- **`ty::Ref(region, rty, _)` (`L128-135`)**: Calls `insert_outlives_predicate(tcx, rty.into(), region, span, required_predicates)`. Note `&'a &'b u32` emits `('b: 'a)` via recursive `Component::Region` handling (`utils.rs:40-59`).
- **`ty::Adt(def, args)` (`L137-155`) & `ty::Alias(ty::Free { def_id }, args)` (`L157-176`)**: Invokes **both** `check_inferred_predicates` (from `global_inferred_outlives` computed in prior rounds, `L303-324`) **and** `check_explicit_predicates(..., IgnorePredicatesReferencingSelf::No)` (`L248-276`). Thus mutual recursion across structs/enums converges monotonically (`struct_mutual_rec_fixpoint_ok`: `Inner<'a, T>` -> `Outer<'a, T>` <-> `Either<'a, T>`).
- **`ty::Dynamic(obj, ..)` (`L178-205`)**: If `obj.principal()` exists, substitutes `tcx.types.trait_object_dummy_self` for `Self` and calls `check_explicit_predicates` with `IgnorePredicatesReferencingSelf::Yes` (`L202`). This avoids leaking `trait_object_dummy_self` (`implicit_infer.rs:187-195` explicitly notes it also drops `Self: 'a` and `Self::AssocTy: 'b` bounds). Crucially, RFC 599/1156 default trait-object lifetime resolution runs **during HIR type lowering before** RFC 2093 (`rfc2093_runs_after_default_object_bound`: `InferredRef<'a, dyn Dummy>` defaults `dyn Dummy` to `dyn Dummy + 'static`, failing `InferredRef(x)` for `'a dyn Dummy` with `returning this value requires that 'a must outlive 'static`; adding an explicit `struct ExplicitRef<'a, T: 'a>(&'a T)` shifts the default to `+'a`, tested passing in `explicit_outlives_changes_default_object_bound_ok`).
- **`ty::Alias(ty::Projection { def_id }, args)` (`L207-220`)**: Calls `check_explicit_predicates` ONLY on `tcx.parent(def_id)` (the **defining trait**), explicitly omitting bounds on the associated type itself (`implicit_infer.rs:209-211`) and performing **zero** normalization through trait `impl`s.
  - Observed empirical proof (`struct_proj_unnormalized_impl_e0309`): defining `trait MakeRef<'a> { type Type; }` and `impl<'a, T: 'a> MakeRef<'a> for Vec<T> { type Type = &'a T; }`, `struct Holder<'a, T> { field: <Vec<T> as MakeRef<'a>>::Type }` (RFC 2093 Example 4) emits **two** `E0309` errors (`the parameter type T may not live long enough`) because `inferred_outlives_of(Holder)` sees no explicit `T: 'a` on `MakeRef<'a>` and never normalizes `<Vec<T> as MakeRef<'a>>::Type` to `&'a T`.
- **`ty::Alias(ty::Inherent { .. })` (`L222-223`)**: Empty (`FIXME(inherent_associated_types)`), emitting nothing.

Basis: source + execution + documentation

#### `push_outlives_components` and Why `is_free_region` Rejects `'static` (`E0310`)

The single most counterintuitive RFC 2093 rule—and a frequent surprise when reading signatures vs struct headers—lies in `compiler/rustc_hir_analysis/src/outlives/utils.rs:14-183`:

1. `insert_outlives_predicate` (`insert_outlives_clause` in `058c70105`, `utils.rs:23`) begins with:
   ```rust
   if !is_free_region(outlived_region) {
       return;
   }
   ```
   And the same guard runs on `GenericArgKind::Lifetime(r)` (`L134-136`).
2. `is_free_region` (`utils.rs:146-182` in both `14210df0e` and `058c70105`) matches `region.kind()` as follows:
   - `ty::ReEarlyParam(_) => true` (`L156`): named lifetime parameters on the item header (e.g., `'a` in `struct Ref<'a, T>`).
   - `ty::ReStatic => false` (`L164`): `'static` is intentionally rejected (*"These correspond to `T: 'static` relationships which can be rather surprising."*).
   - `ty::ReBound(..) => false` (`L174`): late-bound lifetimes inside `for<'b> fn(&'b T)` binders cannot name header parameters and are skipped.
   - `ty::ReError(_) => false` (`L176`): error recovery.
   - `ReErased | ReVar(..) | RePlaceholder(..) | ReLateParam(..) => bug!(...)` (`L179-181`): invariant asserting only AST/header/binder regions appear in type declarations.
3. For types (`GenericArgKind::Type(ty)`), `utils.rs:36-130` calls `push_outlives_components` (`rustc_type_ir/src/outlives.rs:56-274`):
   - `Component::Param(param_ty)` emits `Param: outlived_region`.
   - `Component::Alias(alias_ty)` (`Component::Alias(is_rigid, alias_ty)` in `058c70105`) **stops descending into `ty`'s subtrees** (`rustc_type_ir/src/outlives.rs:152-159`) and emits `AliasTy: outlived_region` verbatim (e.g., `<T as Id>::Out: 'a`). Thus `struct Wrap<'a, T: Id>(&'a <T as Id>::Out)` infers **only** `<T as Id>::Out: 'a` (`PROJ_ASSOC_OUTLIVES_OK=1`), **never** `T: 'a` (`struct_proj_rejects_param_outlives_e0309`: calling `req_outlives::<'a, T>()` inside `fn check_param<'a, T: Id>(_: Wrap<'a, T>)` fails with `E0309`).
   - `Component::EscapingAlias(_)` (`utils.rs:111-126`): if `alias_ty.has_escaping_bound_vars()` (e.g., `for<'b> fn(<&'b T as Iterator>::Item)`), `push_outlives_components` pushes `Component::EscapingAlias` and `utils.rs` **discards** it completely, deferring WF checking to call sites (`L111-125`).
   - **`ty::FnDef(_, args)` quirk (`rustc_type_ir/src/outlives.rs:84-100`)**: `OutlivesCollector` ignores shallow lifetime args on `FnDef` while descending type/const args (*"HACK(eddyb) ignore lifetimes found shallowly in `args`"*).

Direct compiler inspection via `#[rustc_dump_inferred_outlives]` (`outlives/dump.rs:6-30`, probe `rustc_dump_inferred_outlives_oracle`) verifies the exact output emitted by `tcx.inferred_outlives_of`:

| Rust Declaration Probed | `#[rustc_dump_inferred_outlives]` Output (`rustc 1.98.0-nightly 14210df0e`) | Root Code Cause |
| :--- | :--- | :--- |
| `struct Ref<'a, T>(&'a T);` | `note: T: 'a` | `ty::Ref(ReEarlyParam('a), Param(T))` -> `is_free_region('a) = true` |
| `struct StaticRef<T: 'static>(&'static T);` | *(empty — zero notes)* | `is_free_region(ReStatic) = false` (`utils.rs:164`) |
| `struct Wrap<'a, T: Id>(&'a <T as Id>::Out);` | `note: <T as Id>::Out: 'a` | `Component::Alias` stops subtree descent (`outlives.rs:152-159`, `utils.rs:86-109`) |
| `struct FnHolder<T>(for<'b> fn(&'b T));` | *(empty — zero notes)* | `is_free_region(ReBound('b)) = false` (`utils.rs:174`) |
| `struct Outer<'a, T> { inner: Inner<'a, T> }` (where `Inner` wraps `&'a T`) | `note: T: 'a` | `infer_predicates` fixed point propagates `Inner` bounds (`implicit_infer.rs:140-146`) |
| `enum Either<'a, T> { A(&'a T), B(T) }` | `note: T: 'a` | `adt_def.all_fields()` walks all enum variants (`implicit_infer.rs:38`) |
| `struct NestedStatic<U: 'static>(StaticRef<U>);` | *(empty — zero notes)* | `check_explicit_predicates` runs `insert_outlives_predicate`, which drops `ReStatic` |
| `#![feature(lazy_type_alias)] type CheckedAlias<'a, T> = &'a T;` | `note: T: 'a` | `type_alias_is_lazy` triggers `inferred_outlives_of` (`mod.rs:20-23`, `type_of.rs:520-537`) |

Look carefully at row 2 (`StaticRef<T: 'static>(&'static T)`) and row 7 (`NestedStatic`): even **explicitly written** `T: 'static` is stripped from `inferred_outlives_of` because `explicit.rs` calls `insert_outlives_predicate` (where `is_free_region(ReStatic) == false`). Explicit `T: 'static` lives in `explicit_predicates_of` / `predicates_of`, so omitting explicit `T: 'static` on either `struct StaticRef<T>(&'static T)` (`struct_static_ref_no_outlives_e0310`) or a wrapper `struct Wrapper<U>(StaticRef<U>)` (`struct_nested_static_ref_e0310`) fails WF check with **`E0310`**. Meanwhile, because `type_alias_unchecked_static_ok` (`type StaticAlias<T> = &'static T;` without `lazy_type_alias`) returns `&[]` and skips WF checking (`wfcheck.rs:170-171`), unchecked type aliases allow `&'static T` unguarded until instantiation—whereas enabling `#![feature(lazy_type_alias)]` immediately triggers `E0310` (`type_alias_lazy_checked_static_e0310`).

Basis: source + execution + normative

---

### Function Signatures, Impls, `wfcheck`, and `compute_implied_outlives_bounds_inner`

#### `assumed_wf_types` vs. `enter_wf_checking_ctxt` Execution Pipeline

Whereas RFC 2093 inspects item definitions (`Struct`/`Enum`/`Union`/checked `TyAlias`), function bodies, trait impls, inherent impls, and associated items receive implied bounds from **`rustc_ty_utils::implied_bounds::assumed_wf_types`** (`implied_bounds.rs:23-163`), consumed inside **`rustc_hir_analysis::check::wfcheck::enter_wf_checking_ctxt`** (`wfcheck.rs:154-223` in `14210df0e`; `158-226` in `058c70105`):

1. **Fulfillment of Item's Own Obligations (`wfcheck.rs:176-181`)**: `f(&mut wfcx)?` checks item types and signatures (using `wf::unnormalized_obligations` via `ObligationCtxt`). `wfcx.evaluate_obligations_error_on_ambiguity()` reports non-region trait/projection errors first (`L178-181`).
2. **Assumed-WF Normalization (`wfcheck.rs:183`, `engine.rs:309-343`)**: `wfcx.ocx.assumed_wf_types_and_report_errors(param_env, body_def_id)` iterates over `(ty, span) in tcx.assumed_wf_types(def_id)`. Crucially, `engine.rs:329-338` **comments out `// implied_bounds.insert(ty);`** (`FIXME(@lcnr): ... #100910`) and **deeply normalizes** `ty` under `(cause, param_env)` before inserting `normalized` into the `FxIndexSet` of assumed-WF types!
   - Consequence confirmed live in `normalized_sig_implies_inner_outlives_ok`: given `trait Id<'a> { type Out; }` and `fn f<'a, U, T: Id<'a, Out = &'a U>>(_: T::Out)`, deeply normalizing `<T as Id<'a>>::Out` produces `&'a U`, allowing `compute_implied_outlives_bounds_inner` to imply `U: 'a` (`NORM_IMPLIED_OK=1`).
3. **Outlives Environment Construction (`wfcheck.rs:190-213`, `regions.rs:24-70`)**: `OutlivesEnvironment::new_with_implied_bounds_compat` takes `param_env` type-outlives bounds (normalized under `-Znext-solver` at `regions.rs:35-45`), higher-ranked assumptions via `elaborate_outlives_assumptions`, and **`infcx.implied_bounds_tys(...)`** (`outlives_bounds.rs:105-115` -> canonical `ImpliedOutlivesBounds` query -> `compute_implied_outlives_bounds_inner`). Notice `wfcheck.rs:190-219` tries first with `disable_implied_bounds_hack = true` and falls back to `false` only if errors remain (for legacy `bevy_ecs::ParamSet` detection).
4. **Extracting Outlives Bounds — and Dropping Trait Bounds (`implied_outlives_bounds.rs:51-170` in `14210df0e`; `45-125` in `058c70105`)**: `compute_implied_outlives_bounds_inner` pushes `[ty, normalized_ty]` onto worklist `wf_args` (`L89`) and repeatedly queries `wf::unnormalized_obligations(ocx.infcx, param_env, arg, ...)` (`L100`), deeply normalizing each predicate (`L104-110`) and dispatching on `pred`:
   - `ClauseKind::{Trait, HostEffect, ConstArgHasType, Projection, ConstEvaluatable, UnstableFeature}` and `Subtype/Coerce/DynCompatible/ConstEquate/Ambiguous/NormalizesTo/AliasRelate` (**`L117-129`**): **explicitly dropped `{}`**!
   - `ClauseKind::WellFormed(term)` (**`L132-134`**): pushes `term` onto `wf_args` for recursive decomposition (note: in `wfcheck`, this picks up field obligations of ADTs via `nominal_obligations`).
   - `ClauseKind::RegionOutlives(r_a, r_b)` (**`L137-139`**): pushes `OutlivesBound::RegionSubRegion(r_b, r_a)` (NOTE argument order: `OutlivesPredicate(r_a, r_b)` means `r_a: r_b`, stored as sub-region first `r_b <= r_a`).
   - `ClauseKind::TypeOutlives(ty_a, r_b)` (**`L141-148`**): runs `push_outlives_components(tcx, ty_a, &mut components)` and passes `components` to **`implied_bounds_from_components(r_b, components)`**—which **retains `ty::ReStatic`** and never invokes RFC 2093's `is_free_region`!

This single contrast explains three major `rustc` asymmetries empirically confirmed by our probes:

- **Asymmetry 1 (`'static` in functions/impls vs. structs)**:
  - `fn f<T>(_x: &'static T) { need_static::<T>(); }` (`fn_implied_static_ref_ok`, stdout `FN_STATIC_OK=1`) and `impl<T> StaticTr for &'static T` (`impl_for_static_ref_ok`, stdout `IMPL_STATIC_OK=7`) **both succeed**, because `&'static T` is in `assumed_wf_types` and `implied_bounds_from_components` emits `T: 'static`.
  - Meanwhile, `struct StaticRef<T>(&'static T)` **fails `E0310`** because `struct` has `assumed_wf_types = &[]` and relies exclusively on RFC 2093 (`is_free_region(ReStatic) == false`).
- **Asymmetry 2 (`impl` header vs. associated type RHS)**:
  - `impl<'a, T> MyTrait for &'a T` (`trait_impl_for_ref_requires_wf_ok`, `IMPL_FOR_REF_OK=1`) succeeds because `trait_ref.args.types()` includes `&'a T`, implying `T: 'a`.
  - `impl<'a, T> Assoc<'a, T> for S { type Out = &'a T; }` (`assoc_type_ref_missing_outlives_e0309`) fails **`E0309`** because `DefKind::AssocTy` (`implied_bounds.rs:127-129`) delegates solely to `assumed_wf_types(local_parent(def_id))` (`[S]`), omitting `Out`'s own RHS `&'a T`.
- **Asymmetry 3 (ADT outlives bounds inherit into `impl`s, ADT trait bounds do NOT)**:
  - `impl<'a, T> Ref<'a, T>` (`struct_ref_impl_inherits_rfc2093_ok`, `IMPL_INHERIT_OK=1`) inherits `T: 'a` because checking `[Self = Ref<'a, T>]` triggers `WellFormed` -> `inferred_outlives_of(Ref)` -> `TypeOutlives(T, 'a)` which `compute_implied_outlives_bounds_inner` collects.
  - `struct NeedEq<T: PartialEq>(T); impl<T> NeedEq<T> { fn same(&self, other: &Self) -> bool { self.0 == other.0 } }` (`struct_where_not_implied_in_impl_e0277`) fails **`E0277` + `E0369`**, because `wf::unnormalized_obligations(NeedEq<T>)` emits `ClauseKind::Trait(T: PartialEq)`, which `compute_implied_outlives_bounds_inner` explicitly ignores at `L117` and which `ParamEnv` never elaborates.

Downstream in borrow checking, `rustc_borrowck::type_check::free_region_relations::create` (`free_region_relations.rs:44-65`) consumes the exact same implied-bounds machinery (via `ImpliedOutlivesBounds` / normalized input-output types) to build `UniversalRegionRelations { outlives, inverse_outlives }`, ensuring MIR borrow checking sees the identical implied outlives closure computed during HIR WF checking.

Basis: source + execution + normative

---

### Supertrait Elaboration and the `PredicateFilter::SelfAndAssociatedTypeBounds` Asymmetry

`rustc_type_ir::elaborate` (`compiler/rustc_type_ir/src/elaborate.rs`, specifically `Elaborator::extend_deduped` `L101-111` and `Elaborator::elaborate` `L127-240`) expands `ParamEnv` clauses, trait obligations, and supertraits using a visited-set deduplicated DFS stack (`self.visited.insert(self.cx.anonymize_bound_vars(o.predicate().kind()))`, preventing cycles on cyclic traits such as `trait Sized: Sized`). Key behavioral rules audited in `elaborate.rs`:

1. **Positive `ClauseKind::Trait` Expansion (`L150-183` in `14210df0e`; `L120-153` in `058c70105`)**:
   - Checks `if data.polarity != PredicatePolarity::Positive { return; }` (`L152` / `ClausePolarity::Positive` in `058c70105` `L121`); negative bounds (`!Trait`) never elaborate.
   - Dispatches on `self.mode`:
     - `Filter::All`: calls **`cx.explicit_implied_predicates_of(data.def_id().into())`** (`explicit_implied_clauses_of` in `058c70105`).
     - `Filter::OnlySelf`: calls **`cx.explicit_super_predicates_of(data.def_id())`** (`explicit_super_clauses_of` in `058c70105`), instantiating via `.instantiate_supertrait(cx, bound_clause.rebind(data.trait_ref))`.
   - Suppresses `Sized` supertrait expansion unless `.elaborate_sized()` is enabled (`L141-146`), an optimization documented in-source for sizedness hierarchy (`PERF(sized-hierarchy)`).
2. **`HostEffect`, `TypeOutlives`, and Non-Elaborated Clauses (`L185-240`)**:
   - `HostEffect`: expands `[const] Trait` -> `[const] Supertrait`.
   - `TypeOutlives(ty_max, r_min)`: if `!r_min.is_bound()` (`L212`: `"Ignore for<'a> T: 'a"`), calls `push_outlives_components` and pushes elaborated component outlives clauses (skipping escaping aliases).
   - `RegionOutlives`, `WellFormed`, `Projection`, `ConstEvaluatable`, `ConstArgHasType`: **no elaboration** (`L225-240`). Notably, `ClauseKind::Projection` obligations (`<T as Base>::Item == u32`) are produced *only* when expanding supertraits from a parent `Trait` bound (e.g., `trait Sub: Base<Item = u32>`), not by further elaborating an isolated projection equation.
3. **The Hidden `PredicateFilter` Trait vs. Trait-Alias Split (`predicates_of.rs:619-650` / `clauses_of.rs:607-638`)**:
   Inspection of `explicit_implied_predicates_of` (`predicates_of.rs:637-650`) and `explicit_implied_clauses_of` (`clauses_of.rs:625-638`) reveals the exact filter passed during `Filter::All` elaboration:
   ```rust
   implied_predicates_with_filter(
       tcx,
       trait_def_id.to_def_id(),
       if tcx.is_trait_alias(trait_def_id.to_def_id()) {
           PredicateFilter::All
       } else {
           PredicateFilter::SelfAndAssociatedTypeBounds
       },
   )
   ```
   Whereas `explicit_super_predicates_of` (`L623`) passes `PredicateFilter::SelfOnly`.

   This single `if/else` creates a crisp four-way partition verified directly by our probe suite (and identical under `-Znext-solver`):

   | Trait / Bound Declaration | Caller / Obligation Context | `PredicateFilter` Applied | Compiled Outcome | Diagnostic / Output |
   | :--- | :--- | :--- | :--- | :--- |
   | `trait Tr<'a>: 'a {}` | `fn caller<'a, X: Tr<'a>>` needing `X: 'a` | `SelfAndAssociatedTypeBounds` (`Self` included) | **PASS** (`rc = 0`) | `SELF_ELAB_OK=1` |
   | `trait Tr<'a> { type Assoc: 'a; }` | `fn caller<'a, X: Tr<'a>>` needing `X::Assoc: 'a` | `SelfAndAssociatedTypeBounds` (`Self::Assoc` included) | **PASS** (`rc = 0`) | `ASSOC_ELAB_OK=1` |
   | `trait Tr<'a, T: 'a> {}` | `fn caller<'a, T, X: Tr<'a, T>>` needing `T: 'a` | `SelfAndAssociatedTypeBounds` (non-`Self` param `T` **excluded**!) | **FAIL** (`rc = 1`, `E0309`) | 2x `error[E0309]: the parameter type T may not live long enough` (`trait_param_bound_not_implied_by_filter_e0309`) |
   | `trait Alias<'a, T: 'a> = Base<'a, T>;` | `fn caller<'a, T, X: Alias<'a, T>>` needing `T: 'a` | `All` (non-`Self` param `T` **included**!) | **PASS** (`rc = 0`) | `TRAIT_ALIAS_ELAB_OK=1` (`trait_alias_all_filter_elaborates_ok`) |

   Because `Self` and `Self::Assoc` are the only LHS subjects admitted by `PredicateFilter::SelfAndAssociatedTypeBounds`, bounds written directly on secondary trait generic parameters (`T: 'a` on `trait Tr<'a, T: 'a>`) must still be repeated by callers unless `Tr` is a `trait_alias` (`PredicateFilter::All`). Even `X: Tr<'a, T>` itself in the caller header fails WF check (`trait_param_bound_not_implied_by_filter_e0309`: line 3 `X: Tr<'a, T>` errors with `E0309` in addition to the body call on line 4!).

Basis: source + execution + derived

---

### Associated-Type Projection Normalization, Precedence, and Diamond Ambiguity

#### Classic Normalization Entry Points, Cache States, and Priority Order

In the classic solver, `normalize_projection_term` (`compiler/rustc_trait_selection/src/traits/project.rs:262-283`) delegates to `opt_normalize_projection_term` (`project.rs:297-380+`), which resolves inference variables (`resolve_vars_if_possible`), queries a per-`InferCtxt` projection cache keyed by `(projection_term, param_env)` (`ProjectionCacheKey::new`), and handles five cached outcomes before invoking `project` (`L375`):
- `ProjectionCacheEntry::Ambiguous` (`L320-326`) -> returns `Ok(None)`, causing `normalize_projection_term` (`L273-282`) to allocate a fresh type inference variable `$X` and enqueue a deferred `<T as Trait>::Assoc == $X` obligation.
- `ProjectionCacheEntry::InProgress` / `Recur` (`L327-347`) -> returns `Err(InProgress)` (cycle detection).
- `ProjectionCacheEntry::NormalizedTerm { ty, complete }` (`L348-363`) -> returns cached `ty.value` and appends `ty.obligations` (preventing obligation-dropping ICEs).
- `ProjectionCacheEntry::Error` (`L364-369`) -> `normalize_to_error`.

When uncached, `project` (`project.rs:652-709` in `14210df0e`; `692-787` in `058c70105`) guards against `recursion_depth` overflow (`OverflowError::Canonical`, `L656-662`), short-circuits on non-region tainted errors (`L666-672`), and—in `058c70105` `L716-750`—rejects `<dyn Trait>::Name` when `!tcx.is_dyn_compatible(def_id)`. It then populates `let mut candidates = ProjectionCandidateSet::None` strictly in four ordered stages (`project.rs:676-692` / `754-770`):

1. **`assemble_candidates_from_param_env`** (elaborated `caller_bounds` projection equations — **highest priority**).
2. **`assemble_candidates_from_trait_def`** (associated-type item bounds such as `type FooT: Bar<BarT = i32>`).
3. **`assemble_candidates_from_object_ty`** (`dyn Trait<Assoc = T>` object type projections).
4. **`assemble_candidates_from_impls`** (matching `impl`s — skipped when `candidates` is already `ProjectionCandidateSet::Single(ProjectionCandidate::Object(_))` to avoid object-normalization cycles, `L685-692`).

#### `ProjectionCandidateSet::push_candidate`: Why Consistent Diamonds Pass and Conflicting Diamonds Emit `E0284`

`ProjectionCandidateSet::push_candidate` (`project.rs:94-140`) enforces the algebraic merge semantics:
- **`None -> Single(candidate)`** (`L98-101`): records the first matching candidate.
- **`Single(current)` when `current == &candidate`** (`L106-108`): returns `false` without altering `Single(current)` (*"Duplicates can happen inside ParamEnv. In the case, we perform a lazy deduplication."*).
  - Live probe verification (`diamond_consistent_supertrait_proj_ok`): given `trait Base { type Item; }`, `trait Left: Base<Item = u32> {}`, `trait Right: Base<Item = u32> {}`, `trait Both: Left + Right {}`, `fn use_diamond<T: Both>(x: <T as Base>::Item) -> u32 { x }` compiles cleanly and outputs `DIAMOND_NORM=99` when passed `99u32`.
- **`(ParamEnv(..), ParamEnv(..))` with `current != &candidate`** (`L118-119`): sets `self = ProjectionCandidateSet::Ambiguous`. Notice by contrast `(ParamEnv(..), non_ParamEnv)` (`L121`) returns `false`, preserving **`ParamEnv`'s strict precedence over `Impls`**!
- **`ProjectionCandidateSet::Ambiguous` in `project`** (`L707` / `L785`): returns `Err(ProjectionError::TooManyCandidates)`, which `opt_normalize_projection_term` converts into `Ok(None)`, causing `normalize_projection_term` (`L273-282`) to replace `<T as Base>::Item` with a fresh inference variable `$X` (`projection_term_to_infer`). Downstream type checking then reports **`E0284: type annotations needed`** (NOT `E0271`)!
  - Live probe verification (`diamond_conflicting_supertrait_proj_e0284`): changing `Right` to `Base<Item = i32>` yields three `error[E0284]` diagnostics (`cannot satisfy <Self as Base>::Item == u32` on `trait Both: Left + Right {}`, plus `cannot infer type` / `cannot satisfy <T as Base>::Item == u32` on `fn take<T: Both>(x: <T as Base>::Item) -> u32`), matching `TooManyCandidates -> projection_term_to_infer` line-for-line.

#### Classic vs. `-Znext-solver` Differential Behavior

Across all 5 targeted differential probes (`c_next_solver_differential` in `probe_results.json`), `-Znext-solver` exhibits identical accept/reject outcomes and identical primary error codes (`E0310` on `StaticRef<T>`, `E0309` on `trait Tr<'a, T: 'a>` caller, `E0277` + `E0369` on `impl<T> NeedEq<T>`, `rc=0` on `fn_implied_ref_ok` and `supertrait_elaboration_and_norm_ok`). The only observed diagnostic-count difference occurs in `next_solver_struct_where_not_implied_e0277`, where `-Znext-solver` emits one additional `E0277` spanning the second parameter `other: &Self` (`4 previous errors` vs. `3 previous errors` on the classic solver).

Basis: source + execution

---

### Source Evolution Between `14210df0e` (`2026-05-31`) and `058c70105` (`2026-11-24`)

Comparing the installed `rustc 1.98.0-nightly` commit (`14210df0e`) against the `2026-11-24` `rust-lang/rust` snapshot (`058c70105`) shows syntactic refactoring and module relocation without altering the core semantic boundaries established above:

| Subsystem / File (`14210df0e`) | Change in `058c70105` | Semantic Impact on This Report's Invariants |
| :--- | :--- | :--- |
| `compiler/rustc_hir_analysis/src/outlives/mod.rs` (`L17-96`) | `CratePredicatesMap.predicates` -> `CrateClausesMap.clauses`; `type_alias_is_lazy` -> `type_alias_is_checked`; `OutlivesPredicate` -> `OutlivesClause`; `infer_predicates` -> `infer_clauses`. | **None** on core ADT/`TyAlias`/`ReStatic` partition; type-alias feature flag was renamed `lazy_type_alias` -> `checked_type_aliases` (`type_of.rs:582`). |
| `compiler/rustc_hir_analysis/src/collect/type_of.rs` (`L520-537`) | `type_alias_is_checked` (`L572-600`) adds early opt-out `if find_attr!(tcx, def_id, UncheckedTypeAlias) { return false; }` (`L578-580`) and checks `tcx.features().checked_type_aliases()`. | New `#[rustc_unchecked_type_alias]` attribute opts an individual checked/TAIT alias back out of RFC 2093 + WF checking. |
| `compiler/rustc_hir_analysis/src/outlives/utils.rs` (`L86-109`) | `Component::Alias(alias_ty)` becomes `Component::Alias(is_rigid, alias_ty)` -> `alias_ty.to_ty(tcx, is_rigid)` (`L85-108`); `is_free_region` (`L145-182`) is unchanged line-for-line! | Preserves `ReStatic => false`, `ReBound => false`, and `Component::Alias` non-descent identically. |
| `compiler/rustc_hir_analysis/src/collect/predicates_of.rs` | Moved to `compiler/rustc_hir_analysis/src/collect/clauses_of.rs` (confirmed `404` at old path in `058c70105`, `404` at new path in `14210df0e` via `verify_pins.py`); `explicit_implied_clauses_of` (`L625-638`) keeps `All` vs `SelfAndAssociatedTypeBounds` identically. | **None** on `trait Tr<'a, T: 'a>` vs `trait Alias<'a, T: 'a>` asymmetry. |
| `compiler/rustc_trait_selection/src/traits/query/type_op/implied_outlives_bounds.rs` | Moved to `compiler/rustc_trait_selection/src/traits/implied_outlives_bounds.rs` (confirmed `404` move in `verify_pins.py`); `compute_implied_outlives_bounds_inner` (`L45-125`) moves `deeply_normalize` to callers (`normalized_ty` parameter), adds `deeply_resolve_ignoring_regions(arg)` (`L68`), and extracts the bevy compat hack to `consider_implied_bounds_hack_for_ty` (`L132`). | **None** on implied outlives collection (`ClauseKind::Trait` still ignored; `ReStatic` still kept). |
| `compiler/rustc_trait_selection/src/traits/project.rs` | `project` (`L692-787`) adds pre-candidate `<dyn Trait>::Name` `is_dyn_compatible` check (`L716-750`) and passes `ty::IsRigid::No` (`L778`). Candidate priority order (`L757-770`) is unchanged. | Rejects projections from dyn-incompatible trait objects cleanly before candidate assembly. |
| `compiler/rustc_type_ir/src/elaborate.rs` | `PredicatePolarity::Positive` -> `ClausePolarity::Positive`; `explicit_implied_predicates_of` -> `explicit_implied_clauses_of` (`L120-166`). | **None** on positive-only supertrait elaboration or `Filter::All` vs `Filter::OnlySelf`. |

Basis: source + execution (SHA pin & HTTP 404/200 checks in `pin_receipt.json`)

---

### Mechanized Lean `v4.34.1` Soundness Model & TCB Audit

`support/ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness.lean` (`2,519` lines, `115,886` bytes, zero external imports beyond Lean `Init`) mechanizes all four subsystems and their separating counterexamples across seven structured parts:

1. **Kernel Purity & Environment Verification (`support/check_lean.py` + `support/ImpliedBoundsRfc2093Audit.lean`)**:
   - Compiled cleanly with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`0` warnings, `0` errors, `olean_bytes = 3,462,736`).
   - MetaM audit of all `841` constants in the `.olean` environment (`support/lean_check_receipt.json`) verifies **`241` kernel theorems (`99` zero-axiom, remaining using strictly `[Quot.sound, propext]`)**, **`377` defs** (every user `def` marked `noncomputable def`, **`0` bare `def`s**, **`0` `._unsafe_rec` helpers**), **`0` axioms**, **`0` `opaque` declarations**, **`0` `unsafe`/`partial def` definitions**, **`0` `Classical.choice`**, **`0` `sorry`/`sorryAx`**, **`0` `omega`**, **`0` `bv_decide`**, **`0` `native_decide`**, **`0` `noncomputable section`**, and **`0` `deriving` clauses**.

2. **Mechanized Theorems Inventory**:

| Part | Key Definitions | Key Proved Theorems & Guarantees |
| :--- | :--- | :--- |
| **1 — Syntax, Eq & Constructive Fixpoints** | `Region`, mutually inductive `Ty`/`TyArgs`, `OutlivesTarget`, `OutlivesBound`, `TaggedBound`, `listMem`, `dedupList`, `filterScore`, `iterFn` (`@Nat.rec`) | `tyBeq_refl`, `tyBeq_eq`, `mem_dedupList_iff`, **`finite_universe_fixpoint_terminates`**, **`firstFixpointFuel_terminates`** — proves constructively (no `Classical.choice`, no `omega`) via counting score `filterScore` that any monotone list operator staying within finite universe `univ` stabilizes in `≤ univ.length` rounds. |
| **2 — Semantics & Components** | `substTy`, `substBound`, `pushOutlivesComponents` (with `Component.alias` vs `Component.escapingAlias` on `tyHasLate`), `OutlivesHolds`, `TyOutlivesHolds`, `TyWF` | `substRegion_*`, `outlivesHolds_weaken`. |
| **3 — RFC 2093 Inference** | `rfc2093IsFreeRegion` (`ReStatic`/`ReBound => false`), `altIsFreeWithStatic`, `insertOutlivesClause`, `walkTyForClauses`, `inferRound`, `inferredOutlivesOf` | `walkTyForClauses_mono`, `inferRound_mono`, `inferredOutlivesOf_mono`, **`rfc2093_fixpoint_terminates`**, **`rfc2093_least_fixpoint`**, **`rfc2093_fixpoint_field_complete`** (every syntactically required free-region clause across fields is present at the fixed point), `nestedRefChain_size` (recursion-limit necessity witness). |
| **4 — `E0310`, `ReBound`, `E0309`, Convergence** | `staticRefAdt`, `fnHolderAdt`, `wrapProjAdt`, `holderProjAdt`, `nestedAdts` | **`rfc2093_never_emits_static_rhs`**, **`staticRef_wf_fails_without_explicit_e0310`**, `staticRef_explicit_wf_ok`, `staticRef_inferred_when_static_is_free`, `fnHolder_inferred_empty_all_fuel`, `pushOutlivesComponents_late_proj_escaping`, **`wrapProj_never_infers_param_e0309`**, **`holderProj_no_impl_norm_empty_all_fuel`**, `nestedAdts_converge_at_three`. |
| **5 — Implied Bounds & `assumed_wf_types`** | `ItemKind`, `assumedWfTypes`, `extractTypeOutlives`, `wfImpliedOutlivesFull`, `computeImpliedOutlivesEnv` | **`extractTypeOutlives_sound`**, **`wfImpliedOutlivesFull_sound`**, **`implied_bounds_soundness`**, **`callee_outlives_discharged`**, `fn_static_ref_implies_param_static`, `trait_impl_static_ref_implies_param_static`, `inherent_impl_ref_inherits_rfc2093`, **`assoc_ty_rhs_not_assumed_wf_e0309`**, **`struct_where_trait_bound_not_in_implied_env_e0277`**. |
| **6 — Supertrait Elaboration & Filters** | `Clause`, `ElabFilter` (`onlySelf`, `selfAndAssoc`, `all`), `expandClause`, `elaborate`, `ElabEntails`, `ElabPath` | `elaborate_contains_roots`, `elaborate_mono`, **`elaborate_sound`**, **`elaborate_transitivity_chain`** (arbitrary `k`-hop positive supertrait path completeness at fuel `k + 1`), `trait_self_and_assoc_elaborates`, `trait_alias_all_elaborates_param_bound`, **`trait_param_bound_excluded_by_selfAndAssoc_e0309`** (`E0309` exclusion proved for all fuel!). |
| **7 — Projection Precedence & Confluence** | `CandidateSet`, `pushCandidate`, `assembleCandidates`, `ProjRule`, `lookupProj`, `NormStep`, `NormStar`, `ParNorm` | `pushCandidate_consistent_diamond`, `pushCandidate_conflict_ambiguous`, **`paramEnv_beats_impl`**, **`parNorm_diamond`** (Tait–Martin-Löf parallel reduction diamond), **`normStar_confluent`** (full Church–Rosser theorem under `GroundHeadRules`), **`normal_form_unique`**. |

Why every `def` uses `@Nat.rec` / `@Ty.rec` / `@TyArgs.rec` and explicit `noncomputable def`: in Lean `v4.34.1`, recursive equations can synthesize `_unsafe_rec` helpers that trip downstream TCB auditors expecting pure eliminator reductions. Writing eliminator applications explicitly guarantees `AUDIT_UNSAFE_REC=0` by construction while keeping kernel reduction (`rfl`) fast (`7.3s` compile, `2.9s` audit).

Basis: derived + execution (Lean `v4.34.1` kernel & MetaM `.olean` check receipt)

---

### Downstream Boundary with Anneal (`joshlf/anneal`)

Inspection of `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) establishes how Anneal relies on—yet stays cleanly decoupled from—the `rustc` subsystems analyzed here:

- **Post-Cleanup Monomorphic Region-Erased Entry (`trusted/lean/Trusted/MirAst.lean:304-321`)**: Anneal's MIR AST represents references as `.ref mutability pointee` (`MirTy.ref`, documented explicitly at `L305`: `"(regions are erased at runtime)"`) and marks unmonomorphized/unsupported polymorphic-or-object forms (`FnDef`, `FnPtr`, `Dynamic`, `Closure`, `Coroutine`, `Foreign`, etc.) as `MirTy.unsupported` failing closed (`L308-311`).
- **Compiler Pin Gate (`trusted/rustc-capture/src/driver.rs:25, 45-47, 75-84`)**: `driver.rs` enforces exact version string equality against its pinned nightly (`1.98.0-nightly (f8a08b688 2026-05-30)` in `c131b320e`, adjacent by 1 day to this report's `14210df0e` `2026-05-31` toolchain) and records `analysis_reached` only after `tcx.dcx().has_errors().is_none()` (`after_analysis`, `L82`) followed by clean compilation exit.
- **Architectural Implication**: Anneal never re-checks RFC 2093 outlives, trait elaboration, associated-type projection normalization, or NLL borrowck region constraints inside Lean. Instead, Anneal's `Runtime(PostCleanup)` capture boundary assumes **`rustc`'s front-end typeck + trait solver + borrowck have validly rejected every ill-lifetime (`E0309`/`E0310`), ill-trait (`E0277`), and ambiguous projection (`E0284`) program prior to monomorphic region-erased MIR emission**. Conversely, Anneal's `.lean` proof hygiene (`trusted/audit/TrustedBoundary.lean:14-95`) forbids `partial`, `axiom`, `unsafe`, `sorryAx`, `Lean.ofReduceBool`/`bv_decide`, `native_decide`, and `._unsafe_rec`—constraints satisfied 100% by this package's Lean formalization.

Basis: source + derived

---

## Boundaries

Per the corpus epistemic contract, negative space and unestablished stronger conclusions are explicitly separated below:

1. **Not examined**:
   - Arbitrary `crates.io` ecosystem breakage rates or prevalence of RFC 2093 / `E0310` / `E0284` diagnostics across third-party crates; empirical probes are minimal focused reproducers constructed specifically to isolate each compiler rule cleanly.
   - `bevy_ecs::ParamSet` legacy compat fallback behavior on real Bevy crates (`wfcheck.rs:205-221` / `implied_outlives_bounds.rs:132-167`), `-Zno-implied-bounds-compat` performance impacts, and `generic_const_exprs` `AnonConst` param-default chains (`outlives/mod.rs:24-44`) were inspected in `rustc` source only and not executed dynamically.
   - Specialization interactions (`#![feature(min_specialization)]`), coroutine witness outlives inference, and RPITIT lifetime-remapping edge cases (`implied_bounds.rs:58-126`) were read in source (`outlives.rs`, `implied_bounds.rs`) without dedicated live `rustc` probes.
   - Nightly build `1.98.0-nightly (f8a08b688 2026-05-30)` referenced as a literal string in `joshlf/anneal@c131b320e`'s `driver.rs:25` was not separately installed; `rustc` execution ran on `1.98.0-nightly (14210df0e 2026-05-31)`, cross-checked via source inspection against `14210df0e` and `058c70105`.

2. **Unknown**:
   - Exact timeline or FCP stabilization status for moving/removing the legacy `bevy_ecs::ParamSet` compat path noted in `FIXME(#160491)` (`058c70105` `implied_outlives_bounds.rs:19`) or landing `checked_type_aliases` (`#112792`) on stable Rust.
   - Whether `#100910` / `#98543` (`engine.rs:318-329`, commented-out unnormalized insertion into `assumed_wf_types`) will be resolved by replacing pre-normalization checks in `-Znext-solver` or via a breaking deprecation cycle.

3. **Known not to apply**:
   - **RFC 2093 does NOT apply to `'static` (`ReStatic`)**: Direct inspection of `utils.rs:164`, `#[rustc_dump_inferred_outlives]` output, and `E0310` probes establish that `struct Foo<T>(&'static T)` **never** infers `T: 'static`.
   - **Implied bounds do NOT propagate `ClauseKind::Trait` from ADTs into impls or functions**: `impl<T> NeedEq<T>` for `struct NeedEq<T: PartialEq>(T)` does **not** inherit `T: PartialEq` (`compute_implied_outlives_bounds_inner` drops `ClauseKind::Trait`).
   - **Associated-type RHS definitions do NOT imply outlives bounds on the defining `impl`**: `impl<'a, T> Assoc<'a, T> for S { type Out = &'a T; }` fails `E0309` because `assumed_wf_types` returns only parent `Impl` assumed-WF types.
   - **`PredicateFilter::SelfAndAssociatedTypeBounds` prevents `trait Tr<'a, T: 'a>` from implying `T: 'a` to callers**: Unlike `Self: 'a` and `Self::Assoc: 'a` (which elaborate), non-`Self` parameter bounds on ordinary traits do **not** elaborate (`trait_alias` `PredicateFilter::All` is the deliberate exception).
   - **`rustc` borrowck/typeck soundness guarantees are NOT equivalent to MIR-level formalization**: Our Lean formalization covers the modeled static type/outlives/projection calculus; it does **not** mechanize all of `rustc_borrowck`, NLL Polonius fixed points, or Rust's complete operational soundness over unsafe code.

4. **Unsupported (Explicit Non-Features & Rejected Patterns)**:
   - Normal (unchecked) `type` aliases do not perform RFC 2093 outlives inference or definition-site WF checking on stable Rust.
   - `inherent_associated_types` outlives inference in `implicit_infer.rs:223` is explicitly unimplemented (`FIXME`).
   - Projections referencing escaping higher-ranked `for<'b>` lifetimes cannot be represented as header outlives clauses (`Component::EscapingAlias` in `outlives/utils.rs:111-126`).
   - Projections from dyn-incompatible trait objects (`<dyn Trait>::Assoc`) fail pre-candidate dyn-compatibility checks (`058c70105` `project.rs:716-750`).

Basis: source + execution + derived

---

## Evidence

All artifacts preserving primary source citations, live `rustc` executions, Lean `v4.34.1` kernel proofs, and pin verification live inside this package's `support/` directory and use immutable commits and SHA-256 hashes.

### 1. Preserved Package Support Artifacts

| File (`support/...`) | Size / Scope | Purpose & Verification Role |
| :--- | :--- | :--- |
| `probe_implied_bounds_and_supertraits.py` | `30,597` bytes (`39` test cases in 3 groups) | Self-contained `rustc` driver running each testcase in `tempfile.TemporaryDirectory()`, capturing compiler exit codes, error codes, stderr, and compiled binary stdout. |
| `probe_results.json` | `35,356` bytes (`39/39` passed) | Full JSON record with per-case source SHA-256, exact `rustc 1.98.0-nightly (14210df0e 2026-05-31)` version metadata, stdout, and verbatim stderr diagnostics. |
| `probe_summary.md` | `5,646` bytes | Concise pass/fail and diagnostic table across groups `a_implied_bounds_and_rfc2093_boundaries` (25), `b_supertrait_elaboration_and_projection_norm` (9), and `c_next_solver_differential` (5). |
| `ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness.lean` | `2,519` lines, `115,886` bytes (`70` `noncomputable def`s, `26` inductives/structs, `120` theorems) | Kernel-checked Lean `v4.34.1` mechanization of Parts 1–7 (`rfc2093_fixpoint_terminates`, `rfc2093_fixpoint_field_complete`, `staticRef_wf_fails_without_explicit_e0310`, `implied_bounds_soundness`, `elaborate_sound`, `elaborate_transitivity_chain`, `trait_param_bound_excluded_by_selfAndAssoc_e0309`, `paramEnv_beats_impl`, `parNorm_diamond`, `normStar_confluent`, `normal_form_unique`). |
| `ImpliedBoundsRfc2093Audit.lean` | `3,350` bytes | Lean MetaM `.olean` auditor inspecting every constant in the compiled soundness module (`841` total constants, `241` kernel theorems). |
| `check_lean.py` | `9,220` bytes | Reproducible Lean `v4.34.1` verification harness: strips comments, checks `0` forbidden tokens & `0` bare non-`noncomputable` `def`s, compiles synchronously (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`), runs `ImpliedBoundsRfc2093Audit.lean`, cleans `.olean` temps, and emits `lean_check_receipt.json`. |
| `lean_check_receipt.json` | `1,640` bytes (`passed: true`) | Recorded Lean receipt (`module_sha256: 7f170383...`, `AUDIT_AXIOMS: [Quot.sound, propext]`, `AUDIT_UNSAFE_REC: 0`, `AUDIT_VIOLATIONS: 0`, compile `7.323s`, audit `2.971s`). |
| `verify_pins.py` | `10,888` bytes | Live GitHub commit + raw-file pin verifier checking all 6 commit SHAs, 36 cited file paths (`HTTP 200`), and 4 file-move negative controls (`HTTP 404`). |
| `pin_receipt.json` | `12,050` bytes (`all_verified: true`) | Recorded GitHub API & raw-content verification receipt (`6/6 commits, 40/40 files verified`). |

### 2. Primary Source Citations (`rust-lang/rust` & `joshlf/anneal`)

- **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`** (`2026-05-31`):
  - `compiler/rustc_hir_analysis/src/outlives/mod.rs:11-96`: `inferred_outlives_of`, `inferred_outlives_crate`
  - `compiler/rustc_hir_analysis/src/outlives/implicit_infer.rs:12-324`: `infer_predicates`, `insert_required_predicates_to_be_wf`, `check_explicit_predicates`, `check_inferred_predicates`
  - `compiler/rustc_hir_analysis/src/outlives/utils.rs:14-183`: `insert_outlives_predicate`, `is_free_region` (`ty::ReStatic => false` at `L164`, `ty::ReBound(..) => false` at `L174`)
  - `compiler/rustc_hir_analysis/src/outlives/explicit.rs:12-65`: `ExplicitPredicatesMap`
  - `compiler/rustc_hir_analysis/src/outlives/dump.rs:6-30`: `#[rustc_dump_inferred_outlives]` handler
  - `compiler/rustc_hir_analysis/src/collect/type_of.rs:520-537`: `type_alias_is_lazy`
  - `compiler/rustc_hir_analysis/src/collect/predicates_of.rs:619-690`: `explicit_super_predicates_of` (`SelfOnly`), `explicit_implied_predicates_of` (`All` vs `SelfAndAssociatedTypeBounds` at `L644-648`)
  - `compiler/rustc_hir_analysis/src/check/wfcheck.rs:140-240`: `enter_wf_checking_ctxt`, `check_well_formed`
  - `compiler/rustc_ty_utils/src/implied_bounds.rs:23-163`: `assumed_wf_types`
  - `compiler/rustc_trait_selection/src/traits/engine.rs:309-343`: `ObligationCtxt::assumed_wf_types` (deeply normalizing types, comment `#100910`)
  - `compiler/rustc_trait_selection/src/regions.rs:24-70`: `OutlivesEnvironment::new_with_implied_bounds_compat`
  - `compiler/rustc_trait_selection/src/traits/outlives_bounds.rs:34-116`: `implied_outlives_bounds`, `implied_bounds_tys`
  - `compiler/rustc_trait_selection/src/traits/query/type_op/implied_outlives_bounds.rs:51-170`: `compute_implied_outlives_bounds_inner`
  - `compiler/rustc_trait_selection/src/traits/project.rs:95-140, 262-380, 652-727`: `ProjectionCandidateSet::push_candidate`, `normalize_projection_term`, `opt_normalize_projection_term`, `project`
  - `compiler/rustc_type_ir/src/elaborate.rs:100-240`: `Elaborator::extend_deduped`, `Elaborator::elaborate`
  - `compiler/rustc_type_ir/src/outlives.rs:13-160`: `Component`, `push_outlives_components`, `FnDef` hack (`L84-100`), `Alias` / `EscapingAlias` (`L151-160`)
  - `compiler/rustc_borrowck/src/type_check/free_region_relations.rs:23-120`: `UniversalRegionRelations`, `create`
- **`rust-lang/rust` @ `058c701055c4b6f60f622d616afc0349911c38c3`** (`2026-11-24` HEAD):
  - `compiler/rustc_hir_analysis/src/outlives/{mod.rs:11-75, utils.rs:9-182}`
  - `compiler/rustc_hir_analysis/src/collect/{clauses_of.rs:607-638, type_of.rs:572-600}` (`type_alias_is_checked`, `UncheckedTypeAlias`)
  - `compiler/rustc_trait_selection/src/traits/{implied_outlives_bounds.rs:45-125, project.rs:692-787}`
  - `compiler/rustc_type_ir/src/elaborate.rs:120-210`
- **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`** (`2026-11-19`):
  - `trusted/lean/Trusted/MirAst.lean:304-321`: region-erased `MirTy.ref`, fail-closed `MirTy.unsupported`
  - `trusted/audit/TrustedBoundary.lean:14-95`: preflight & kernel `.olean` replay boundary
  - `trusted/rustc-capture/src/driver.rs:25, 45-47, 75-84`: compiler version guard & clean-analysis requirement

### 3. Live Execution & Lean Verification Receipts (`2026-11-24`)

- **Live `rustc` probe run**: `python3 reports/rustc-implied-bounds-rfc2093-outlives-inference-projection-and-supertraits/support/probe_implied_bounds_and_supertraits.py` against `rustc 1.98.0-nightly (14210df0e 2026-05-31)` exited `0` (`39/39` passed: `25/25` RFC 2093 / implied-bounds cases, `9/9` supertrait elaboration & projection cases, `5/5` `-Znext-solver` differential checks).
- **Lean `v4.34.1` compile + MetaM `.olean` audit**: `python3 reports/rustc-implied-bounds-rfc2093-outlives-inference-projection-and-supertraits/support/check_lean.py` exited `0` (`passed: true`, `compile.returncode: 0`, `compile.stdout: ""`, `compile.stderr: ""`, `compile.wall_seconds: 7.323`, `audit.returncode: 0`, `AUDIT_VIOLATIONS=0`, `AUDIT_UNSAFE_REC=0`, `AUDIT_AXIOMS=[Quot.sound, propext]`).
- **GitHub pin & raw path verification**: `python3 reports/rustc-implied-bounds-rfc2093-outlives-inference-projection-and-supertraits/support/verify_pins.py` exited `0` (`commits_verified: 6/6`, `files_verified: 40/40`, `all_verified: true`).

Basis: execution + source

---

## Revalidation

To test whether these compiler behaviors, upstream source invariants, and Lean soundness proofs continue to hold against another `rustc` nightly, `rust-lang/rust` commit, or Lean toolchain, run the package's standalone verification commands from the repository root (`cd <corpus-root>`):

1. **Re-run the 39-case `rustc` behavioral & `-Znext-solver` probe suite**:
   ```bash
   python3 reports/rustc-implied-bounds-rfc2093-outlives-inference-projection-and-supertraits/support/probe_implied_bounds_and_supertraits.py \
     --rustc "$(command -v rustc)" \
     --json-out /tmp/reval_probe_results.json \
     --md-out /tmp/reval_probe_summary.md
   ```
   (Passes iff exit code is `0` and `summary.failed == 0` in `/tmp/reval_probe_results.json`. Any diagnostic change on `StaticRef`, `Tr<'a, T: 'a>`, `Wrap<'a, T: Id>`, `Both: Left + Right`, `NeedEq<T>`, or `-Znext-solver` pinpoints the exact changed subsystem.)

2. **Minimal 1-command spot check on upstream source lines (detects RFC 2093 / `PredicateFilter` / `assumed_wf_types` changes)**:
   Inspect only:
   - `compiler/rustc_hir_analysis/src/outlives/utils.rs` (`is_free_region`, check whether `ty::ReStatic => false` changed)
   - `compiler/rustc_hir_analysis/src/collect/clauses_of.rs` (`explicit_implied_clauses_of`, check `PredicateFilter::SelfAndAssociatedTypeBounds` vs `All`)
   - `compiler/rustc_ty_utils/src/implied_bounds.rs` (`assumed_wf_types`, check `AssocTy` / `Impl` / `Fn` arms)
   - `compiler/rustc_trait_selection/src/traits/implied_outlives_bounds.rs` (`compute_implied_outlives_bounds_inner`, check `ClauseKind::Trait` handling)
   - `compiler/rustc_trait_selection/src/traits/project.rs` (`project` / `ProjectionCandidateSet::push_candidate`)

3. **Re-verify the `2,519`-LOC Lean `v4.34.1` mechanization and MetaM `.olean` audit**:
   ```bash
   python3 reports/rustc-implied-bounds-rfc2093-outlives-inference-projection-and-supertraits/support/check_lean.py \
     --lean "$(command -v lean)" \
     --no-wrapper \
     --out /tmp/reval_lean_receipt.json
   ```
   (Verifies zero forbidden tokens, zero bare `def`s without `noncomputable def`, clean `-DwarningAsError=true` synchronous compilation, and `0` `._unsafe_rec` / `0` forbidden axioms via `ImpliedBoundsRfc2093Audit.lean`.)

4. **Re-verify upstream GitHub commit pins & validate the corpus package**:
   ```bash
   python3 reports/rustc-implied-bounds-rfc2093-outlives-inference-projection-and-supertraits/support/verify_pins.py \
     --out /tmp/reval_pin_receipt.json
   python3 tools/reference.py check
   ```

Basis: derived + execution
