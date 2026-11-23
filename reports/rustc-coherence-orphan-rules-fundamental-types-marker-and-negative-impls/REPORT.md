# `rustc` Coherence, Covered-Type Orphan Checking (`E0117`/`E0210`), `#[fundamental]` Types and Traits, `#[marker]` Impls, Negative Coherence, and `zerocopy` Disjoint Blankets

## Summary

Rust preserves **global trait coherence** (at most one implementation applies to any closed `(Trait, Self, Args...)` query across all separately compiled crates) and **SemVer monotonicity** (upstream library additions of non-blanket impls or negative impls never break downstream crates) through a four-stage compile-time pipeline anchored in `rustc_hir_analysis::coherence`, `rustc_next_trait_solver::coherence`, and `rustc_trait_selection::traits::coherence`:

1. **Coherence Pass Orchestration & Built-In Guards (`coherence/mod.rs`, `coherence/builtin.rs`, `coherence/unsafety.rs`, `coherence/inherent_impls*.rs`):** For every trait with at least one local impl, `coherent_trait` constructs `specialization_graph_of(def_id)` (which drives pairwise trait-impl overlap checking) and validates every local impl against: (a) manual-implementability bans (`#[rustc_deny_explicit_impl]` -> `E0322` / `E0328`, `Freeze` feature gate, `#[rustc_specialization_trait]`, `impl_restriction`), (b) `#[marker]` zero-item enforcement (`E0715` complementing `wfcheck`'s `E0714`), (c) negative auto-trait always-applicability (`E0366`/`E0367`), (d) automatic `dyn Trait` object-supertrait overlap (`check_object_overlap` -> `E0371`), (e) impl safety matching (`unsafety::check_item` -> `E0199`/`E0200`/`E0569`), (f) orphan checking (`orphan_check_impl`), and (g) built-in structural checks (`Drop`, `Copy`, `Unpin`, `ConstParamTy`, `CoerceUnsized`, `Reborrow`, `CoerceShared`, `DispatchFromDyn`, `CoercePointeeValidated`). Separately, `crate_inherent_impls` enforces defining-crate ownership for inherent impls (`E0116`/`E0390`), and `crate_inherent_impls_overlap_check` pairs an $O(n^2)$ / connected-component symbol filter (`ALLOCATING_ALGO_THRESHOLD = 500`) with `overlapping_inherent_impls` (`E0592`).
2. **Covered-Type Orphan Rules & `#[fundamental]` Traversal (`orphan_check_trait_ref`, `E0117` / `E0210`):** When implementing a foreign (non-local) trait `impl<P1..=Pm> Trait<T1..=Tn> for T0`, `OrphanChecker::visit_ty` executes a strict left-to-right pre-order tree walk over `[T0, T1, ..., Tn]` (`Self` first). It treats crate-local ADTs, `extern type`s, and `dyn LocalTrait` as `LocalTy` (admissible), built-in `&T`/`&mut T` and `#[fundamental]` ADTs (`Box`, `Pin`) as **transparent** wrappers (recursing inward without covering parameters), uncovered `Param`/`Infer`/`Placeholder` types as `UncoveredTyParam` (`E0210` in `InCrate::Local`, `LocalTy` in `InCrate::Remote`), and primitives, tuples, arrays, slices, raw pointers, opaque `RPIT` types, and non-fundamental foreign ADTs (`Vec<T>`, `Option<T>`) as opaque `NonLocalInputType` cutoffs (`E0117` when no subsequent local type is reached). Under RFC 2451 (`Proper` mode), `impl<T> ForeignTrait<LocalType> for Vec<T>` succeeds because non-fundamental `Vec<T>` **covers** `T` before `LocalType`, whereas `impl<T> ForeignTrait<LocalType> for Box<T>` fails `E0210` because `#[fundamental]` `Box` does **not** cover `T`. Crucially, between `rustc 1.98.0-nightly` (`14210df0e`) and upstream `main` (`0259d5e9a`, following `allocator_api` stabilization on `Box<T, A>` in `1.100.0`), `OrphanChecker::visit_ty` added a `SolverAdtLangItem::OwnedBox` special case restricting `Box`'s fundamental unwrapping strictly to `args.type_at(0)` (`T`), stopping `Box<u32, LocalAlloc>` from passing orphan checks via the allocator parameter.
3. **Foreign Auto-Trait Restriction (`E0321`) & `#[fundamental]` Trait Knowability (`trait_ref_is_knowable`):** Foreign auto traits (`Send`, `Sync`, `Unpin`, `Freeze`) bypass `#[fundamental]` unwrapping in `orphan_check_impl`: `NonlocalImpl::Allow` admits only directly local nominal ADTs or `extern type`s, rejecting `unsafe impl Send for Box<Local>` with `E0321`. Meanwhile, `trait_ref_is_knowable` governs negative reasoning during overlap checking: `#[fundamental]` traits (`Fn`, `FnMut`, `FnOnce`, `FnPtr`) satisfy `trait_ref_is_local_or_fundamental`, promising upstream crates will not retroactively implement them for existing foreign types and thereby allowing disjoint blanket patterns such as `impl<F: FnMut(char) -> bool> Pattern for F` alongside `impl Pattern for &str` (which fails `E0119` for ordinary non-fundamental foreign traits).
4. **`#[marker]` Impls (`E0714` / `E0715`) & Negative Coherence (`with_negative_coherence`):** In `TyCtxt::impls_are_allowed_to_overlap`, same-polarity impls of `#[marker]` traits return `Some(ImplOverlapKind::Permitted { marker: true })`, skipping specialization comparison in `Children::insert`. Coherence remains sound solely because `wfcheck::check_trait` (`E0714`) and `enforce_empty_impls_for_marker_traits` (`E0715`) forbid any associated item on `#[marker]` traits or impls. For non-marker traits, `OverlapMode::get` selects `OverlapMode::Stable` (`use_negative_impl = false`, `use_implicit_negative = true`) by default or `OverlapMode::WithNegative` (`use_negative_impl = true`, `use_implicit_negative = true`) under `#![feature(with_negative_coherence)]`. Live `rustc` execution sharpens this distinction: local `!Send` (`impl !Send for Local` + `impl<T: Send> Tr for T` + `impl Tr for Local`) already compiles under `OverlapMode::Stable` because `Local` makes `Local: Send` locally knowable via implicit negative reasoning; by contrast, foreign negative impls (`Rc<T>: !Send` in `alloc`, or an upstream crate's `impl !UpNegTrait for UpNegStruct`) fail `E0119` under `OverlapMode::Stable` and succeed only under `OverlapMode::WithNegative` via `impl_intersection_has_negative_obligation` + `try_prove_negated_where_clause` (with `E0751` forbidding simultaneous positive and negative impls and `E0749` forbidding items in negative impls).
5. **First-Customer `google/zerocopy` Coherence Architecture & Mechanized Verification:** On stable Rust (`google/zerocopy@e5a9824d87f7daa5282969a25a8bbca9af985400`), `zerocopy/src/pointer/transmute.rs` and `invariant.rs` simulate multi-branch `#[marker]`/`specialization`-free coherence over overlapping blanket targets (`TryTransmuteFromPtr`, `MutationCompatible`, `Read`) by indexing traits with **disjoint phantom reason markers `R`** (`(BecauseMutationCompatible, R)` vs. `BecauseImmutable`; `(BecauseRead, R)` vs. `BecauseSharedCompatible`; `BecauseImmutable` vs. `BecauseExclusive`) and relying on the **unification occurs check** to separate `impl<T: ?Sized> SharedCompatible<T> for T` from `ManuallyDrop<T>` (and `Unalign<T>` / `Wrapping<T>`), while `zerocopy/src/impls.rs` implements local traits across `Box<T>`, `&T`, `&mut T` so downstream crates benefit from `#[fundamental]` unwrapping. All 44 live `rustc` multi-crate probe cases (`support/probe_coherence_orphan_fundamental_neg.py`, `support/probe_results.json`) and a standalone 1,727-line kernel-checked Lean `v4.34.1` formalization (`support/CoherenceOrphanFundamentalAndNegativeImplsSoundness.lean`, 36 named theorems, 0 `sorry`, 0 `Classical.choice`, 0 `Quot.sound`, 0 `._unsafe_rec`) verify these invariants end-to-end.

## Applicability

### Studied Upstream Subjects and Relationships

This package characterizes the coherence, orphan, `#[fundamental]`, `#[marker]`, negative-coherence, and first-customer `zerocopy` trait-system layers across seven durable upstream subjects recorded in `REPORT.json`:

1. **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, commit date `2026-05-31`, LLVM `22.1.6`, host `x86_64-unknown-linux-gnu`):** Inspected directly at primary compiler and standard-library sources AND executed live across all 44 probe scenarios in `support/probe_coherence_orphan_fundamental_neg.py` (`support/probe_results.json`).
2. **`rust-lang/rust` at `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` (upstream `main` as of `2026-11-23`):** Audited line-by-line side-by-side against `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` across all coherence, orphan, trait-selection, specialization, `core`, and `alloc` files to establish continuity and isolate concrete behavioral deltas.
3. **`google/zerocopy` at `e5a9824d87f7daa5282969a25a8bbca9af985400` (`main` as of `2026-11-23`):** Audited at `zerocopy/src/impls.rs`, `zerocopy/src/pointer/transmute.rs`, `zerocopy/src/pointer/invariant.rs`, and `zerocopy/src/lib.rs` to extract production first-customer coherence idioms (`TryTransmuteFromPtr`, `MutationCompatible`, `SharedCompatible`, `Read`, `#[fundamental]` container impls) and reconstruct counterfactual probes (`d01`–`d03`).
4. **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`main` as of `2026-11-19`):** Inspected at `trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, and `trusted/lean/Trusted/MirSemantics.lean` to relate upstream trait coherence guarantees to Anneal's post-analysis compiler capture boundary (pinned to `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`).
5. **`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`master` as of `2026-11-17`):** Consulted for normative language specifications in `src/items/implementations.md` and `src/glossary.md`.
6. **`rust-lang/rfcs` at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`:** Consulted for RFC 1023 (`text/1023-rebalancing-coherence.md`) and RFC 2451 (`text/2451-re-rebalancing-coherence.md`) forward-compatibility rationales.
7. **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):** Used to kernel-check `support/CoherenceOrphanFundamentalAndNegativeImplsSoundness.lean` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

### Shared vs. Revision-Specific Behavior (`14210df0e` vs. `0259d5e9a`)

Core coherence orchestration, left-to-right covered-type orphan checking (`OrphanCheckMode::Proper` vs. `Compat`), `#[fundamental]` unwrapping of `&T`/`&mut T`/`Pin<P>`, `#[fundamental]` trait knowability (`Fn`/`FnMut`/`FnOnce`), `E0321` auto-trait restrictions, inherent-impl overlap (`E0592`/`E0116`/`E0390`), `#[marker]` zero-item enforcement (`E0714`/`E0715`), and `with_negative_coherence` (`OverlapMode::Stable` vs. `WithNegative` vs. `Strict`) are shared identically between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `0259d5e9a81c6af08e40f8c204f2c0c41dca1647`. Five verified structural or semantic changes occur between the two revisions:

1. **`OwnedBox` Allocator-Parameter Special Case in `OrphanChecker::visit_ty` (Semantic Difference):**
   - In `14210df0e` (`compiler/rustc_next_trait_solver/src/coherence.rs` L414-416), `library/alloc/src/boxed.rs` L236 gates the second type parameter `A: Allocator = Global` behind `#[unstable(feature = "allocator_api", ...)]`, and `visit_ty` unwraps any `def.is_fundamental()` ADT via `args.visit_with(self)`—visiting **both** `T` and `A` of `Box<T, A>`. Live probe `a15_box_allocator_param_unwrapped_in_1_98` empirically confirms that `impl ForeignTrait for Box<u32, LocalAlloc>` compiles and executes (`compile_rc = 0`, `stdout = "A15=box_u32_local_alloc"`) on `rustc 1.98.0-nightly` (`14210df0e`).
   - In `0259d5e9a` (`library/alloc/src/boxed.rs` L310), `A: Allocator = Global` carries `#[stable(feature = "allocator_api", since = "1.100.0")]`. Correspondingly, `compiler/rustc_next_trait_solver/src/coherence.rs` L418-421 special-cases `SolverAdtLangItem::OwnedBox`:
     ```rust
     match self.infcx.cx().as_adt_lang_item(def.def_id()) {
         Some(SolverAdtLangItem::OwnedBox) => args.type_at(0).visit_with(self),
         Some(..) | None => args.visit_with(self)
     }
     ```
     On `0259d5e9a`, `OwnedBox` visits only `args.type_at(0)` (`T`) and skips `A`, so `impl ForeignTrait for Box<u32, LocalAlloc>` is rejected (`E0117`) while `impl<A: Allocator> ForeignTrait for Box<u32, A>` remains coherent with respect to future allocator-parameterized blanket rules.
2. **Removal of `ImplPolarity::Reservation` (`coherence/unsafety.rs`, `ty/mod.rs`):** `14210df0e` matched `(Positive | Reservation)` in `unsafety::check_item` (L46, L87) and handled `Reservation` in `impls_are_allowed_to_overlap`; `0259d5e9a` removes `Reservation` polarity entirely (`unsafety.rs` L36-122 matches only `Positive` and `Negative`).
3. **`ImplHeader::impl_def_id` Removal (`rustc_trait_selection/src/traits/coherence.rs`):** `0259d5e9a` removes `impl_def_id: DefId` from `ImplHeader` (L43-48 vs. `14210df0e` L47-53) and contracts `coherence.rs` from 868 lines to 744 lines (shifting `overlap` from L243 to L172 and `impl_intersection_has_negative_obligation` from L494 to L388) while keeping the unification, placeholder-plugging, and negated-where-clause logic unchanged.
4. **Built-In `CoerceShared` & `Reborrow` Checks (`coherence/builtin.rs`):** Both revisions run `Reborrow` and `CoerceShared` validation inside `coherence::builtin::check_trait` (`14210df0e` L44-46; `0259d5e9a` L46-47), while `BikeshedGuaranteedNoDrop` (present in earlier 1.9x cycles) is absent in both `14210df0e` and `0259d5e9a`.
5. **Diagnostic / Error-Module Refactoring:** `0259d5e9a` renames `crate::errors` to `crate::diagnostics` across `coherence/*.rs` and moves `rustc_hir::LangItem` to `rustc_attr_ir::lang_items::LangItem` without changing diagnostic codes (`E0117`, `E0210`, `E0119`, `E0116`, `E0321`, `E0322`, `E0328`, `E0366`, `E0367`, `E0371`, `E0592`, `E0714`, `E0715`, `E0749`, `E0751`).

### Configuration, Feature Gates, and Scope Boundaries

- All 44 live Rust probes compiled with `rustc --edition=2024` on `x86_64-unknown-linux-gnu` using `--extern up=libup.rlib` / `--extern up_neg=libup_neg.rlib` for genuine multi-crate compilation boundaries.
- Part A (`a01`–`a14`, `a16`–`a20`), Part B (`b01`–`b05`), `c01`, `c07`, and all of Part D (`zerocopy`-style patterns `d01`–`d03`) use strictly stable Rust.
- `a15` requires `#![feature(allocator_api)]` on `1.98.0-nightly` (`14210df0e`); `b06`–`b08` require `#![feature(marker_trait_attr)]`; `c02`–`c06b`, `c08`–`c11` require `#![feature(negative_impls)]` and/or `#![feature(with_negative_coherence)]`.
- Companion corpus packages cover adjacent seams without overlap: `coherence-orphan-instances-and-module-system-compilation` treats the cross-language Coherence Trilemma (Rust vs. GHC vs. Scala 3 vs. Lean 4 vs. ML modules); `first-order-unification-occurs-check-and-impl-overlap-coherence` analyzes Martelli–Montanari unification and occurs-check soundness in depth; and `rustc-auto-traits-rpit-leakage-fundamental-orphan-specialization-and-freeze` covers `RPIT` auto-trait leakage, `min_specialization`, and `Freeze` ELF placement.

## Findings

### 1. Coherence Pass Pipeline, Built-In Checks, and Attribute Collection

Basis: source + execution

#### 1.1 Query Entry Points and `coherent_trait` Checks (`coherence/mod.rs`)

In `compiler/rustc_hir_analysis/src/coherence/mod.rs` (`14210df0e` L140-189; `0259d5e9a` L142-189), coherence provides eight `TyCtxt` queries via `coherence::provide`: `coherent_trait`, `crate_inherent_impls`, `crate_incoherent_impls`, `inherent_impls`, `crate_inherent_impls_validity_check`, `crate_inherent_impls_overlap_check`, `coerce_unsized_info`, and `orphan_check_impl`.

When `coherent_trait(tcx, def_id)` runs for a trait `def_id`:
1. If `tcx.local_trait_impls(def_id).is_empty()`, it returns `Ok(())` immediately without creating a dependency-graph edge on `specialization_graph_of(def_id)` (`mod.rs` L165-170).
2. Otherwise it evaluates `tcx.ensure_result().specialization_graph_of(def_id)` (`mod.rs` L173), which builds the per-trait specialization tree and invokes `traits::overlapping_trait_impls` on all candidate siblings.
3. For every local impl `impl_def_id` of `def_id`, it sequentially runs five checks (`mod.rs` L175-186):
   - `check_impl` (`mod.rs` L27-52):
     - `enforce_trait_manually_implementable` (L54-114): rejects user impls of `Freeze` without `#![feature(freeze_impls)]`; rejects any impl of `#[rustc_deny_explicit_impl]` traits (`E0322`, or `E0328` specifically for `Unsize`); rejects impls of `#[rustc_specialization_trait]` without `#![feature(specialization)]` or `#![feature(min_specialization)]`; and enforces `#[rustc_impl_restriction]` (`impl_restriction.is_allowed_in(...)`).
     - `enforce_empty_impls_for_marker_traits` (L118-139): emits `E0715` (`"impls for marker traits cannot contain items"`) whenever `trait_def.is_marker` and `!tcx.associated_item_def_ids(trait_def_id).is_empty()`.
     - `always_applicable::check_negative_auto_trait_impl` (`always_applicable.rs` `14210df0e` L88-139 / `0259d5e9a` L84-135): emits `E0366` / `E0367` if a negative auto-trait impl specializes parameters or adds bounds not implied by the ADT definition.
   - `check_object_overlap` (`mod.rs` L192-248): if `trait_ref.self_ty()` is `ty::Dynamic(data, ..)`, iterates over all `ExistentialPredicate::{Trait, AutoTrait}` components; for any dyn-compatible component, traverses `elaborate::supertrait_def_ids(tcx, component_def_id)` and emits **`E0371`** (`"the object type ... automatically implements the trait ..."`) if `trait_def_id` appears (verified empirically in probe `b05_object_overlap_supertrait_e0371`: `impl Sup for dyn Sub {}` -> `compile_rc = 1`, `E0371`).
   - `unsafety::check_item` (`unsafety.rs` `14210df0e` L13-122 / `0259d5e9a` L14-123): checks impl `Safety` against trait `Safety` (with a special check in `0259d5e9a` L24-34 / `14210df0e` L23-33 requiring `unsafe impl Copy` when `self_ty.has_unsafe_fields()`), emitting `E0199` (`unsafe impl` for safe trait without `#[may_dangle]`), `E0200` (missing `unsafe impl` for unsafe trait), or `E0569` (missing `unsafe impl` when a generic parameter carries `#[may_dangle]`, `pure_wrt_drop`).
   - `tcx.ensure_result().orphan_check_impl(impl_def_id)`.
   - `builtin::check_trait` (`builtin.rs` L32-54): runs structural compiler-magic validation for `Drop`, `AsyncDrop`, `Copy`, `Unpin` (under `pin_ergonomics`, rejecting `#[pin_v2]` ADTs), `ConstParamTy`, `CoerceUnsized`, `Reborrow`, `CoerceShared`, `DispatchFromDyn` (requiring `repr(transparent)`-equivalent pointer layout), and `CoercePointeeValidated`. Note `Drop` (`builtin.rs` L62-78) requires `ty::Adt(def, _)` with `def.did().is_local()` (rejecting fundamental wrappers like `Box<Local>` even if `Drop` were local), and `Copy` (`builtin.rs` L80-131) rejects non-ADTs (`E0206`), types with destructors (`E0184`), and fields failing `Copy`.

#### 1.2 Inherent Impl Locality & Overlap (`inherent_impls.rs`, `inherent_impls_overlap.rs`)

Inherent impls bypass orphan unwrapping completely:
- **Crate-Locality Gate (`inherent_impls.rs` `0259d5e9a` L64-232 / `14210df0e` L65-220):** `InherentCollect::check_item` strips free type aliases (`peel_off_free_alias_tys`) and pattern types (`ty::Pat`), then requires:
  - For `ty::Adt`, `ty::Foreign`, or `ty::Dynamic` with principal trait: `ty_def_id.is_local()` (unless `#![feature(rustc_attrs)]` and the type carries `#[rustc_has_incoherent_inherent_impls]` and every item carries `#[rustc_allow_incoherent_impl]`); otherwise emits **`E0116`** (`"cannot define inherent `impl` for a type outside of the crate where the type is defined"`—verified in `b04_inherent_impl_foreign_type_e0116`, `compile_rc = 1`, `E0116`).
  - For primitives, slices, arrays, pointers, references, tuples, `str`, `!`, `fn` pointers (`L191-204`): requires `tcx.hir_rustc_coherence_is_core()` or `#[rustc_allow_incoherent_impl]`, otherwise emitting `E0390`.
  - For type parameters, projections, opaques, or un-principaled `dyn` (`L187-214`): emits `E0118` / `E0785`.
- **Inherent Overlap Check (`inherent_impls_overlap.rs` L15-345):** For every `Enum`, `Struct`, `Trait`, or `Union` item in the crate, `InherentOverlapChecker::check_item`:
  1. Checks each single impl for duplicate item names via `normalize_to_macros_2_0()` (`check_for_duplicate_items_in_impl` L72-102 -> **`E0592`**).
  2. Uses $O(n^2)$ pairwise checking when `impls.len() < 500` (`ALLOCATING_ALGO_THRESHOLD = 500`, L191) or builds union-find-like connected components over shared unhygienic item `Symbol`s when `impls.len() >= 500` (`L207-342`).
  3. Only when two inherent impls share a hygienically identical `(namespace, normalized_ident)` pair (`impls_have_common_items` L39-70) does it invoke `traits::overlapping_inherent_impls(tcx, impl1, impl2, SkipLeakCheck::Yes, overlap_mode)` (`L157-169`). If self types unify (`b03_inherent_impls_overlap_e0592`: `impl<T> Wrap<T> { fn dup }` + `impl Wrap<u32> { fn dup }`), it emits **`E0592`** (`"duplicate definitions with name `dup`"`), whereas disjoint self types (`b02_inherent_impls_disjoint_ok`: `Wrap<u32>` vs. `Wrap<i32>`) compile cleanly (`B02=10,-3`).

#### 1.3 Attribute Collection (`collect.rs`)

In `compiler/rustc_hir_analysis/src/collect.rs` (`0259d5e9a` L1114-1191; `14210df0e` L894-949), `trait_def` collects `#[marker]` onto `ty::TraitDef.is_marker` (`!is_alias && find_attr!(attrs, Marker)`) and `#[fundamental]` onto `ty::TraitDef.is_fundamental` (`find_attr!(attrs, Fundamental)`). For ADTs, `def.is_fundamental()` reflects `#[fundamental]` on `struct`/`enum`/`union` definitions (`Box<T, A>` at `library/alloc/src/boxed.rs` `14210df0e` L228 / `0259d5e9a` L302; `Pin<Ptr>` at `library/core/src/pin.rs` `14210df0e` L1088 / `0259d5e9a` L1087).

---

### 2. Covered-Type Orphan Checking (`orphan_check_trait_ref`, `E0117`, `E0210`) & `OwnedBox` Revision Delta

Basis: normative (`reference`, `rfcs`) + source (`rustc_next_trait_solver`, `rustc_hir_analysis`) + execution + derived (Lean mechanization)

#### 2.1 Normative Rule (RFC 1023 + RFC 2451)

The Rust Reference (`src/items/implementations.md` L161-174, `r[items.impl.trait.orphan-rule.def]`) and RFC 2451 (`text/2451-re-rebalancing-coherence.md` L185-226) state that `impl<P1..=Pm> Trait<T1..=Tn> for T0` is valid in crate $C$ if and only if either `Trait` is local to $C$, or:
1. At least one input type in `[T0, T1, ..., Tn]` (ordered `Self` first, then trait type arguments linearly) is a **local type** (a nominal `struct`/`enum`/`union` defined in $C$, or a `#[fundamental]` type constructor applied recursively to a local type), let $T_i$ be the first such input; and
2. **No uncovered type parameter** $P_j$ appears before that first local type (i.e., outside non-fundamental constructors prior to reaching the first local type).

Crucially, `impl<T> ForeignTrait<LocalType> for Vec<T>`—banned under RFC 1023—is **admitted** under RFC 2451 because `Vec<T>` is non-fundamental and therefore **covers** `T` prior to `LocalType`. Any upstream impl in `alloc` that could collide with it would have to write `impl<T, U> ForeignTrait<U> for Vec<T>`, which leaves `U` uncovered and is already a major SemVer-breaking change (`2451-re-rebalancing-coherence.md` L202-226, L246-258).

#### 2.2 Exact Compiler Algorithm (`OrphanChecker::visit_ty`)

In `compiler/rustc_next_trait_solver/src/coherence.rs` (`14210df0e` L221-469; `0259d5e9a` L222-478), `orphan_check_trait_ref` expects all impl generic parameters to be instantiated with fresh inference variables (`orphan.rs` L325-326: `if trait_ref.has_param() { panic!(...) }`), then walks `trait_ref` (`[Self, T1, ..., Tn]`) with `OrphanChecker::visit_ty`:

1. **Shallow resolution & lazy normalization (`L326-331`):** Calls `infcx.shallow_resolve(ty)` and `(self.lazily_normalize_ty)(ty)` (`orphan.rs` L328-340 normalizes non-rigid type aliases in an empty `ParamEnv` when evaluation succeeds cleanly, keeping `user_ty` if normalization leaves an infer var or errors).
2. **Primitive & structural non-local cutoffs (`L334-348`):** `Bool`, `Char`, `Int`, `Uint`, `Float`, `Str`, `Pat`, `FnPtr`, `Array`, `Slice`, `RawPtr`, `Never`, `Tuple`, and `UnsafeBinder` call `self.found_non_local_ty(ty)`—appending `(ty, self.in_self_ty.into())` and returning `ControlFlow::Continue(())` **without** visiting inner element types. Consequently, `(LocalType, u32)` or `[LocalType; 2]` or `*const LocalType` is **not** local (`a19_tuple_containing_local_type_rejected_e0117` -> `E0117`).
3. **Uncovered type parameters (`ty::Placeholder | ty::Bound | ty::Infer`, `L352-359`):**
   - In `InCrate::Local { .. }`: calls `found_uncovered_ty_param(ty)`, returning `ControlFlow::Break(UncoveredTyParam(ty))`. `orphan_check_trait_ref` (L242-253) then re-runs `visit_with` with `search_first_local_ty = true` solely to compute `local_ty` for a better **`E0210`** diagnostic (`error[E0210]: type parameter T must be covered by another type when it appears before the first local type (LocalType)`).
   - In `InCrate::Remote`: immediately returns `ControlFlow::Break(LocalTy(ty))`, conservatively assuming a remote crate could instantiate the inference variable with its own local nominal type.
4. **Rigid aliases & opaques (`ty::Alias`, `L366-408`):**
   - If the alias contains `HAS_TY_PLACEHOLDER | HAS_TY_BOUND | HAS_TY_INFER`, `InCrate::Remote` breaks with `LocalTy`, while `InCrate::Local` breaks with `UncoveredTyParam`—**except** when `kind` is `ty::Projection` and `mode == OrphanCheckMode::Compat`, which returns `Continue(())` and emits the backward-compatibility lint `UNCOVERED_PARAM_IN_PROJECTION` (`orphan.rs` L29-49; linked upstream to `#99554` and `#124559`).
   - Otherwise, rigid opaque types (`impl Trait`) are unconditionally treated as **non-local even inside their defining crate** (`L389-407`), preventing type-checking cycles and preventing hidden-type swaps from becoming SemVer-breaking coherence changes.
5. **Fundamental unwrapping (`ty::Ref`, `ty::Adt`, `L413-425`):**
   - `ty::Ref(_, ty, _)` unconditionally recurses into `ty.visit_with(self)`.
   - `ty::Adt(def, args)`:
     - If `self.def_id_is_local(def.def_id())`: immediately returns `ControlFlow::Break(LocalTy(ty))` (admissible!).
     - Else if `def.is_fundamental()`:
       - On `14210df0e` (`L415`): unconditionally executes `args.visit_with(self)`.
       - On `0259d5e9a` (`L418-421`): checks `self.infcx.cx().as_adt_lang_item(def.def_id())`; if `Some(SolverAdtLangItem::OwnedBox)`, visits **only `args.type_at(0)`** (`T`), ignoring the allocator type parameter `A`.
     - Else (non-fundamental foreign ADTs like `Vec<T>`, `Option<T>`, `ForeignWrapper<T>`): calls `found_non_local_ty(ty)` and returns `ControlFlow::Continue(())` **without** visiting `args`.
6. **`Foreign`, `Dynamic`, and `Const` (`L426-477`):** `ty::Foreign(def_id)` and `ty::Dynamic(tt, ..)` succeed iff `def_id` / `principal_def_id` is local. `visit_const` always returns `ControlFlow::Continue(())` because constant values live in primitive/shared domains and cannot encode crate-local nominal identities.

#### 2.3 Empirical Multi-Crate Orphan Matrix & `OwnedBox` Revision Discriminator

Executed live against compiled `libup.rlib` (`ForeignTrait<Rhs = ()>`, `ForeignType`, `ForeignWrapper<T>`) in `support/probe_coherence_orphan_fundamental_neg.py` (`support/probe_results.json`):

| Case ID | Impl Header (`--extern up=libup.rlib`) | `rustc` `rc` | Error | Mechanism Verified |
| :--- | :--- | ---: | :--- | :--- |
| `a01` | `impl ForeignTrait for LocalType` | `0` | — | Direct `LocalTy` at `Self` (`A01=local`) |
| `a02` | `impl ForeignTrait for Box<LocalType>` | `0` | — | `#[fundamental]` `Box` unwraps to `LocalType` (`A02=box_local`) |
| `a03` | `impl ForeignTrait for &LocalType` | `0` | — | Built-in `ty::Ref` unwraps to `LocalType` (`A03=ref_local`) |
| `a04` | `impl ForeignTrait for &mut LocalType` | `0` | — | Built-in mutable `ty::Ref` unwraps (`A04=mut_ref_local`) |
| `a05` | `impl ForeignTrait for Pin<&LocalType>` & `Pin<Box<LocalType>>` | `0` | — | Multi-layer `#[fundamental]` unwrapping (`A05=pin_ref_local,pin_box_local`) |
| `a06` | `impl ForeignTrait for Vec<LocalType>` | `1` | `E0117` | Non-fundamental `Vec` stops traversal (`NonLocalInputType`) |
| `a07` | `impl ForeignTrait for up::ForeignWrapper<LocalType>` | `1` | `E0117` | Non-fundamental foreign ADT stops traversal |
| `a08` | `impl ForeignTrait<LocalType> for u32` | `0` | — | `u32` is `NonLocalInput` (`Continue`), then `LocalType` in `traitArgs` hits `LocalTy` |
| `a09` | `impl<T> ForeignTrait<LocalType> for Vec<T>` | `0` | — | RFC 2451: `Vec<T>` covers `T` (`Continue`) before `LocalType` (`A09=vec_t_local_arg`) |
| `a10` | `impl<T> ForeignTrait<LocalType> for T` | `1` | `E0210` | Uncovered `T` at `Self` breaks before `LocalType` |
| `a11` | `impl<T> ForeignTrait<LocalType> for Box<T>` | `1` | `E0210` | `#[fundamental]` `Box` unwraps to uncovered `T` (`Box` does not cover `T`) |
| `a12` | `impl<T> ForeignTrait<T> for LocalType` & `LocalGen<T>` | `0` | — | `LocalTy` at `Self` short-circuits before uncovered `T` in `traitArgs` |
| `a13` | `impl<T> ForeignTrait<T> for up::ForeignType` | `1` | `E0210` | `ForeignType` (`Continue`), then uncovered `T` (`UncoveredTyParam`) |
| `a14` | `impl ForeignTrait for up::ForeignType` | `1` | `E0117` | Both `ForeignType` and `()` (`Rhs`) are `NonLocalInputType` |
| `a15` | `impl ForeignTrait for Box<u32, LocalAlloc>` (`feature(allocator_api)`) | **`0`** | — | On `14210df0e`, `args.visit_with(self)` visits `A = LocalAlloc` (`A15=box_u32_local_alloc`); `0259d5e9a` restricts `OwnedBox` to `args.type_at(0)` (`E0117`) |
| `a19` | `impl ForeignTrait for (LocalType, u32)` | `1` | `E0117` | `ty::Tuple` stops traversal without visiting tuple fields |
| `a20` | `impl<T> ForeignTrait<T> for Box<LocalType>` | `0` | — | Fundamental unwrap on `Self` reaches `LocalType` before `T` (`A20=box_local_before_t`) |

---

### 3. `#[fundamental]` Types vs. Traits, `trait_ref_is_knowable`, and Foreign Auto-Trait `E0321`

Basis: source + execution + derived (Lean mechanization)

#### 3.1 Why `#[fundamental]` Applies Both to Type Constructors and to Traits

`#[fundamental]` carries dual, symmetric SemVer obligations depending on whether it annotates a type constructor or a trait (`rust-lang/reference/src/glossary.md` L76-85; `rustc_next_trait_solver/src/coherence.rs` L48-98):

- **On a `#[fundamental]` type constructor (`Box<T, A>`, `Pin<Ptr>`, and built-in `&T`, `&mut T`):** Downstream crates are granted ownership over `Wrapper<LocalType>`. Consequently, the defining crate (`core`/`alloc`) permanently forfeits the SemVer right to add blanket impls (`impl<T> ForeignTrait for Wrapper<T>`) in future releases (`library/core/src/pin.rs` `0259d5e9a` L1701-1711 explains why `Pin::deref_mut` had to route through a non-fundamental `PinHelper<Ptr>` wrapper after `#85099`, preventing downstream crates from implementing `DerefMut` for `Pin<&LocalType>`).
- **On a `#[fundamental]` trait (`Fn`, `FnMut`, `FnOnce`, `FnPtr` at `library/core/src/ops/function.rs` `0259d5e9a` L73, L160, L239, L350; `Sized`):** `trait_ref_is_knowable` (`rustc_next_trait_solver/src/coherence.rs` L48-98) determines whether an unsatisfied trait obligation `trait_ref` can be treated as *definitely false across all future upstream and downstream versions* during coherence:
  1. First, `orphan_check_trait_ref(infcx, trait_ref, InCrate::Remote, ...)` checks if a downstream or cousin crate could implement `trait_ref`; if `Ok(())`, returns `Err(Conflict::Downstream)` (`L58-63`).
  2. Second, `if trait_ref_is_local_or_fundamental(infcx.cx(), trait_ref)` (`trait_ref.def_id.is_local() || tcx.trait_is_fundamental(trait_ref.def_id)`, `L65-72, L96-98`), returns **`Ok(Ok(()))` (`knowable`) immediately**! Marking `Fn`/`FnMut`/`FnOnce` as `#[fundamental]` (`#[fundamental] // so that regex can rely that &str: !FnMut`, `function.rs` L73, L160, L239) is a SemVer promise by `core` never to retroactively add `impl FnMut<Args> for &str` (or any existing foreign type).
  3. Third, for remote non-fundamental traits, `trait_ref_is_knowable` passes (`Ok(Ok(()))`) if and only if `orphan_check_trait_ref(..., InCrate::Local { Proper }, ...)` passes (`L82-93`); otherwise it returns `Err(Conflict::Upstream)` (`upstream crates may add a new impl ... in future versions`).

Live probes `a17` vs. `a18` isolate this exact branch in `trait_ref_is_knowable`:
- `a17_fundamental_fnmut_trait_knowable_ok`: `impl<F: FnMut(char) -> bool> Pattern for F` + `impl Pattern for &str` compiles and runs (`compile_rc = 0`, `A17=fnmut,str_ref`).
- `a18_non_fundamental_foreign_trait_knowability_e0119`: replacing `FnMut` with ordinary foreign trait `up::ForeignBlanketTrait` (`is_fundamental == false`) fails with **`E0119`** and `note: upstream crates may add a new impl of trait up::ForeignBlanketTrait for type &str in future versions`.

#### 3.2 Foreign Auto-Trait Bypass (`E0321`)

Immediately after `orphan_check`, `orphan_check_impl` (`compiler/rustc_hir_analysis/src/coherence/orphan.rs` `0259d5e9a` L99-288; `14210df0e` L85-271) applies a strictly tighter check when `tcx.trait_is_auto(trait_def_id)` is `true`:
- If `trait_def_id` is remote (`!trait_def_id.is_local()`), `NonlocalImpl::Allow` accepts **only** `ty::Adt(self_def, _)` with `self_def.did().is_local()` or `ty::Foreign(did)` with `did.is_local()`.
- `ty::Ref`, `Box<Local>`, `Pin<Local>`, tuples, arrays, and primitives all map to `NonlocalImpl::DisallowOther` (`E0321`), preventing downstream crates from overriding structural auto-trait composition (`impl !Foo for (A, B)` breaking `two_foos` generic reasoning, `#22978`, `orphan.rs` L60-91). Probe `a16_auto_trait_bypasses_fundamental_e0321` confirms `unsafe impl Send for Box<LocalType> {}` fails `E0321`.

---

### 4. Trait Overlap Detection, `#[marker]` Zero-Item Enforcement, and `SpecializationGraph`

Basis: source + execution + derived (Lean mechanization)

#### 4.1 `Children::insert` and `overlapping_trait_impls`

When populating `specialization_graph_of(def_id)` (`compiler/rustc_trait_selection/src/traits/specialize/mod.rs` L423-455; `specialization_graph.rs` L76-193), `rustc` sorts impls with foreign `CrateNum` before local `LocalDefId`s and inserts each local impl via `sg.insert`:

1. **Fast rejection (`rustc_trait_selection/src/traits/coherence.rs` `0259d5e9a` L112-134):** `overlapping_trait_impls` first calls `DeepRejectCtxt::relate_infer_infer(tcx).args_may_unify(impl1_args, impl2_args)` without allocating an `InferCtxt`. Disjoint outer type constructors or argument counts exit immediately with `None`.
2. **Header unification & obligation feasibility (`overlap`, `coherence.rs` `0259d5e9a` L172-265 / `14210df0e` L243-346):** If `fast_reject` cannot rule out overlap, `overlap` instantiates both impl headers with fresh inference variables (`fresh_impl_header`) inside `TypingMode::Coherence`, equates them (`equate_impl_headers` L268-288 with `DefineOpaqueTypes::Yes`), collects all instantiated where-clause obligations, and checks `impl_intersection_has_impossible_obligation` (`L323-370`) whenever `overlap_mode.use_implicit_negative()` holds. Any definite `TraitError` (`is_true_error()`) proves the intersection empty (`None`), whereas ambiguities—including `CandidateSource::CoherenceUnknowable`—keep the overlap alive and collect `IntercrateAmbiguityCause::{UpstreamCrateUpdate, DownstreamCrate}` diagnostic hints (`compute_intercrate_ambiguity_causes`, L601-744).
3. **`impls_are_allowed_to_overlap` (`rustc_middle/src/ty/mod.rs` `0259d5e9a` L1935-1970 / `14210df0e` L1689-1724):** Before consulting specialization ordering (`tcx.specializes`), `Children::insert` (`specialization_graph.rs` L148-156) calls `tcx.impls_are_allowed_to_overlap(impl_def_id, possible_sibling)`:
   - Opposite polarities (`Positive` vs. `Negative`) return `None`, falling through to `report_negative_positive_conflict` -> **`E0751`** (`specialize/mod.rs` L495-515, confirmed by `c10_negative_positive_conflict_e0751`).
   - Same-polarity pairs where both impls target a trait with `trait_def.is_marker == true` return `Some(ImplOverlapKind::Permitted { marker: true })`, causing `Children::insert` to return `Ok((false, false))` immediately and install both impls as unordered siblings.

#### 4.2 Why `#[marker]` Requires `E0714` and `E0715`

Permitting arbitrary overlapping blanket impls without a specialization tree (`b06_marker_trait_overlap_allowed_ok`: `#[marker] trait Mark {}` with `impl<T: Copy> Mark for T {}` and `impl<T: Clone> Mark for T {}` both matching `42u32`, `compile_rc = 0`, `B06=marker_ok`) is coherent **if and only if** the trait carries zero associated items:
- **Definition-site check (`wfcheck.rs` `0259d5e9a` L1117-1131 / `14210df0e` L1178-1192):** Iterates `tcx.associated_item_def_ids(def_id)` on `trait_def.is_marker` and emits **`E0714`** (`"marker traits cannot have associated items"`).
- **Impl-site defense-in-depth (`coherence/mod.rs` `0259d5e9a` L118-139 / `14210df0e` L116-137):** `enforce_empty_impls_for_marker_traits` checks `!tcx.associated_item_def_ids(trait_def_id).is_empty()` on every impl and emits **`E0715`** (`"impls for marker traits cannot contain items"`).
- Probes `b07` and `b08` confirm both `E0714` and `E0715` fire whenever a `#[marker]` trait declares a method or associated constant and an impl exists (`error_codes = ["E0714", "E0715"]`).

---

### 5. Negative Impls & `with_negative_coherence` (`OverlapMode`, Disjointness, and SemVer)

Basis: source + execution + derived (Lean mechanization)

#### 5.1 `OverlapMode` and `impl_intersection_has_negative_obligation`

`compiler/rustc_middle/src/traits/specialization_graph.rs` (L51-86) defines three overlap modes via `OverlapMode::get(tcx, trait_id)`:

| `OverlapMode` | Activation | `use_negative_impl()` | `use_implicit_negative()` |
| :--- | :--- | :---: | :---: |
| `OverlapMode::Stable` | Default Rust (no feature gate) | `false` | `true` |
| `OverlapMode::WithNegative` | `#![feature(with_negative_coherence)]` | `true` | `true` |
| `OverlapMode::Strict` | `#![feature(with_negative_coherence)]` + `#[rustc_strict_coherence]` | `true` | `false` |

In `compiler/rustc_trait_selection/src/traits/coherence.rs` (`0259d5e9a` L180-191, L388-592; `14210df0e` L252-263, L494-699), when `overlap_mode.use_negative_impl()` is `true`, `overlap` tests `impl_intersection_has_negative_obligation` symmetrically in both directions `(impl1, impl2)` and `(impl2, impl1)` **before** running implicit negative checking:
1. Unifies fresh headers of `impl1` and `impl2` under `TypingMode::Coherence` (`equate_impl_headers`).
2. Drops equate obligations and region constraints (`FIXME(with_negative_coherence)` at `0259d5e9a` L417-423) and calls `plug_infer_with_placeholders` (`L453-559`) to replace every remaining type, const, and region inference variable with universal `Placeholder`s in `UniverseIndex::ROOT`.
3. Instantiates `impl1`'s `param_env` with those placeholders (`L439-441`) and elaborates all where-clauses of `impl2` (`util::elaborate`, `L443-450`).
4. For each clause, `try_prove_negated_where_clause` (`L561-592`) flips polarity via `clause.as_predicate().flip_polarity(tcx)`, forks `infcx` into `TypingMode::non_body_analysis()` (`FIXME(#132279)` at L574-576), evaluates the negated goal (`!Trait` predicate) via `evaluate_obligations_error_on_ambiguity()`, and verifies `ocx.resolve_regions(...)` is empty (`L591`). If any negated predicate holds, `overlap` returns `None` (provably disjoint).

#### 5.2 Empirical Separation of `OverlapMode::Stable` vs. `OverlapMode::WithNegative`

Live `rustc` execution in `support/probe_coherence_orphan_fundamental_neg.py` cleanly exposes the exact boundary between `use_implicit_negative()` (active in `Stable`) and `use_negative_impl()` (active only in `WithNegative`):

| Case ID | Scenario | `with_negative_coherence`? | `rustc` `rc` | Outcome & Reason |
| :--- | :--- | :---: | ---: | :--- |
| `c01` | `struct Local(u32)` (no `!Send`), `impl<T: Send> M for T` + `impl M for Local` | No | `1` | `E0119` (`Local: Send` holds via auto-trait synthesis) |
| `c02` | `struct Local(u32)` + `impl !Send for Local {}`, `impl<T: Send> M for T` + `impl M for Local` | **No (`Stable`)** | **`0`** | **`C02=1,2`** — `Local` is crate-local, so `Local: Send` is `knowable` (`use_implicit_negative` proves `Local: Send` impossible without `with_negative_coherence`!) |
| `c03` | Same with `with_negative_coherence` | Yes | `0` | `C03=1,2` |
| `c04` | Custom trait `impl !CustomBound for Local {}` + overlapping blanket | Yes | `0` | `C04=10,20` |
| `c05` | Foreign trait `impl !up::ForeignBlanketTrait for Local {}` + overlapping blanket | Yes | `0` | `C05=200` (orphan-allowed because `Local` is local!) |
| `c06a` | Foreign crate `up_neg::UpNegStruct` (`impl !UpNegTrait for UpNegStruct`) + `impl<T: UpNegTrait> CrossClassify for T` + `impl CrossClassify for UpNegStruct` | **No (`Stable`)** | **`1`** | **`E0119`** — `UpNegStruct` is foreign, so `Stable` ignores `up_neg`'s explicit negative impl and hits `Conflict::Upstream` |
| `c06b` | Same as `c06a` + `UpNoSend` (`impl !Send for UpNoSend`) | **Yes** | **`0`** | **`C06B=up_nosend,up_negstruct`** — `WithNegative` proves `UpNoSend: !Send` and `UpNegStruct: !UpNegTrait` across crate boundary! |
| `c07` | `impl<T: Send> Classify for T` + `impl<T> Classify for Rc<T>` | **No (`Stable`)** | **`1`** | **`E0119`** (`upstream crates may add a new impl of trait std::marker::Send for type std::rc::Rc<_>`) |
| `c08` | Same `Rc<T>` pair | **Yes** | **`0`** | **`C08=1,2`** (`alloc`'s `impl<T, A> !Send for Rc<T, A>` proves `Rc<!0>: !Send`) |
| `c09` | `impl !Foo for Local { fn bar(&self) {} }` | N/A | `1` | `E0749` (`check/check.rs:1326`: negative impls cannot have items) |
| `c10` | `impl Foo for Local {}` + `impl !Foo for Local {}` | N/A | `1` | `E0751` (`specialize/mod.rs:495`: positive + negative conflict) |
| `c11` | `struct Wrap<T>(T); impl !Send for Wrap<u32> {}` | N/A | `1` | `E0366` (`always_applicable.rs:160`: negative auto-trait impl cannot specialize) |

Notice the SemVer guarantee verified in `c06b` and `c08` (and proved in Lean theorem `neg_impl_semver_monotone`): once an upstream crate publishes `impl !Trait for Ty`, removing that negative impl or adding `impl Trait for Ty` is a major SemVer-breaking change (which would trigger `E0751` against its own negative impl). Downstream crates under `with_negative_coherence` can therefore rely monotonically on foreign negative impls without losing separate-compilation soundness.

---

### 6. Real `google/zerocopy` First-Customer Coherence Patterns

Basis: source (`google/zerocopy@e5a9824d87f7daa5282969a25a8bbca9af985400`) + execution + derived (Lean mechanization)

Inspecting `google/zerocopy` at `e5a9824d87f7daa5282969a25a8bbca9af985400` reveals three distinct stable-Rust coherence engineering techniques across `zerocopy/src/pointer/transmute.rs`, `zerocopy/src/pointer/invariant.rs`, and `zerocopy/src/impls.rs`:

1. **Phantom Reason-Marker Partitioning (`R`) Across Disjoint Conditional Blankets (`transmute.rs`, `invariant.rs`):**
   Because `zerocopy` compiles on stable Rust (without `#[marker]`, `specialization`, or `with_negative_coherence`), multiple blanket impls on the same `(Src, Dst)` pair would collide under `E0119` (`d02_zerocopy_style_omitting_reason_param_triggers_e0119` confirms `E0119` immediately when `R` is removed). `zerocopy` avoids overlap by appending a type-level reason parameter `R` instantiated with disjoint uninhabited enums or tuples in each blanket header:
   - `Read<A: Aliasing, R>` (`invariant.rs` L273-286):
     - `impl<A: Aliasing, T: ?Sized + Immutable> Read<A, BecauseImmutable> for T {}` (L275)
     - `impl<T: ?Sized> Read<Exclusive, BecauseExclusive> for T {}` (L276)
     Both apply to any `T: ?Sized + Immutable` when `A = Exclusive`, yet `BecauseImmutable` vs. `BecauseExclusive` fail `equate_impl_headers`.
   - `MutationCompatible<Src: ?Sized, A: Aliasing, SV, DV, R>` (`transmute.rs` L194-232):
     - `unsafe impl<Src: ?Sized, Dst: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R> MutationCompatible<Src, A, SV, DV, (BecauseRead, R)> for Dst where Src: Read<A, R>, Dst: Read<A, R>` (L200-206)
     - `unsafe impl<Src: ?Sized, Dst: ?Sized, A: Aliasing, SV: Validity, DV: Validity> MutationCompatible<Src, A, SV, DV, BecauseSharedCompatible> for Dst where Src: TransmuteFrom<Dst, DV, SV>, Dst: TransmuteFrom<Src, SV, DV> + SharedCompatible<Src>` (L223-229)
     Here `(BecauseRead, R)` (2-tuple) vs. `BecauseSharedCompatible` (uninhabited enum) are rejected in `O(1)` by `DeepRejectCtxt` before any where-clause evaluation.
   - `TryTransmuteFromPtr<Src: ?Sized, A: Aliasing, SV: Validity, DV: Validity, C: CastExact<Src, Self>, R>` (`transmute.rs` L114-181):
     - Blanket `(BecauseMutationCompatible, R)` (`L153-163`) vs. `BecauseImmutable` (`L172-181`, restricted to `A = Shared`).
   - Live probe `d01_zerocopy_style_disjoint_reason_markers_and_occurs_check_ok` replicates this complete 4-trait lattice and executes cleanly (`compile_rc = 0`, `D01=ok,ok,ok`).

2. **Occurs-Check Asymmetry on `SharedCompatible<T>` (`transmute.rs` L216-261, L411, L444):**
   `SharedCompatible<T: ?Sized>` exposes symmetric wrapper relationships without an explicit reason marker:
   - `unsafe impl<T: ?Sized> SharedCompatible<T> for T {}` (`L219`)
   - `unsafe impl<T: ?Sized> SharedCompatible<T> for ManuallyDrop<T> {}` (`L258`)
   - `unsafe impl<T: ?Sized> SharedCompatible<ManuallyDrop<T>> for T {}` (`L260`)
   - Symmetric pairs `(T, Unalign<T>)` / `(Unalign<T>, T)` (`L411`) and `(T, Wrapping<T>)` / `(Wrapping<T>, T)` (`L444`).
   Coherence accepts all seven blankets simultaneously because unifying `(T₁, T₁)` with `(T₂, ManuallyDrop<T₂>)` requires `T₂ = ManuallyDrop<T₂>`, and unifying `(T₁, ManuallyDrop<T₁>)` with `(ManuallyDrop<T₂>, T₂)` requires `T₁ = ManuallyDrop<ManuallyDrop<T₁>>`—both rejected by the unification **occurs check** in `equate_impl_headers`.

3. **Foreign-Type Blanket Impls and Downstream `#[fundamental]` Composition (`impls.rs`):**
   Because `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`, `Unaligned`, and `HasTag` are local to `zerocopy`, `zerocopy/src/impls.rs` freely implements them on foreign types including `Box<T>` (`Immutable`, L306), `Option<Box<T>>` (`TryFromBytes`/`FromZeros`, L336-341), `Option<&T>` / `Option<&mut T>` (L344-350), `ManuallyDrop<T>` (L735-761), and `&T` / `&mut T` (L981-982). Downstream user crates deriving or implementing a `zerocopy`-style trait for `Box<UserStruct>`, `&UserStruct`, or `Pin<&UserStruct>` succeed via `#[fundamental]` unwrapping (`d03a`, `D03=user,box_user,ref_user,pin_ref_user`), whereas `Vec<UserStruct>` fails `E0117` (`d03b`). Note that for `KnownLayout`/`HasTag` or custom pointer wrappers, downstream crates cannot overlap `zerocopy`'s existing blanket `Immutable for Box<T>`—`#[fundamental]` enables downstream crates to implement *additional* traits (or trait combinations on `Box<UserStruct>`) that `zerocopy` did not blanket-impl.

---

### 7. Kernel-Checked Lean `v4.34.1` Formalization and Link to `joshlf/anneal`

Basis: derived (Lean `v4.34.1` kernel check) + source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

#### 7.1 Mechanized Theorems and Purity Audit (`CoherenceOrphanFundamentalAndNegativeImplsSoundness.lean`)

`support/CoherenceOrphanFundamentalAndNegativeImplsSoundness.lean` (1,727 lines, 78,273 bytes) mechanizes the full multi-crate coherence model in standalone Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with **0** warnings/errors under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`. Direct `Lean.Meta.MetaM` inspection of all 874 local environment constants confirms:
- **0** `._unsafe_rec` auxiliary compiler constants (every `def` carries `noncomputable` explicitly; zero `noncomputable section`, zero `deriving` on recursive inductives);
- **0** `partial` or `unsafe` definitions;
- **0** `sorryAx`, **0** `Classical.choice`, **0** `Quot.sound`, **0** `Lean.ofReduceBool`, **0** `Lean.trustCompiler`, **0** `omega`, **0** `bv_decide`, **0** `native_decide`.

| Lean Theorem (`RustcCoherence.*`) | Formal Property / Counterexample Proved | Kernel Axioms |
| :--- | :--- | :--- |
| `orphan_check_cross_crate_disjoint` | **Cross-Crate Orphan Separation:** For `c₁ ≠ c₂` avoiding each other's ADTs/traits, passing `orphanCheck` (`AllArgs` or `ElemOnly`) guarantees `instTraitRef σ₁ tr₁ ≠ instTraitRef σ₂ tr₂` for all `(σ₁, σ₂)`. | `[propext]` |
| `orphan_dag_unrelated_crates_disjoint` | **Crate-DAG Separation:** Lifts `orphan_check_cross_crate_disjoint` to any two unrelated crates (`¬ UpstreamOf c₁ c₂ ∧ ¬ UpstreamOf c₂ c₁`) with `TraitRefScopedInCrate`. | `[propext]` |
| `pin_box_mut_shared_ref_local_passes` | Arbitrary nested fundamental unwrapping (`Pin<Box<&mut &Local>>`) passes `orphanCheck` in both `BoxMode`s. | `[propext]` |
| `vec_local_blocked_e0117` & `foreign_wrapper_local_blocked_e0117` | Non-fundamental `Vec<Local>` and `ForeignWrapper<Local>` fail `orphanCheck` (`nonLocalInput`). | `[propext]` |
| `ce_vec_local_collides_with_alloc_blanket` | **Non-Fundamental `E0117` Counterexample:** `alloc` (`crate 0`) validly implements `Vec<T>`, so admitting `Vec<Local>` in `crate 2` produces a ground collision on `Vec<Local>`. | `[propext]` |
| `rfc2451_vec_t_before_local_arg_passes` | RFC 2451 admission of `impl<T> ForeignTrait<Local> for Vec<T>` (`Vec<T>` covers `T` before `Local`). | `[propext]` |
| `uncovered_t_and_box_t_rejected_e0210` & `ce_uncovered_t_collides_with_sibling` | Rejects `T` and `Box<T>` before `Local` (`E0210`), and constructs a concrete sibling-crate collision on `(LocalB, LocalA)` if admitted. | `[]` / `[propext]` |
| `owned_box_allocator_revision_delta` | Exact `14210df0e` (`BoxMode.allArgs`, passes) vs. `0259d5e9a` (`BoxMode.elemOnly`, fails) separation on `Box<u32, LocalAlloc>`. | `[propext]` |
| `neg_impl_disjoint_sound` & `neg_impl_semver_monotone` | **Negative-Impl Mutual Exclusion & SemVer Monotonicity:** Explicit `impl !reqTrait for specPat` guarantees disjointness under `posNegDisjoint` (`E0751`) across **every** valid `SemVerExtension w₁ w₂`. | `[]` (0 axioms!) |
| `stable_vs_with_negative_and_fundamental_trait_discrimination` | Mechanizes all five `OverlapMode` regimes (`Local: !Send` under `Stable`, `Rc<T>: !Send` failing `Stable` and passing `WithNegative`, `FnMut` on `&str` passing vs. non-fundamental trait failing). | `[propext]` |
| `neg_impl_wf_checks` | Rejects item-bearing negative impls (`E0749`) and specialized negative auto-trait impls (`E0366`). | `[]` (0 axioms!) |
| `marker_item_free_coherent` & `ce_marker_with_assoc_item_incoherent` | **`#[marker]` Item-Free Soundness:** `E0714`/`E0715` (`assocItems = []`) guarantees `CoherentItemResolution` vacuously across overlapping impls; omitting `E0714` yields a concrete `u32` constant-value ambiguity. | `[]` / `[propext]` |
| `inherent_disjoint_names_sound`, `inherent_disjoint_self_types_sound`, `inherent_u32_vs_i32_disjoint` | Inherent overlap safety (`E0592`) via disjoint item names or non-unifying `Self` types. | `[]` / `[propext]` |
| `zc_reason_marker_disjointness` & `ce_zc_without_reason_marker_overlaps` | **`zerocopy` Reason-Marker Disjointness:** Proves `Read`, `MutationCompatible`, and `TryTransmuteFromPtr` markers never overlap, and proves collision if `R` is dropped. | `[]` (0 axioms!) |
| `zc_shared_compatible_occurs_check_disjoint` & `zc_unalign_wrapping_shared_compatible_disjoint` | **`zerocopy` Occurs-Check Non-Overlap:** Proves `SharedCompatible` for `T` vs. `ManuallyDrop<T>` vs. `Unalign<T>` vs. `Wrapping<T>` are pairwise disjoint via constructive `groundZcTySize` (`n + 1 ≠ n`). | `[]` (0 axioms!) |
| `master_coherence_safety` | End-to-end multi-crate coherence composition combining cross-crate orphan separation, intra-crate non-marker uniqueness, and `#[marker]` item agreement. | `[propext]` |
| `concrete_rc_disjoint_across_semver` & `builtin_coherence_witnesses` | Concrete `SemVerExtension` witness for `Rc<T>` and witnesses for `E0321`, `Drop`, `Copy` (`E0206`), and `dyn` object overlap (`E0371`). | `[propext]` |

#### 7.2 Architectural Relationship to `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`

In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/rustc-capture/src/driver.rs` (L25, L75-84, L137-150) hooks `rustc_driver::Callbacks::after_analysis` on `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` and only records `analysis_reached` when `tcx.dcx().has_errors().is_none()` and `run_compiler` exits cleanly without errors. Because `coherent_trait`, `orphan_check_impl`, `crate_inherent_impls_overlap_check`, `wfcheck`, and `specialization_graph_of` all execute prior to `after_analysis` during analysis, every program accepted into Anneal's MIR capture boundary already satisfies cross-crate orphan uniqueness, `E0714`/`E0715` marker emptiness, `E0751` positive/negative exclusion, and `E0592` inherent non-collision. Note that `trusted/lean/Trusted/MirAst.lean` (L308-321) currently lowers non-fieldless ADTs (including `Box`, `Pin`, `ManuallyDrop`), `TyKind::Dynamic`, and `TyKind::Alias` to `MirTy.unsupported` (failing closed to `FaultKind.unsupported` in `MirSemantics.lean` L49-52); as Anneal extends MIR capture to generic trait dispatch and `zerocopy` wrappers, monomorphized `DefId` resolution soundness relies directly on these upstream coherence guarantees (and specifically on `0259d5e9a`'s `OwnedBox` narrowing if upgraded past `1.100.0`).

## Boundaries

Negative space is classified strictly under `reference-corpus/1`:

1. **`OrphanCheckMode::Compat` Projection Unsoundness (`not examined` empirically / `known not to apply` to theorem):** Our Lean theorem `orphan_check_cross_crate_disjoint` models `OrphanCheckMode::Proper` without associated-type projection aliases (`ty::Projection`). `rustc`'s legacy `OrphanCheckMode::Compat` (`rustc_next_trait_solver/src/coherence.rs` L24-33, L373-380; `orphan.rs` L31-53) treats type parameters inside projections as covered (emitting the `UNCOVERED_PARAM_IN_PROJECTION` lint rather than an error, linked to upstream `#99554` and `#124559`). That unsound compatibility escape hatch is **known not to apply** to our separation theorem and was **not examined** via live `rustc` probes.
2. **Known Upstream `with_negative_coherence` `FIXME`s and `Strict` Mode (`unknown` / `not examined`):** `compiler/rustc_trait_selection/src/traits/coherence.rs` (`0259d5e9a` L417-423, L574-576; `14210df0e` L519-525, L676-678) flags two open upstream soundness/completeness caveats: `impl_intersection_has_negative_obligation` drops header-unification constraints rather than assuming them, and `try_prove_negated_where_clause` forks with `TypingMode::non_body_analysis()` (which can reveal opaque types during negative coherence, upstream `#132279`). Edge-case interactions between opaque `RPIT` types and `with_negative_coherence`, as well as `#[rustc_strict_coherence]` (`OverlapMode::Strict`) probes, were **not examined**, and completeness of negative coherence under complex header constraints remains **unknown**.
3. **Full `#![feature(specialization)]` vs. `#[marker]` and Coherence (`known not to apply`):** Our Lean `master_coherence_safety` assumes non-marker impls have disjoint ground applicability (`NonMarkerUnique`), intentionally excluding specialization trees (`impl<T> Tr` + `impl Tr for u32`); specialization soundness under lifetime erasure is **known not to apply** to non-specialized coherence and is analyzed separately in `rustc-auto-traits-rpit-leakage-fundamental-orphan-specialization-and-freeze`.
4. **Live Execution at `0259d5e9a` (`not examined` by execution):** Our live 44-case `rustc` probe executed on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), directly confirming `a15` (`Box<u32, LocalAlloc>` admitted on `14210df0e`). Rejection of `Box<u32, LocalAlloc>` on `0259d5e9a` (`OwnedBox => args.type_at(0)`) is established from primary source inspection (`source`) rather than live execution on a post-`1.100.0` binary.
5. **Other Built-In Coherence Checks (`Reborrow`, `CoerceShared`, `CoerceUnsized`, `DispatchFromDyn`) (`not examined` empirically):** While dispatch points in `coherence/builtin.rs` (`L32-54`, `L247-1041`) were audited by source inspection, structural field-matching probes for `CoerceUnsized`, `Reborrow`, `CoerceShared`, and `DispatchFromDyn` were **not examined** via live `rustc` execution.
6. **Lean Formalization Scope (`known not to apply` to unmodeled Rust features):** `support/CoherenceOrphanFundamentalAndNegativeImplsSoundness.lean` is a standalone formalization that does **not** import `joshlf/anneal`'s `Trusted.MirAst` or `Trusted.MirSemantics`, does not model lifetimes/higher-ranked trait bounds (`for<'a>`), associated-type normalization cycles, or `impl_restriction` visibility paths, and assumes crate well-scopedness (`TraitRefScopedInCrate`) externally rather than proving it from a full Rust name-resolver model.
7. **`-Znext-solver=globally` Trait Selection (`not examined`):** Probes ran under `rustc`'s default solver configuration (where `orphan_check` and `coherence::overlap` already pass `.with_next_trait_solver(true)` internally regardless of crate-wide `-Znext-solver`). Downstream call-site selection under `-Znext-solver=globally` was **not examined**.

## Evidence

All primary-source inspections, live `rustc` executions, and Lean `v4.34.1` kernel checks below were freshly acquired and verified on `2026-11-23`.

### 1. Upstream Primary Sources (Pinned 40-Hex Commits)

#### `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` executed nightly; `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` `main`)

| File Path | Key Symbols & Checks | `14210df0e` Lines | `0259d5e9a` Lines |
| :--- | :--- | :--- | :--- |
| `compiler/rustc_hir_analysis/src/coherence/mod.rs` | `check_impl`, `enforce_trait_manually_implementable` (`Freeze`, `E0322`, `E0328`), `enforce_empty_impls_for_marker_traits` (`E0715`), `provide`, `coherent_trait`, `check_object_overlap` (`E0371`) | L27-246 | L27-248 |
| `compiler/rustc_hir_analysis/src/coherence/orphan.rs` | `orphan_check_impl` (`Compat` lint `UNCOVERED_PARAM_IN_PROJECTION`, auto-trait nominal check `E0321`), `orphan_check`, `emit_orphan_check_error` (`E0117`, `E0210`), `UncoveredTyParamCollector` | L22-530 | L22-526 |
| `compiler/rustc_hir_analysis/src/coherence/inherent_impls.rs` | `crate_inherent_impls`, `check_def_id` (`E0116`), `check_primitive_impl` (`E0390`), `check_item` | L22-220 | L21-233 |
| `compiler/rustc_hir_analysis/src/coherence/inherent_impls_overlap.rs` | `crate_inherent_impls_overlap_check`, `check_for_duplicate_items_in_impl`, `check_for_common_items_in_impls` (`E0592`), `ALLOCATING_ALGO_THRESHOLD = 500` | L15-345 | L15-345 |
| `compiler/rustc_hir_analysis/src/coherence/builtin.rs` | `check_trait` (`Drop`, `AsyncDrop`, `Copy`, `Unpin`, `ConstParamTy`, `CoerceUnsized`, `Reborrow`, `CoerceShared`, `DispatchFromDyn`, `CoercePointeeValidated`) | L31-1178 | L32-1041 |
| `compiler/rustc_hir_analysis/src/coherence/unsafety.rs` | `check_item` (`E0199`, `E0200`, `E0569`, `unsafe_fields` `Copy` check) | L13-122 | L14-123 |
| `compiler/rustc_hir_analysis/src/collect.rs` | `trait_def` (`is_marker`, `is_fundamental`, `specialization_kind`, `deny_explicit_impl`) | L894-949 | L1114-1191 |
| `compiler/rustc_hir_analysis/src/check/wfcheck.rs` | `check_trait` (`E0714` zero-item check on `#[marker]` traits) | L1178-1192 | L1111-1139 |
| `compiler/rustc_hir_analysis/src/check/check.rs` | Negative impl zero-item enforcement (`E0749`) | L1263-1275 | L1318-1333 |
| `compiler/rustc_hir_analysis/src/check/always_applicable.rs` | `check_negative_auto_trait_impl` (`E0366`, `E0367`) | L88-435 | L84-435 |
| `compiler/rustc_next_trait_solver/src/coherence.rs` | `InCrate`, `OrphanCheckMode`, `Conflict`, `trait_ref_is_knowable`, `trait_ref_is_local_or_fundamental`, `orphan_check_trait_ref`, `OrphanChecker::visit_ty` (`OwnedBox` in `0259d5e9a`), `visit_const` | L13-469 | L13-478 |
| `compiler/rustc_trait_selection/src/traits/coherence.rs` | `overlapping_inherent_impls`, `overlapping_trait_impls`, `overlap`, `equate_impl_headers`, `impl_intersection_has_impossible_obligation`, `impl_intersection_has_negative_obligation`, `plug_infer_with_placeholders`, `try_prove_negated_where_clause`, `compute_intercrate_ambiguity_causes` | L105-868 | L85-744 |
| `compiler/rustc_trait_selection/src/traits/specialize/specialization_graph.rs` | `Children::insert` (`impls_are_allowed_to_overlap` bypass, `if le == ge`) | L76-193 | L76-193 |
| `compiler/rustc_trait_selection/src/traits/specialize/mod.rs` | `specialization_graph_provider`, `report_overlap_conflict`, `report_negative_positive_conflict` (`E0751`) | L420-520 | L423-515 |
| `compiler/rustc_middle/src/traits/specialization_graph.rs` | `OverlapMode::{Stable, WithNegative, Strict}` and `OverlapMode::get` | L52-86 | L52-86 |
| `compiler/rustc_middle/src/ty/mod.rs` | `TyCtxt::impls_are_allowed_to_overlap` (`Permitted { marker: true }`) | L1689-1724 | L1935-1970 |
| `library/alloc/src/boxed.rs` | `#[lang = "owned_box"] #[fundamental] pub struct Box<T, A>` (`allocator_api` stabilized `since = "1.100.0"` on `0259d5e9a`) | L228-237 | L301-311 |
| `library/core/src/pin.rs` | `#[lang = "pin"] #[fundamental] pub struct Pin<Ptr>`, `helper::PinHelper` (`#85099`) | L1088-1094, L1697-1720 | L1087-1093, L1694-1741 |
| `library/core/src/ops/function.rs` | `#[fundamental]` on `Fn`, `FnMut`, `FnOnce` (and `FnPtr` on `0259d5e9a`), `"so that regex can rely that &str: !FnMut"` | L73, L160, L239 | L73, L160, L239, L350 |

#### `google/zerocopy` (`e5a9824d87f7daa5282969a25a8bbca9af985400`)

- `zerocopy/src/pointer/transmute.rs`: `TryTransmuteFromPtr` (L114-123), `BecauseMutationCompatible` (L126), blanket impl `(BecauseMutationCompatible, R)` (L153-163), blanket impl `BecauseImmutable` (L172-181), `MutationCompatible` (L194), `BecauseRead` (L197), blanket `(BecauseRead, R)` (L200-206), `SharedCompatible` (L216), reflexive `SharedCompatible<T> for T` (L219), blanket `BecauseSharedCompatible` (L223-229), `ManuallyDrop<T>` symmetric `SharedCompatible` impls (L258-260), `unsafe_impl_shared_compatible!` for `Unalign<T>` (L411) and `Wrapping<T>` (L444).
- `zerocopy/src/pointer/invariant.rs`: `Read<A: Aliasing, R>` (L273), `Read<A, BecauseImmutable>` (L275), `Read<Exclusive, BecauseExclusive>` (L276), `BecauseExclusive` (L281), `BecauseImmutable` (L286).
- `zerocopy/src/impls.rs`: `Immutable for Box<T>` (L306), `TryFromBytes` / `FromZeros` for `Option<Box<T>>` (L336-342), `Option<&'_ T>` / `Option<&'_ mut T>` (L344-350), `Immutable` / `TryFromBytes` / `FromZeros` / `FromBytes` / `IntoBytes` / `Unaligned` / `HasTag` for `ManuallyDrop<T>` (L735-781), `Immutable for &'_ T` / `&'_ mut T` (L981-982).

#### `joshlf/anneal`, `rust-lang/reference`, and `rust-lang/rfcs`

- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/rustc-capture/src/driver.rs` (L25 `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"`, L75-84 `after_analysis`, L137-150), `trusted/lean/Trusted/MirAst.lean` (L75-92 `noncomputable` convention, L308-321 `MirTy.unsupported`), `trusted/lean/Trusted/MirSemantics.lean` (L49-52 `FaultKind.unsupported`).
- `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/items/implementations.md` (L53-88, L142-174), `src/glossary.md` (L32-35, L76-85, L102-109, L251-254).
- `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/1023-rebalancing-coherence.md`, `text/2451-re-rebalancing-coherence.md` (L181-258).

### 2. Preserved Package Support Artifacts

1. **`support/probe_coherence_orphan_fundamental_neg.py`:** Standalone Python 3.10+ stdlib probe building independent upstream rlibs (`up`, `up_neg`) and compiling/executing all 44 multi-crate coherence, orphan-rule, `#[fundamental]`, `#[marker]`, negative-impl, and `zerocopy`-pattern test cases inside `tempfile.TemporaryDirectory()`, scrubbing temporary paths and sysroots before emitting JSON.
2. **`support/probe_results.json`:** Recorded live execution results captured on `2026-11-23` under `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (LLVM `22.1.6`, `x86_64-unknown-linux-gnu`), `total_cases = 44`, zero path leaks.
3. **`support/CoherenceOrphanFundamentalAndNegativeImplsSoundness.lean`:** 1,727-line (78,273-byte) standalone Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) kernel-checked formalization covering multi-crate DAG orphan separation, `#[fundamental]` unwrapping & `E0117`/`E0210` counterexamples, `OwnedBox` revision delta (`allArgs` vs. `elemOnly`), negative-impl SemVer monotonicity & `OverlapMode` discrimination, `#[marker]` item-free soundness (`E0714`/`E0715`), inherent overlap (`E0592`), built-in coherence checks (`E0321`/`E0371`/`Drop`/`Copy`), and `zerocopy` reason-marker + occurs-check coherence. Verified with exit code `0`, `0` warnings, `0` `sorry`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `Lean.ofReduceBool`, and `0` `._unsafe_rec` across all 874 local environment constants.

## Revalidation

To verify whether these findings hold on a newer `rustc` nightly (especially post-`1.100.0` `Box<T, A>` `OwnedBox` behavior), another host target, or a newer Lean 4 toolchain:

### 1. Re-run the Live Multi-Crate `rustc` Probe (~5 seconds)

From the package directory:

```bash
python3 support/probe_coherence_orphan_fundamental_neg.py --out /tmp/coherence_reval.json
```

Check these key discriminators against `support/probe_results.json`:
- `a01`–`a05`, `a08`–`a09`, `a12`, `a17`, `a20`: all exit `0` (`compile_rc == 0`, `run_rc == 0`); `a06`, `a07`, `a14`, `a19` fail `E0117`; `a10`, `a11`, `a13` fail `E0210`; `a16` fails `E0321`; `a18` fails `E0119`.
- **Revision-delta discriminator `a15` (`Box<u32, LocalAlloc>`):** On `14210df0e` (`1.98.0-nightly`), `a15` passes (`compile_rc == 0`, `A15=box_u32_local_alloc`). On `rustc` builds incorporating `0259d5e9a`'s `SolverAdtLangItem::OwnedBox => args.type_at(0)` check, `a15` is expected to flip to `compile_rc == 1` (`E0117`).
- `b02` (`compile_rc == 0`), `b03` (`E0592`), `b04` (`E0116`), `b05` (`E0371`), `b06` (`compile_rc == 0`), `b07`–`b08` (`E0714` + `E0715`).
- `c02` (`compile_rc == 0` under `OverlapMode::Stable`), `c06a` & `c07` (`E0119` under `Stable`), `c06b` & `c08` (`compile_rc == 0` under `WithNegative`), `c09` (`E0749`), `c10` (`E0751`), `c11` (`E0366`).
- `d01` (`compile_rc == 0`, `D01=ok,ok,ok`), `d02` (`E0119`), `d03a` (`compile_rc == 0`), `d03b` (`E0117`).

### 2. Re-check the Standalone Lean `v4.34.1` Formalization (~3 seconds)

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/CoherenceOrphanFundamentalAndNegativeImplsSoundness.lean
```

Exit code `0` with zero output confirms all 36 named theorems and supporting lemmas remain kernel-checked without warnings, `sorry`, or forbidden tactics.

### 3. Diff Upstream Compiler Source Seams

When bumping `rust-lang/rust` or `google/zerocopy`, diff `compiler/rustc_next_trait_solver/src/coherence.rs` (`orphan_check_trait_ref`, `trait_ref_is_knowable`), `compiler/rustc_trait_selection/src/traits/coherence.rs` (`overlap`, `impl_intersection_has_negative_obligation`), `compiler/rustc_hir_analysis/src/coherence/{mod,orphan,inherent_impls_overlap,builtin}.rs`, and `zerocopy/src/pointer/transmute.rs` against the pinned commits recorded in `REPORT.json`.
