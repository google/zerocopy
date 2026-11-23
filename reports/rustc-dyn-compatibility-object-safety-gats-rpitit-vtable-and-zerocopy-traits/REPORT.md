# Rustc Dyn-Compatibility, Object-Safety Rules, GATs/RPITIT, Vtable Slot Construction, and Zerocopy Trait Classification

## Summary

Rust's dyn-compatibility check (formerly object safety) determines whether a trait `Trait` admits trait objects `dyn Trait` by enforcing that every non-`final`, non-`Self: Sized` item can either be erased into a trait object's fixed vtable or bound concretely at the `dyn Trait` type site (`Basis: source + execution`). In `rust-lang/rust` (`277240238554297f93fa9ee3c7643dfa03ccbbb4` HEAD and executed `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly`), the canonical checker lives in `compiler/rustc_trait_selection/src/traits/dyn_compatibility.rs` (invoked during HIR lowering at `compiler/rustc_hir_analysis/src/hir_ty_lowering/dyn_trait.rs`), while compiled vtable slot layouts are constructed in `compiler/rustc_trait_selection/src/traits/vtable.rs` and `compiler/rustc_middle/src/ty/vtable.rs` (`Basis: source`).

Six load-bearing architectural mechanisms and empirically observed discrepancies govern real Rust code, `google/zerocopy` trait hierarchies, and verified-`rustc` mechanization:

1. **`where Self: Sized` Omission vs. `VtblEntry::Vacant` Slot Retention:** Every associated item (`fn`, `const`, `type`) whose elaborated predicates contain `Self: Sized` (including indirect supertrait bounds such as `where Self: Clone`, because `Clone: Sized`) is exempted from dyn-compatibility violations via `generics_require_sized_self` and completely omitted from `own_existential_vtable_entries` (`0` vtable slots). Conversely, methods that pass `is_vtable_safe_method` (such as `fn m(&self) where Self: Send`) *retain* a deterministic vtable slot across all implementations and receive `VtblEntry::Vacant` (`AllocInit::Uninit`, emitted as `[8 x i8] undef` in LLVM IR) on concrete types like `Rc<u32>` where the bound does not hold (`Basis: source + execution + derived`).
2. **Associated Constants, GATs, RPITIT, and `async fn` (`E0038`):** Unbounded generic methods (`MethodViolation::Generic`), non-`Self: Sized` associated constants (failing with `AssocConstViolation::FeatureNotEnabled` unless gated with `#![feature(generic_const_items)]` / `gca_min_const_items`, where `where Self: Sized` permits dyn-compatibility), generic associated types (`DynCompatibilityViolation::GenericAssocTy`), return-position `impl Trait` in traits (`MethodViolation::ReferencesImplTraitInTrait`), and `async fn` (`MethodViolation::AsyncFn`) all emit hard `E0038` diagnostics whenever reachable on `dyn Trait` (`Basis: source + execution`).
3. **`WhereClauseReferencesSelf` Doc-Comment Drift and `Clone: Sized` Elaboration:** Compiler comments at `compiler/rustc_middle/src/traits/mod.rs:985` (`/// e.g., fn foo(&self) where Self: Clone`) and `dyn_compatibility.rs:568` (`// results in a lint, and not a hard error`) are stale with respect to live compiler behavior. On `rustc 1.98.0-nightly`, `where Self: Clone` elaborates to `Self: Sized` so `&dyn Trait` compiles cleanly and `d.f()` is rejected for lacking `Sized`, whereas non-`Sized` non-auto traits (`where Self: NonAuto` or `where Self: Immutable` in `zerocopy::IntoBytes`) hit `MethodViolation::WhereClauseReferencesSelf` and emit a hard **`E0038`** error via `report_dyn_incompatibility` rather than a lint (`Basis: source + execution`).
4. **The `fn by_val(self)` `E0161` vs. `E0038` Special Case and `Box<dyn FnOnce()>`:** Contrary to prose in `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`src/items/traits.md:102,105`), `dyn_compatibility.rs:526` (`520` in `1.98.0-nightly`) explicitly skips `receiver_is_dispatchable` when `receiver_ty == tcx.types.self_param`. A `fn by_val(self)` method without `where Self: Sized` leaves the trait dyn-compatible, receives a vtable slot populated with a `ShimKind::VTable` wrapper (`fn(*mut Self, ...) -> ...`), rejects safe calls at borrow-check with **`E0161`** (`cannot move a value of type dyn Trait`), and succeeds under `#![feature(unsized_fn_params)]` (the internal feature enabled by `alloc/src/lib.rs:199` that makes `Box<dyn FnOnce()>` work on stable Rust) (`Basis: source + execution`, diverging from Reference prose).
5. **`AsyncFn`, `AsyncFnMut`, and `AsyncFnOnce`:** In contrast to `rust-lang/reference@c9cc3282` (`src/items/traits.md:108`), which states that all three `AsyncFn*` traits are not dyn-compatible, `AsyncFn` and `AsyncFnMut` fail `E0038` due to the GAT `type CallRefFuture<'a>`, whereas `AsyncFnOnce` has an unparameterized associated type `CallOnceFuture` (and no `#[rustc_dyn_incompatible_trait]` attribute). On stable Rust, `dyn AsyncFnOnce() -> u32` fails `E0191` (`CallOnceFuture` must be specified, gated by `#[unstable(feature = "async_fn_traits")]`), and under `#![feature(async_fn_traits, unboxed_closures)]`, `Box<dyn AsyncFnOnce<(), Output = u32, CallOnceFuture = Ready<u32>>>` compiles and runs (`Basis: source + execution`, diverging from Reference prose).
6. **Smart-Pointer Receivers & `google/zerocopy` Traits:** All built-in `DispatchFromDyn` receivers (`&Self`, `&mut Self`, `Box<Self>`, `Rc<Self>`, `Arc<Self>`, `Pin<Ptr>`, and feature-gated `*const Self` / `#[repr(transparent)]` wrappers with at most one non-parameterized 1-ZST field) erase `Self` uniformly via a thin data pointer + vtable pair, while double indirection (`&&Self`, `Rc<Box<Self>>`) fails `E0038` (`UndispatchableReceiver`) (`Basis: source + execution`). In `google/zerocopy` (`0.8.64`), **`Immutable` and `Unaligned` are dyn-compatible** (`where Self: Sized` on `only_derive_is_allowed_to_implement_this_trait`), whereas **`KnownLayout`, `TryFromBytes`, `FromZeros`, `FromBytes`, and `IntoBytes` all fail `E0038`** (`KnownLayout` via `const LAYOUT` + 7 static functions, `TryFromBytes`/`FromZeros`/`FromBytes` via static associated functions such as `is_safe<A>` which short-circuits at `StaticMethod` before `Generic`, and `IntoBytes` via `WhereClauseReferencesSelf` and `ReferencesSelfOutput`). All invariants, counterexamples, and `zerocopy` classifications are mechanized in kernel-checked Lean `v4.34.1` (`2,483` LOC, `266` theorems, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `native_decide`, `0` `._unsafe_rec`, strict `[propext]`-only kernel axioms) (`Basis: source + execution + derived`).

## Applicability

This report establishes primary-source, empirical, and mechanized findings across the following subjects recorded in `REPORT.json`, all observed on `2026-11-23`:

- **Rust compiler & standard libraries (`rust-lang/rust`):**
  - Executed compiler empirical baseline: `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, host `x86_64-unknown-linux-gnu`, `LLVM 22.1.6`), compiled with Edition `2024` (probes) and Edition `2021` (`zerocopy`).
  - Audited upstream HEAD baseline: `277240238554297f93fa9ee3c7643dfa03ccbbb4`. Where line numbers or internal names differ between `14210df0e27c` (`rustc 1.98.0-nightly`, 989 lines in `dyn_compatibility.rs`) and `277240238554` (1,078 lines), both revisions are stated explicitly:
    - `dyn_compatibility.rs`: `receiver_ty != tcx.types.self_param` is line `520` in `14210df0e27c` and line `526` in `277240238554`; `predicates_of` was renamed to `clauses_of` and `Trait` super-clauses gained `SupertraitNonLifetimeBinder` and `SupertraitConst` (`HostEffect`) checks; `min_generic_const_args` + `is_type_const` evolved into `gca_min_const_items` + `is_always_gca` / `gca_const_items`, and `ty::AssocKind::Const` gained `AssocConstData::{Anonymous, Named}` in `277240238554`. Core `E0038` violation categories, `where Self: Sized` elaboration, `by_val(self)` `ShimKind::VTable` / `E0161` handling, `vtable.rs` slot generation, and `DispatchFromDyn` coherence checks are shared across both revisions.
- **The Rust Reference (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** Interpreted as the descriptive/normative language specification target (`src/items/traits.md`, lines `70-160`), explicitly contrasted against live `rustc` source and execution on `fn(self)` and `AsyncFnOnce`.
- **`google/zerocopy` (`0.8.64`):** Audited against upstream `main` HEAD `e86eb0281380bdc278f4b4b3788dc9525ef59035` and compiled cleanly via `rustc` (`CARGO_PKG_VERSION=0.8.64`, `--edition=2021`, zero default Cargo features) against `907b9175fee081872ec883ca4709e6ad922f8ed0`. Direct `diff -u` of `zerocopy/src/lib.rs` between `907b9175` and `e86eb028` confirms only a line-12 doc comment changed; all `zerocopy` trait definitions (`KnownLayout`, `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`, `Unaligned`) are byte-for-byte identical at identical line numbers (`748-6676`) across both commits.
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Examined for its `TrustedBoundary` kernel-purity rules (`trusted/lean/Trusted/MirAst.lean:77-91`) and current MIR type coverage (`trusted/lean/Trusted/MirAst.lean:308-322`), establishing how standalone pure-`prelude` `noncomputable def` proofs integrate cleanly with Anneal's verification trust model and where MIR support for `TyKind::Dynamic` currently stops (`MirTy.unsupported`).
- **Lean 4 prover (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`):** Used to verify the formal model and all 266 kernel-checked theorems in `support/DynCompatibilityVtableSlotSoundness.lean`.

Relation to companion corpus packages: `custom-unsized-types-coerce-unsized-vtable-metadata-and-gat-lifetime-variance` covers `Pointee::Metadata`, `CoerceUnsized`/`DispatchFromDyn` symmetric coercion laws, RFC 3324 trait upcasting, `DstLayout`, and GAT variance; `closure-upvar-defunctionalization-symbolic-vtables-and-trait-coherence-laws` covers closure defunctionalization and coherence; and `rust-unsafe-traits-coinduction-gats-and-safety-invariants` covers `unsafe trait` coherence and auto-trait coinduction. The present package focuses specifically on `rustc` dyn-compatibility checking (`E0038`), `where Self: Sized` vtable-slot omission vs. `VtblEntry::Vacant`, `fn by_val(self)` `E0161` vs. `E0038`, `AsyncFn*` and smart-pointer receiver dispatchability, real `google/zerocopy` trait `dyn`-compatibility, and an independent pure Lean `v4.34.1` mechanization.

## Findings

### 3.1 Architecture of the `rustc` Dyn-Compatibility Pipeline

`Basis: source`

Contrary to historical terminology ("object safety") and occasional attribution to `rustc_hir_analysis`, the canonical dyn-compatibility implementation resides in `compiler/rustc_trait_selection/src/traits/dyn_compatibility.rs` and exposes three query providers registered at lines `1071-1078` (`14210df0e27c:983-989`):

```rust
pub(crate) fn provide(providers: &mut Providers) {
    *providers = Providers {
        dyn_compatibility_violations,
        is_dyn_compatible,
        generics_require_sized_self,
        ..*providers
    };
}
```

At HIR type lowering time, `compiler/rustc_hir_analysis/src/hir_ty_lowering/dyn_trait.rs` computes trait-object bounds for `dyn Trait<...>`:
1. Before full `dyn_compatibility_violations` can run safely without query cycles during item signature collection, `hir_ty_lowering_dyn_compatibility_violations` (`dyn_compatibility.rs:38-48`) checks elaborated supertrait clauses for non-projected `Self` (`AllowSelfProjections::No`).
2. Full trait-object construction evaluates `tcx.dyn_compatibility_violations(trait_def_id)` (`dyn_compatibility.rs:50-60`), which iterates `elaborate::supertrait_def_ids(tcx, trait_def_id)` (including the principal trait itself and all transitive supertraits) and collects every `DynCompatibilityViolation`.
3. `is_dyn_compatible` (`dyn_compatibility.rs:62-64`) holds if and only if `tcx.dyn_compatibility_violations(trait_def_id).is_empty()`.
4. Whenever `dyn_compatibility_violations` is non-empty, `report_dyn_incompatibility` (`compiler/rustc_trait_selection/src/error_reporting/traits/mod.rs:680-860`) renders diagnostic code **`E0038`** (`the trait X is not dyn compatible`) with per-violation notes derived from `DynCompatibilityViolation` (`compiler/rustc_middle/src/traits/mod.rs:700-1033`).

#### Complete Taxonomy of `DynCompatibilityViolation` Variants

`Basis: source + execution`

At `dyn_compatibility.rs:82-120` and `dyn_compatibility.rs:349-437`, per-trait and per-associated-item checks produce the following variants (with executable confirmation on `rustc 1.98.0-nightly` recorded in `support/probe_results.json`):

| Violation Variant (`rustc_middle::traits`) | Trigger Condition (`dyn_compatibility.rs`) | `E0038` Note Text (`rustc_middle` / `1.98.0-nightly`) | Executable Probe Confirmation (`support/probe_results.json`) |
| :--- | :--- | :--- | :--- |
| `SizedSelf` | `trait_has_sized_self(tcx, trait_def_id)` via supertrait `: Sized` or `where Self: Sized` | `...because it requires Self: Sized` | `i_sized_self_supertrait_e0038`, `i_sized_self_where_e0038` (`E0038`) |
| `ExplicitlyDynIncompatible` | `tcx.trait_def(did).force_dyn_incompatible.is_some()` (`#[rustc_dyn_incompatible_trait]`) | `...because it was explicitly marked dyn-incompatible` | Checked by source (`middle/traits/mod.rs`); see `Boundaries` |
| `SupertraitSelf` | Supertrait / trait clause or non-`Self: Sized` assoc-type item bound illegally references `Self` | `...because it uses Self as a type parameter` | `i_supertrait_self_type_arg_e0038` (`E0038` + `E0277`), `i_supertrait_self_proj_input_e0038` (`E0038`); output projection `Sub: Sup<Item = Self::Out>` succeeds (`SUPERTRAIT_PROJ_OUT=17`) |
| `SupertraitNonLifetimeBinder` | Super-clause has non-region bound vars (`for<T>`) (`277240238554:284-293`) | Supertrait binder references non-lifetime parameter | Checked by source (`dyn_compatibility.rs:284-293`); see `Boundaries` |
| `SupertraitConst` | Unconditionally `const` supertrait clause (`HostEffect`) (`277240238554:298-313`) | `const` supertrait requirement | Checked by source (`dyn_compatibility.rs:298-313`); see `Boundaries` |
| `Method(_, StaticMethod(_))` | `!method.is_method()` (first arg not `self`) — **returns early** before other method checks! | `...because associated function X has no self parameter` | `iii_static_method_e0038` (`E0038`), also `zerocopy::TryFromBytes::is_safe<A>` |
| `Method(_, ReferencesSelfInput(_))` | Extra parameter (`inputs.skip(1)`) has bare `Self` or `<Self as NonSuper>::Assoc` (`AllowSelfProjections::Yes`) | `...because method X references the Self type in this parameter` | `iv_self_input_output_e0038` (`E0038`) |
| `Method(_, ReferencesSelfOutput)` | Return type has bare `Self` or non-supertrait `Self::Assoc` (`AllowSelfProjections::Yes`) | `...because method X references the Self type in its return type` | `iv_self_input_output_e0038`, `zerocopy::IntoBytes::write_to` (`E0038`) |
| `Method(_, ReferencesImplTraitInTrait(_))` | `!is_async` and `IllegalRpititVisitor` finds RPITIT projection in `sig.output()` | `...because method X references an impl Trait type in its return type` | `viii_rpitit_and_async_fn_e0038` (`E0038`) |
| `Method(_, AsyncFn)` | `tcx.asyncness(fn_def_id).is_async()` | `...because method X is async` | `viii_rpitit_and_async_fn_e0038` (`E0038`) |
| `Method(_, CVariadic)` | `sig.skip_binder().c_variadic()` (`...`) | `...because method X is C-variadic` | Checked by source (`dyn_compatibility.rs:510-512`) |
| `Method(_, Generic)` | `own_counts.types > 0 \|\| own_counts.consts > 0` (lifetime params allowed!) | `...because method X has generic type/const parameters` | `ii_generic_method_e0038` (`E0038`) |
| `Method(_, UndispatchableReceiver(_))` | `receiver_ty != tcx.types.self_param && !receiver_is_dispatchable(...)` | `...because method X's self parameter cannot be dispatched on` | `undispatchable_double_indirection_e0038` (`E0038`) |
| `Method(_, WhereClauseReferencesSelf)` | Any non-outlives, non-positive-auto-trait method `where` clause illegally references `Self` | `...because method X references the Self type in its where clause` | `ix_where_self_non_auto_unsized_e0038`, `zerocopy::IntoBytes::as_bytes` (`E0038`) |
| `AssocConst(_, FeatureNotEnabled)` | Non-`Self: Sized` associated const without `gca_min_const_items` (`min_generic_const_args` in `1.98`) | `...because it contains associated const C` | `vi_assoc_const_e0038` (`E0038`), `zerocopy::KnownLayout::LAYOUT` (`E0038`) |
| `AssocConst(_, Generic / NonType / TypeReferencesSelf)` | Non-`Self: Sized` assoc const under `gca_min_const_items` that is generic, non-`type const`, or mentions `Self` | Dedicated assoc-const `E0038` notes | `vi_assoc_const_where_self_sized_e0658` vs. `vi_assoc_const_nightly_generic_const_items_self_sized_ok` (`OK=99`) |
| `GenericAssocTy(_, _)` | `!tcx.generics_of(item.def_id).is_own_empty()` on assoc type without `Self: Sized` | `...because it contains generic associated type Item` | `vii_gat_e0038` (`E0038`), `AsyncFn` / `AsyncFnMut` (`E0038` via `CallRefFuture<'a>`) |

Two control-flow subtleties in `dyn_compatibility.rs` matter when diagnosing real errors:
- **Early Return on `StaticMethod` (`dyn_compatibility.rs:451-476`):** If `!method.is_method()`, `virtual_call_violations_for_method` immediately returns `vec![MethodViolation::StaticMethod(sugg)]` and *never* checks generics, `Self` inputs/outputs, or RPITIT on that associated function. That explains why `zerocopy::TryFromBytes::is_safe<A>(candidate: Maybe<'_, Self, A>) -> bool` emits *only* `"associated function is_safe has no self parameter"` in `rustc` even though it has both a type parameter `<A>` and `Self` in its parameter (`Basis: source + execution`).
- **Supertrait Projection Allowance (`AllowSelfProjections::Yes` vs. `No`, `dyn_compatibility.rs:841-998`):** In method inputs/outputs (`sig`), method `where` clauses, assoc const types, and assoc-type item bounds (`AllowSelfProjections::Yes`), `IllegalSelfTypeVisitor` allows `<Self as Super>::Assoc` (or `Self::Assoc`) without walking into `Self` when `Super` is the principal trait or any supertrait, because every non-generic associated type binding must be fixed on the trait object type itself (`dyn Trait<Assoc = T>`, else `E0191` — `vii_assoc_ty_non_gat_missing_e0191` vs. `vii_assoc_ty_non_gat_specified_ok`). Conversely, in supertrait predicates (`trait A: Sup<Self::Out> { type Out; }`, checked with `AllowSelfProjections::No`), `Self::Out` in an **input type argument** to a supertrait is rejected (`i_supertrait_self_proj_input_e0038`), whereas `Self::Out` in an **associated-type projection output** (`trait Sub: Sup<Item = Self::Out> { type Out; }`) is skipped by `&data.projection_term.args.as_slice()[1..]` (`dyn_compatibility.rs:247-265`) and succeeds once both `Item = u32, Out = u32` are specified (`i_supertrait_self_proj_output_ok`: `SUPERTRAIT_PROJ_OUT=17`) (`Basis: source + execution`).

---

### 3.2 `where Self: Sized` Omission vs. `VtblEntry::Vacant` in Vtable Construction

`Basis: source + execution + derived`

Every vtable generated by `compiler/rustc_trait_selection/src/traits/vtable.rs` and materialized by `compiler/rustc_middle/src/ty/vtable.rs` obeys a two-stage invariant: first, trait-level schema selection decides which methods occupy physical pointer slots; second, concrete per-type monomorphization fills or leaves vacant those already-indexed slots.

#### Stage 1: Trait-Wide Slot Allocation (`own_existential_vtable_entries_iter`)

At `vtable.rs:204-231` and `235-310`:
1. `VtblSegment::MetadataDSA` emits `TyCtxt::COMMON_VTABLE_ENTRIES` (`middle/ty/vtable.rs:45-51`):
   - Slot `0` (`COMMON_VTABLE_ENTRIES_DROPINPLACE`): `*mut fn(*mut ())` drop glue (`Pointer::null()` if `!ty.needs_drop(...)`)
   - Slot `1` (`COMMON_VTABLE_ENTRIES_SIZE`): `usize` size in bytes
   - Slot `2` (`COMMON_VTABLE_ENTRIES_ALIGN`): `usize` align in bytes
2. `VtblSegment::TraitOwnEntries` looks up `tcx.own_existential_vtable_entries(def_id)`. This filter iterates `associated_items.in_definition_order().filter(|item| item.is_fn())`, dropping:
   - `final` functions (`defaultness(tcx).is_final()`)
   - Any function where `!is_vtable_safe_method(tcx, trait_def_id, trait_method)` (`dyn_compatibility.rs:70-79`): i.e., **every method with `generics_require_sized_self(method.def_id) == true` receives zero vtable slots**, regardless of concrete `Self` type!
3. For associated types (including GATs) with `where Self: Sized` (`trait HasGatSized { type Item<'a> where Self: Sized; fn tag(&self) -> u32; }`), `dyn_compatibility.rs:202` and `360` exempt both the GAT and its bounds. Attempting to specify `&dyn HasGatSized<Item<'static> = u32>` compiles cleanly while firing the `#[warn(unused_associated_type_bounds)]` lint (`hir_dyn_trait.rs:288-301`, observed in `vii_gat_where_self_sized_unused_bound_lint`: `"this associated type has a where Self: Sized bound, and while the associated type can be specified, it cannot be used because trait objects are never Sized"`). Similarly, `const C: usize where Self: Sized` is rejected on stable/default syntax with **`E0658`** (`generic const items are experimental`, issue `#113521`), and compiles + runs cleanly once `#![feature(generic_const_items)]` is enabled (`GENERIC_CONST_ITEMS_SELF_SIZED_OK=99`) (`Basis: source + execution`).

#### Stage 2: Per-Impl Slot Materialization (`vtable_entries` + `vtable_allocation_provider`)

For each remaining method `def_id` in `own_existential_vtable_entries`, `vtable.rs:280-294` checks:

```rust
if tcx.instantiate_and_check_impossible_clauses((def_id, args)) {
    return VtblEntry::Vacant;
}
```

When clauses fail on a concrete `Self` (such as `fn m_send(&self) -> u32 where Self: Send` evaluated for `Self = Rc<u32>`), `middle/ty/vtable.rs:114-152` initializes the `Allocation` with `AllocInit::Uninit`, **retaining the slot index** and executing `VtblEntry::Vacant => continue` so the slot remains uninitialized bytes (`undef` in LLVM IR), preserving uniform slot offsets across all concrete implementations (`Basis: source`).

#### Empirical LLVM IR Proof (`c_vtable_ir`: `SlotProbe`)

Compiling a single trait `SlotProbe` with five methods and two implementations (`u32: Send` and `Rc<u32>: !Send`) via `rustc -C opt-level=0 --emit=llvm-ir` (`support/probe_dyn_compatibility_and_zerocopy.py`, `c_vtable_ir`) directly confirms both `Self: Sized` omission and `VtblEntry::Vacant`:

```rust
pub trait SlotProbe {
    fn m1(&self) -> u32;
    fn m_sized(&self) -> u32 where Self: Sized; // omitted from vtable (0 slots)
    fn m_send(&self) -> u32 where Self: Send;   // retained at slot 4; Vacant for Rc<u32>
    fn m_by_val(self) -> u32;                   // retained at slot 5; ShimKind::VTable
    fn m2(&self) -> u32;                        // retained at slot 6
}
```

Observed LLVM IR globals emitted verbatim by `rustc 1.98.0-nightly`:

- **`@vtable.0` (`Rc<u32>` impl, `!Send`, `needs_drop = true`, size 8, align 8):**
  ```llvm
  @vtable.0 = private unnamed_addr constant <{ ptr, [16 x i8], ptr, [8 x i8], ptr, ptr }> <{
    ptr @_RINvNtCs8b4M6GsfcPr_4core3ptr9drop_glueINtNtCs8jjFDZd5IFg_5alloc2rc2RcmEECsXdCfStjyhV_9vtable_ir,
    [16 x i8] c"\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00",
    ptr @_RNvXs_CsXdCfStjyhV_9vtable_irINtNtCs8jjFDZd5IFg_5alloc2rc2RcmENtB4_9SlotProbe2m1,
    [8 x i8] undef,
    ptr @_RNSNvYINtNtCs8jjFDZd5IFg_5alloc2rc2RcmENtCsXdCfStjyhV_9vtable_ir9SlotProbe8m_by_val6vtableBD_,
    ptr @_RNvXs_CsXdCfStjyhV_9vtable_irINtNtCs8jjFDZd5IFg_5alloc2rc2RcmENtB4_9SlotProbe2m2
  }>, align 8
  ```
- **`@vtable.1` (`u32` impl, `Send`, `needs_drop = false`, size 4, align 4):**
  ```llvm
  @vtable.1 = private unnamed_addr constant <{ [24 x i8], ptr, ptr, ptr, ptr }> <{
    [24 x i8] c"\00\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00",
    ptr @_RNvXCsXdCfStjyhV_9vtable_irmNtB2_9SlotProbe2m1,
    ptr @_RNvXCsXdCfStjyhV_9vtable_irmNtB2_9SlotProbe6m_send,
    ptr @_RNSNvYmNtCsXdCfStjyhV_9vtable_ir9SlotProbe8m_by_val6vtableB7_,
    ptr @_RNvXCsXdCfStjyhV_9vtable_irmNtB2_9SlotProbe2m2
  }>, align 8
  ```

Each vtable spans exactly `7` pointer-sized words (`56` bytes on `x86_64`): words `0..2` carry the 3 DSA entries (packed by LLVM into `ptr + [16 x i8]` or `[24 x i8]`), word `3` is `m1`, **`m_sized` occupies zero bytes**, word `4` is `[8 x i8] undef` in `@vtable.0` vs. `ptr SlotProbe::m_send` in `@vtable.1`, word `5` is the `...8m_by_val6vtable...` MIR call shim, and word `6` is `m2` (`Basis: execution`). Because `generics_require_sized_self` prevents `d.m_sized()` during method resolution (`error: the m_sized method cannot be invoked on a trait object`), and `d.m_send()` requires `dyn SlotProbe: Send` (`error[E0277]`), neither the omitted method nor the `undef` vacant slot can be invoked safely (`Basis: source + execution + derived`).

---

### 3.3 `WhereClauseReferencesSelf` Comments vs. Actual Elaboration and Hard `E0038`

`Basis: source + execution`

Source inspection and live execution uncovered an important discrepancy in `rustc`'s internal documentation:
- `compiler/rustc_middle/src/traits/mod.rs:985` still annotates `MethodViolation::WhereClauseReferencesSelf` with `/// e.g., fn foo(&self) where Self: Clone`.
- `compiler/rustc_trait_selection/src/traits/dyn_compatibility.rs:568` (`538` in `1.98.0-nightly`) comments:
  ```rust
  // NOTE: This check happens last, because it results in a lint, and not a
  // hard error.
  if tcx.clauses_of(method.def_id).clauses.iter().any(|&(clause, _span)| { ... }) {
      errors.push(MethodViolation::WhereClauseReferencesSelf);
  }
  ```

Empirical tests on `rustc 1.98.0-nightly` and audit of `report_dyn_incompatibility` (`compiler/rustc_trait_selection/src/error_reporting/traits/mod.rs:702`) show **both comments are outdated**:
1. **`where Self: Clone` does NOT trigger `WhereClauseReferencesSelf` (`ix_where_self_clone_elaborates_to_sized_ok`, `ix_where_self_clone_dyn_call_rejected`):** Because `pub trait Clone: Sized`, `elaborate(tcx, clauses)` inside `generics_require_sized_self` (`dyn_compatibility.rs:332`) expands `Self: Clone` into `Self: Sized`. Hence `isVtableSafeMethod` returns `false`, `dyn WhereClone` compiles cleanly (`rc=0`, prints `CLONE_ELAB_SIZED_TAG=30 CONCRETE_F=31`), `f` gets `0` vtable slots, and `d.f()` fails at call site with `error: the f method cannot be invoked on a trait object ... this has a Sized requirement` — never hitting `WhereClauseReferencesSelf`.
2. **Non-`Sized`, non-auto trait bounds trigger a HARD `E0038` error (`ix_where_self_non_auto_unsized_e0038`):** Defining `trait NonAuto {}` (implicitly `?Sized`-unrelated only because `Sized` is not a supertrait — no auto trait, and no `: Sized` supertrait!) and `fn f(&self) -> u32 where Self: NonAuto;` passes `generics_require_sized_self` (`false`), bypasses the positive auto-trait exemption (`dyn_compatibility.rs:597-615`), matches `contains_illegal_self_type_reference` (`dyn_compatibility.rs:617`), pushes `WhereClauseReferencesSelf`, and causes `pub fn use_dyn(_x: &dyn WhereNonAutoUnsized) {}` to abort compilation with **`error[E0038]`** (`...because method f references the Self type in its where clause`), **not a warning/lint**. Meanwhile `where Self: 'static` (`as_type_outlives_clause()`) and `where Self: Send` (`trait_is_auto`) pass cleanly (`ix_where_self_static_and_auto_ok`: `PLAIN=10 SEND=12 STATIC=11 RC_PLAIN=20`), while calling `d.f_send()` on `&dyn WhereOk` without `+ Send` rejects with `E0277` (`ix_where_self_send_called_without_send_e0277`) (`Basis: source + execution`).

---

### 3.4 The `fn by_val(self)` `E0161` vs. `E0038` Special Case and `Box<dyn FnOnce()>`

`Basis: source + execution + derived` (diverging from `documentation` / `normative` Reference prose)

The Rust Reference (`src/items/traits.md:102,105`, `c9cc3282`) states that `fn by_val(self)` implies a `where Self: Sized` bound and counts as explicitly non-dispatchable under dyn-compatibility. Live compiler source and probes establish a materially different pipeline across three subsystems:

1. **Dyn-Compatibility Checker (`dyn_compatibility.rs:520-526`):**
   ```rust
   // `self: Self` can't be dispatched on.
   // However, this is considered dyn compatible. We allow it as a special case here.
   // FIXME(mikeyhew) get rid of this `if` statement once `receiver_is_dispatchable` allows
   // `Receiver: Unsize<Receiver[Self => dyn Trait]>`.
   if receiver_ty != tcx.types.self_param {
       if !receiver_is_dispatchable(tcx, method, receiver_ty) { ... }
   }
   ```
   Because `receiver_ty == tcx.types.self_param` skips `receiver_is_dispatchable`, `virtual_call_violations_for_method` returns `[]` and `is_vtable_safe_method` returns **`true`**. Thus `trait ByVal { fn by_val(self) -> u32; }` **IS dyn-compatible** (`v_by_val_self_allowed_in_dyn_unused_ok` compiles and prints `BY_VAL_TYPE_ALLOWED_PEEK=41`).
2. **Vtable & MIR Shim Codegen (`compiler/rustc_mir_transform/src/shim.rs:36-38, 844-851`):**
   Because `by_val(self)` IS in `own_existential_vtable_entries`, `vtable.rs` inserts a slot pointing to `ShimKind::VTable(def_id)`:
   ```rust
   if let ty::ShimKind::VTable(..) = shim {
       // Modify fn(self, ...) to fn(self: *mut Self, ...)
       ...
       *self_arg = Ty::new_mut_ptr(tcx, *self_arg);
       ...
   }
   ```
   with `Adjustment::Deref { source: DerefSource::MutPtr }` dereferencing `*mut Self` to move out of the caller's stack/box slot (`confirmed verbatim` in `@vtable.0` and `@vtable.1` by symbol `...8m_by_val6vtable...` in `c_vtable_ir`).
3. **Borrow-Check vs. Method-Resolution Call Rejection (`borrowck/src/session_diagnostics.rs:9-16`):**
   - Without `where Self: Sized`: `b.by_val()` on `Box<dyn ByVal>` passes type-checking and fails during borrow-checking in `MoveUnsized` with **`error[E0161]: cannot move a value of type dyn ByVal`** (`v_by_val_self_allowed_in_dyn_box_call_e0161`), and `r.by_val()` on `&dyn ByVal` emits **`E0161` + `E0507`** (`v_by_val_self_allowed_in_dyn_ref_call_e0161_e0507`).
   - With `where Self: Sized`: `fn by_val(self) -> u32 where Self: Sized;` removes the vtable slot and fails *earlier* during method lookup (`v_by_val_where_self_sized_call_rejected`: `error: the by_val method cannot be invoked on a trait object ... this has a Sized requirement`), emitting **no `E0161`**.
   - With `#![feature(unsized_fn_params)]`: `b.by_val()` on `Box<dyn ByVal>` compiles and runs cleanly (`v_by_val_unsized_fn_params_nightly_ok`: `UNSIZED_FN_PARAMS_OK=42`) because `E0161` is lifted for moves into unsized by-value parameters across `ShimKind::VTable`.
   - **Why `Box<dyn FnOnce()>` works on stable Rust (`library/alloc/src/lib.rs:199` + `boxed.rs:2273-2279`):** `FnOnce::call_once(self, args: Args)` takes bare `self: Self` without `where Self: Sized`, so `dyn FnOnce()` is dyn-compatible with a `ShimKind::VTable` slot. Because `library/alloc` internally enables `#![feature(unsized_fn_params)]` (`alloc/src/lib.rs:199`), `impl<Args: Tuple, F: FnOnce<Args> + ?Sized, A: Allocator> FnOnce<Args> for Box<F, A>` (`alloc/src/boxed.rs:2273-2279`) moves the unsized `*self` inside standard-library code so safe user code executes `f()` cleanly on stable (`v_box_dyn_fnonce_stable_ok`: `BOX_DYN_FNONCE_LEN=9`) (`Basis: source + execution + derived`).

---

### 3.5 `AsyncFn`, `AsyncFnMut`, and `AsyncFnOnce` Dyn-Compatibility

`Basis: source + execution` (diverging from `documentation` / `normative` Reference prose)

Auditing `library/core/src/ops/async_function.rs` together with `rustc 1.98.0-nightly` (`x_async_fn_traits_stable_e0038_vs_e0191` and `x_box_dyn_async_fn_once_nightly_ok`) resolves why `AsyncFn` and `AsyncFnMut` differ structurally from `AsyncFnOnce`:
- **`AsyncFnMut` and supertrait-subsumed `AsyncFn`** define `type CallRefFuture<'a>: Future<Output = Self::Output> + Captures<Self> where Self: 'a` (`async_function.rs:28`). Because `CallRefFuture<'a>` is a generic associated type (`own_counts.lifetimes == 1 > 0` without `Self: Sized`), both `&dyn AsyncFn() -> u32` and `&dyn AsyncFnMut() -> u32` fail **`E0038`** (`the trait AsyncFnMut is not dyn compatible ... because it contains generic associated type CallRefFuture`).
- **`AsyncFnOnce`** defines an **unparameterized** associated type `type CallOnceFuture: Future<Output = Self::Output>` (`async_function.rs:48`, gated `#[unstable(feature = "async_fn_traits")]`), an `#[unstable]` output type (`line 53`), and **`async_call_once(self, args: Args)`** (`line 57`, `byValueSelf`), with **zero `#[rustc_dyn_incompatible_trait]` attributes**. Consequently:
  1. On stable Rust (`x_async_fn_traits_stable_e0038_vs_e0191`), `pub fn f3(_x: &dyn AsyncFnOnce() -> u32) {}` emits **`E0191`** (`the value of the associated type CallOnceFuture in AsyncFnOnce() must be specified`) — **NOT `E0038`**!
  2. Under `#![feature(async_fn_traits, unboxed_closures)]` (`x_box_dyn_async_fn_once_nightly_ok`), `let f: Box<dyn AsyncFnOnce<(), Output = u32, CallOnceFuture = Ready<u32>>> = Box::new(|| ready(64u32));` compiles and executes `poll_once(f())` via `Box<F>`'s `AsyncFnOnce` implementation, printing `BOX_DYN_ASYNC_FN_ONCE=64`.
- This directly refines `rust-lang/reference@c9cc3282` (`src/items/traits.md:108`), whose summary line unconditionally groups `AsyncFnOnce` with `AsyncFn` and `AsyncFnMut` as "not dyn-compatible" (`Basis: source + execution`).

---

### 3.6 Smart-Pointer `dyn` Receivers, `LegacyReceiver`, and `DispatchFromDyn` ABI Erasure

`Basis: source + execution`

For any method whose receiver is not bare `Self`, `dyn_compatibility.rs:695-838` checks dispatchability by constructing a fresh placeholder type parameter `U: Trait + MetaSized` plus `Self: Unsize<U>` and checking:
```text
Receiver[Self => Self] : DispatchFromDyn<Receiver[Self => U]>
```
Notice why double-indirection receivers such as `&&Self`, `&Rc<Self>`, or `Rc<Box<Self>>` fail `E0038` (`undispatchable_double_indirection_e0038`): a thin pointer `&(&T)` points to a concrete thin reference `&T` on the stack/heap whose pointee metadata `(data_ptr, vtable_ptr)` does not exist in memory without allocating or rewriting an intermediate wide pointer (`dyn_compatibility.rs:664-670`).

Two orthogonally enforced gates determine valid `dyn` receivers:
1. **Method Well-Formedness (`compiler/rustc_hir_analysis/src/check/wfcheck.rs:1994-2016`):** Without `#![feature(arbitrary_self_types)]` (or `#![feature(arbitrary_self_types_pointers)]` for `*const Self`/`*mut Self`), `receiver_is_valid` requires every autoderef step to implement `core::ops::LegacyReceiver`, which in `core` + `alloc` covers `&T`, `&mut T`, `Pin<Ptr>`, `Box<T, A>`, `Rc<T, A>`, and `Arc<T, A>` (`valid_std_dyn_receivers` compiles and runs all 10 combinations: `&self`, `&mut self`, `Box`, `Rc`, `Arc`, and `Pin<{&, &mut, Box, Rc, Arc}>`, outputting `REF=40 MUT=42 BOX=42 RC=43 ARC=44 PIN_REF=42 PIN_MUT=42 PIN_BOX=45 PIN_RC=46 PIN_ARC=47`). Raw `*const Self` fails **`E0658`** without `#![feature(arbitrary_self_types_pointers)]` (`raw_ptr_receiver_stable_e0658`) and executes cleanly with it (`RAW_PTR_DYN=99`).
2. **`DispatchFromDyn` Coherence (`compiler/rustc_hir_analysis/src/coherence/builtin.rs:287-463`):** Custom `DispatchFromDyn` wrappers (which must also satisfy `CoerceUnsized`) are restricted to `&T`, `*const/*mut T`, `Ty::Pat`, or `struct` types where:
   - Neither `#[repr(C)]` nor `#[repr(packed)]` is present (`DispatchFromDynRepr` error at line `364-366`), so the wrapper obeys `#[repr(transparent)]`-compatible ABI layout rules (`coherence/builtin.rs:322-329`),
   - Ignoring `PhantomData`, at most **one** non-1-ZST field is coerced between `ty_a` and `ty_b` via `DispatchFromDyn` (and `coerced_fields` must not be empty or >1), and
   - Any unchanged sibling field (`ty_a == ty_b`) must be a **1-ZST** containing **zero non-region generic type parameters** (`layout.is_1zst() && !ty_a.has_non_region_param()` at lines `398-403`), preventing unsound transmutation across distinct ZST instantiations (`DispatchFromDynZST` error). Under `#![feature(coerce_unsized, dispatch_from_dyn, unsize, arbitrary_self_types)]`, `#[repr(transparent)] struct MyPtr<T: ?Sized>(*const T)` passes both gates and dispatches `p.get()` cleanly (`custom_dispatch_from_dyn_wrapper_nightly_ok`: `CUSTOM_DISPATCH_FROM_DYN=77`) (`Basis: source + execution`).

---

### 3.7 `google/zerocopy` (`0.8.64`) Trait `dyn`-Compatibility Audit

`Basis: source + execution`

Compiling `google/zerocopy` (`zerocopy/src/lib.rs`, `e86eb028` / `907b9175`, `0.8.64`) directly under `rustc 1.98.0-nightly` and probing trait-object formation yields exact per-trait classification across all seven core `zerocopy` safety/conversion traits (`support/probe_results.json`, `d_zerocopy_traits`):

| `zerocopy` Trait (`zerocopy/src/lib.rs`) | Supertraits & Associated Items Relevant to `dyn` | `rustc 1.98.0` Result | Exact Violation Root Causes (`src/lib.rs` lines & `MethodViolation` / `DynCompat`) | Practical Consequence / Usage Pattern |
| :--- | :--- | :--- | :--- | :--- |
| **`Immutable`** (`1731-1738`) | `fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized` | **Dyn-compatible** (`ZC_IMMUTABLE_DYN_OK=1 SIZE=4`) | Exempted by `where Self: Sized` (`0` vtable slots beyond DSA metadata) | `&dyn Immutable` compiles; however `where Self: Immutable` on another trait's method (`IntoBytes::as_bytes`) triggers `WhereClauseReferencesSelf` because `Immutable` is not an `auto trait` and does not imply `Self: Sized` |
| **`Unaligned`** (`6669-6676`) | `fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized` | **Dyn-compatible** (`ZC_UNALIGNED_DYN_OK=1 SIZE=1`) | Exempted by `where Self: Sized` (`0` vtable slots) | `&dyn Unaligned` compiles cleanly; `core::mem::size_of_val(x)` reads DSA slot `1` |
| **`KnownLayout`** (`748-907`) | `only_derive_... where Self: Sized`, `type PointerMetadata`, `type MaybeUninit`, `const LAYOUT: DstLayout`, and 7 static `fn`s | **`E0038`** (`dyn KnownLayout<...>` rejected) | (1) **`const LAYOUT: DstLayout`** (`797`, `FeatureNotEnabled`); (2–8) **7 `StaticMethod` fns**: `raw_from_ptr_len` (`803`), `pointer_to_metadata` (`812`), `size_of_val_raw` (`828`), `raw_dangling` (`838`), `size_for_metadata` (`870`), `size_for_metadata_unchecked` (`887`), `is_valid_metadata` (`904`) | Despite the source comment at lines `749-752` noting `only_derive_... where Self: Sized`, 8 items fail `E0038` |
| **`TryFromBytes`** (`1967-3277+`) | `only_derive_... where Self: Sized` + 13 static associated functions | **`E0038`** (`&dyn TryFromBytes` rejected) | **13 `StaticMethod` violations**: `is_safe<A>` (`1997`, short-circuits at `StaticMethod` before `Generic` / `Self` input check) + 12 `try_{ref,mut}_from_{bytes,prefix,suffix}[_with_elems]` (`2100..3277`) | Trait-level static constructors prevent erasing `TryFromBytes` behind `dyn` |
| **`FromZeros`** (`3770-4150`) | Inherits `: TryFromBytes`; adds `only_derive_... where Self: Sized`, `new_zeroed() where Self: Sized`, `zero(&mut self)` | **`E0038`** (`&dyn FromZeros` rejected) | `zero(&mut self)` is vtable-safe; **all 13 `E0038` violations come from supertrait `TryFromBytes`** (`is_safe`, `try_*` at `1997..3277`) | A wrapper trait exposing `fn zero_dyn(&mut self)` could be `dyn`-compatible only if decoupled from `TryFromBytes` |
| **`FromBytes`** (`4382-5733+`) | Inherits `: FromZeros`; adds static slice/byte constructors | **`E0038`** (`&dyn FromBytes` rejected) | **27 `StaticMethod` violations total**: 13 inherited from `TryFromBytes` + 14 in `FromBytes` (`ref_from_bytes`..`mut_from_bytes_with_elems`, `ref_from` at `5722`, `mut_from` at `5733`; `read_from_*` constructors already carry `where Self: Sized`) | Static constructors cannot return `Result<&Self, ...>` / `Self` on erased `dyn FromBytes` |
| **`IntoBytes`** (`6029-6534`, `no_std`) | `only_derive_... where Self: Sized`, `as_bytes`, `as_mut_bytes`, `write_to`, `write_to_prefix`, `write_to_suffix`, `as_bytes_mut` (plus `#[cfg(feature = "std")] write_to_io`) | **`E0038`** (`&dyn IntoBytes` rejected) | **`as_bytes`** (`6089`, `WhereClauseReferencesSelf`: `Self: Immutable`); **`as_mut_bytes`** (`6165`, `WhereClauseReferencesSelf`: `Self: Immutable + FromBytes`); **`write_to`/`write_to_prefix`/`write_to_suffix`** (`6265`, `6351`, `6446`: **both** `ReferencesSelfOutput` `SizeError<&Self, &mut [u8]>` and `WhereClauseReferencesSelf`); **`as_bytes_mut`** (`6528`, `WhereClauseReferencesSelf`: `Self: FromBytes`) | Crucially, `as_bytes` intentionally omits `Self: Sized` (`lib.rs:6093-6095`), yet `where Self: Immutable` makes `IntoBytes` non-`dyn`-compatible because `Immutable` is non-auto |

---

### 3.8 Kernel-Checked Lean `v4.34.1` Mechanization & Theorem Map

`Basis: derived` (grounded in `source` and validated by Lean `v4.34.1` kernel execution)

`support/DynCompatibilityVtableSlotSoundness.lean` (`2,483` LOC, `983` local declarations, `266` theorems) mechanizes the full `rustc` dyn-compatibility judgment, vtable construction, ABI erasure, `by_val(self)` shimming, `DispatchFromDyn` coercion, constructive violation impossibility counterexamples, and `google/zerocopy` / `SlotProbe` / `AsyncFn*` specimens in pure `prelude` + `Init.*` Lean `v4.34.1`:

- **Purity & Anneal TCB Compliance:** Matching `joshlf/anneal@c131b320e` (`trusted/lean/Trusted/MirAst.lean:77-91` and `trusted/audit/TrustedBoundary.lean`), *every* function and predicate carries an explicit `noncomputable def` modifier with zero `noncomputable section`, zero `deriving` clauses on inductives/structures, zero `partial def`, zero `sorry`, zero `omega`/`bv_decide`/`native_decide`, zero `._unsafe_rec` compiler helpers (`localUnsafeRecs=0`), and strict `[propext]`-only axiom usage (`Classical.choice=false`, `Quot.sound=false`, `sorryAx=false`).
- **Lean Core AST & Evaluator Architecture (Sections 1–4, lines `36-1258`):**
  - `TyExpr` (`selfParam`, `selfAssoc`, `unit`, `prim`, `named`, `dynObj`, `ref`, `rawPtr`, `boxPtr`, `rcPtr`, `arcPtr`, `pinPtr`, `customPtr`, `rpitit`, `fnPtr`), `ReceiverKind`, `ClausePred` (`sizedSelf`, `outlivesStatic`, `autoTrait`, `nonAutoSizedTrait`, `nonAutoUnsizedTrait`, `supertrait`), `MethodDecl`, `AssocConstDecl`, `AssocTyDecl`, `TraitDecl`.
  - Checker functions mirroring `dyn_compatibility.rs`: `methodRequiresSizedSelf`, `virtualCallViolationsForMethod` (preserving early `[.staticMethod]` exit, `Self` exemption from `isDispatchFromDynReceiver`, and `'static`/auto-trait exemptions), `dynCompatViolationsForAssocItem`, `dynCompatViolationsForTrait`, `isDynCompatible`, and `isVtableSafeMethod`.
  - Vtable & dispatch semantics mirroring `vtable.rs` / `middle/ty/vtable.rs`: `ErasedAbiTy`, `eraseMonoTy`, `VtblEntry` (`metadataDropInPlace`, `metadataSize`, `metadataAlign`, `vacant`, `method` with `viaVTableShim`, `traitVPtr`), `ownExistentialVtableEntries`, `buildVtable`, `vtableSlotIndexOfMethod`, `coerceToDyn`, `canInvokeMethodOnDyn`, and `evalDynCall`.

#### Summary of the Four Verified Theorem Families & Concrete Specimens

| Theorem Family | Key Mechanized Theorems (`DynCompatibilityVtableSlotSoundness.lean`) | Exact Proved Claim |
| :--- | :--- | :--- |
| **1. Vtable Completeness & Monomorphic Determinism** | `vtable_safe_method_monomorphic_signature` (`:1498`), `dyn_compatible_trait_live_method_vtable_safe` (`:1579`), `dyn_compatible_trait_complete_vtable_slots` (`:1628`), `vtable_slot_determinism_across_impls` (`:1665`) | Any input-RPITIT-free vtable-safe method has `0` own type/const params and total monomorphic `eraseMonoTy` erasure; every non-`final`, non-`Self: Sized` method of a `dyn`-compatible trait has a unique index `3 ≤ idx < (buildVtable t impl_).length` identically positioned across all concrete `impl`s (populated with `.method` or `.vacant`). |
| **2. `where Self: Sized` Unreachability & `fn by_val(self)`** | `self_sized_item_exempt_from_violations` (`:1706`), `where_self_clone_elaborates_sized_self` (`:1728`), `self_sized_method_omitted_from_vtable` (`:1745`), `self_sized_method_rejected_e0599_never_missing_slot` (`:1762`), `callable_dyn_method_never_missing_slot` (`:1774`), `by_val_self_exempt_from_e0038_yet_fails_safe_call` (`:1826`) | `Self: Sized` (or elaborated `Self: Clone`) yields zero violations and `0` vtable slots (`vtableSlotIndexOfMethod = none`), cannot be called on `dyn` (`E0599`), and never causes `missingVtableSlot` for any callable method. Bare `fn(self)` yields `0` `E0038` violations, gets a `viaVTableShim = true` slot, rejects safe calls with `.e0161MoveUnsized`, and succeeds when `hasUnsizedFnParams = true` (`Box<dyn FnOnce()>`). |
| **3. Uniform ABI Erasure & `DispatchFromDyn`** | `smart_ptr_receivers_dispatch_from_dyn` (`:1876`), `double_indirection_undispatchable` (`:1890`), `bad_custom_ptr_undispatchable` (`:1911`), `dispatch_from_dyn_uniform_abi_soundness` (`:1919`) | `&`, `&mut`, `Box`, `Rc`, `Arc`, `Pin<Ptr>`, raw pointers, and valid transparent single-coerced-field + parameter-free 1-ZST custom pointers satisfy `isDispatchFromDynReceiver`, coerce via `coerceToDyn` preserving `dataPtr` verbatim, and dispatch `evalDynCall` identically; `&&Self` / `Rc<Box<Self>>` trigger `.undispatchableReceiver`. |
| **4. Constructive Impossibility & `zerocopy` Specimens** | `pigeonhole_distinct` (`:630`), `pigeonhole_inj_nat` (`:713`), `generic_method_finite_vtable_impossible` (`:1980`), `gat_finite_existential_erasure_impossible` (`:2030`), `rpitit_single_fixed_abi_impossible` (`:2066`), `generic_method_rejected_e0038` (`:1985`), `gat_without_sized_rejected_e0038` (`:2035`), `rpitit_and_async_fn_rejected_e0038` (`:2075`), `where_non_auto_unsized_rejected_e0038` (`:2146`), `zc_immutable_and_unaligned_dyn_compatible` (`:2333`), `zc_known_layout_and_conversion_traits_e0038` (`:2340`), `slotProbe_exact_vtable_layout_and_vacant_slot` (`:2415`), `async_fn_and_where_self_specimens` (`:2474`) | Constructive `omega`-free/`Classical.choice`-free Pigeonhole theorem proves no finite vtable can cover unbounded injective monomorphizations `instSym : Nat → Nat` or unbounded GAT projections `projSym : Nat → Nat`, and distinct `(size, align)` layouts forbid a single unboxed RPITIT stack ABI. Exact `rfl` theorems reproduce all 7 `zerocopy` traits, the 7-word `SlotProbe` `@vtable.0`/`@vtable.1` split (`m_sized` omitted, `m_send` vacant in `Rc<u32>`, `m_by_val` shimmed), `AsyncFnMut` vs. `AsyncFnOnce`, and `WhereClone` vs. `WhereNonAuto`. |

---

## Boundaries

The scope of this report is bounded explicitly using the four negative-space categories below:

- **`unsupported`:**
  - `TyKind::Dynamic` (`dyn Trait`) in `joshlf/anneal@c131b320e`: `trusted/lean/Trusted/MirAst.lean:308-322` maps `Dynamic(...)` to `MirTy.unsupported`, causing Anneal's symbolic/operational MIR semantics ($M_{\text{anneal}}$) to fail closed with `FaultKind.unsupported` on any trait-object type or virtual call. Extending Anneal to reason about `dyn Trait` requires lifting `VtblEntry` metadata/methods and `ShimKind::VTable` calls into `Trusted.MirAst` and `Trusted.MirSemantics`.
  - On stable Rust (without nightly feature gates): `*const Self` / `*mut Self` dyn receivers (`E0658`, `arbitrary_self_types_pointers`), custom `DispatchFromDyn` wrappers (`coerce_unsized`, `dispatch_from_dyn`, `unsize`, `arbitrary_self_types`), `const C: T where Self: Sized` (`E0658`, `generic_const_items`), calling `fn by_val(self)` directly on a trait object (`E0161` without `unsized_fn_params`), and forming `&dyn AsyncFnOnce() -> T` (`E0191` on `#[unstable(feature = "async_fn_traits")]` `CallOnceFuture`).
- **`known not to apply`:**
  - `where Self: Sized` slot omission does **not** emit a vacant/undef slot in the vtable (`known not to apply` to `VtblEntry::Vacant`): `Self: Sized` removes the entry in `own_existential_vtable_entries_iter`, whereas `VtblEntry::Vacant` keeps the slot index reserved and leaves bytes uninitialized when `instantiate_and_check_impossible_clauses` triggers for a specific concrete type.
  - `MethodViolation::WhereClauseReferencesSelf` is **not** a lint (`known not to apply` to `dyn_compatibility.rs:568` comment) and does **not** trigger on `where Self: Clone` (`known not to apply` to `middle/traits/mod.rs:985` comment): `Clone: Sized` elaborates to `Self: Sized`, whereas non-`Sized` non-auto traits emit a hard `E0038`.
  - The Lean mechanization in `support/DynCompatibilityVtableSlotSoundness.lean` formalizes a clean abstract model (`TyExpr`, `TraitDecl`, `buildVtable`, `evalDynCall`) rather than importing `joshlf/anneal`'s concrete `Trusted.MirAst` or Rust's actual `Ty<'tcx>` compiler data structures (`known not to apply` as an end-to-end equivalence proof over real `rustc` binaries or LLVM codegen).
  - Trait upcasting vptr uniqueness (`known not to apply` across dynamically loaded `cdylib` DSO boundaries; covered empirically in companion corpus studies).
- **`not examined`:**
  - Live compiler probes for `ExplicitlyDynIncompatible` (`#[rustc_dyn_incompatible_trait]`), `CVariadic`, `SupertraitNonLifetimeBinder` (`for<T>`), `SupertraitConst` (`const Trait` `HostEffect`), `TypeConst` `AssocConstViolation::{NonType, Generic, TypeReferencesSelf}` under `gca_min_const_items` (`277240238554`), and trait-upcasting `VtblEntry::TraitVPtr` layout permutations (the latter covered in `custom-unsized-types-coerce-unsized-vtable-metadata-and-gat-lifetime-variance`). These were inspected in `dyn_compatibility.rs` source but not separately compiled in `support/probe_dyn_compatibility_and_zerocopy.py`.
  - Expansion internals of `zerocopy-derive` procedural macros and Cargo feature combinations of `zerocopy` other than `--no-default-features` (`--cfg`-gated `std` methods such as `IntoBytes::write_to_io`).
- **`unknown`:**
  - Whether upstream `rust-lang/rust` will stabilize `generic_const_items` (`#113521`), `gca_min_const_items`, `arbitrary_self_types` (`#44874`), or `unsized_fn_params` with altered dyn-compatibility predicates in future versions beyond `277240238554`, or whether `WhereClauseReferencesSelf` comments will be updated upstream.

---

## Evidence

### 5.1 Primary Git Source & Specification Locations

`Basis: normative + documentation + source`

| Repository / Component | Exact Revision | Inspected Files & Symbols / Line Ranges | Role in Report |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` (HEAD) | `277240238554297f93fa9ee3c7643dfa03ccbbb4` | `compiler/rustc_trait_selection/src/traits/dyn_compatibility.rs:38-1078` (`hir_ty_lowering_dyn_compatibility_violations`, `is_vtable_safe_method`, `dyn_compatibility_violations_for_trait`, `generics_require_sized_self`, `dyn_compatibility_violations_for_assoc_item`, `virtual_call_violations_for_method` `[526: self_param]`, `receiver_is_dispatchable`, `IllegalSelfTypeVisitor`, `IllegalRpititVisitor`) | Canonical checker rules and HEAD evolution (`gca_min_const_items`, `SupertraitConst`, `SupertraitNonLifetimeBinder`) |
| `rust-lang/rust` (1.98 baseline) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_trait_selection/src/traits/dyn_compatibility.rs:1-989` (`520: self_param`, `371: min_generic_const_args`), `vtable.rs`, `hir_dyn_trait.rs` | Executed toolchain source exact line correspondence |
| `rust-lang/rust` (Vtable & Diagnostics) | `277240238554297f93fa9ee3c7643dfa03ccbbb4` | `compiler/rustc_trait_selection/src/traits/vtable.rs:204-310` (`own_existential_vtable_entries_iter`, `vtable_entries`, `VtblEntry::Vacant`); `compiler/rustc_middle/src/ty/vtable.rs:13-156` (`VtblEntry`, `COMMON_VTABLE_ENTRIES`, `vtable_allocation_provider`); `compiler/rustc_middle/src/traits/mod.rs:700-1033` (`DynCompatibilityViolation`); `compiler/rustc_trait_selection/src/error_reporting/traits/mod.rs:680-860` (`report_dyn_incompatibility`) | Vtable layout, uninit `Vacant` emission, and hard `E0038` rendering |
| `rust-lang/rust` (Lowering, Receivers, Shims, Borrowck, Std) | `277240238554297f93fa9ee3c7643dfa03ccbbb4` / `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_hir_analysis/src/hir_ty_lowering/dyn_trait.rs:129-310` (`UNUSED_ASSOCIATED_TYPE_BOUNDS`); `coherence/builtin.rs:287-463` (`visit_implementation_of_dispatch_from_dyn`); `wfcheck.rs:1975-2065` (`LegacyReceiver`); `compiler/rustc_mir_transform/src/shim.rs:32-40, 830-870` (`ShimKind::VTable`); `rustc_borrowck/src/session_diagnostics.rs:9-16` (`MoveUnsized` `E0161`); `library/core/src/ops/async_function.rs:15-130`; `library/alloc/src/lib.rs:199`, `library/alloc/src/boxed.rs:2273-2279` | Smart-pointer `DispatchFromDyn` rules, `VTable` shim, `E0161` vs `E0038`, `Box<dyn FnOnce()>`, and `AsyncFn*` definitions |
| `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | `src/items/traits.md:70-160` (`Dyn compatibility`, lines `102, 105, 108`) | Normative/descriptive comparison establishing `by_val(self)` and `AsyncFnOnce` discrepancies |
| `google/zerocopy` (`0.8.64`) | `e86eb0281380bdc278f4b4b3788dc9525ef59035` & `907b9175fee081872ec883ca4709e6ad922f8ed0` | `zerocopy/src/lib.rs`: `KnownLayout` (`748-907`), `Immutable` (`1731-1738`), `TryFromBytes` (`1967-3277+`), `FromZeros` (`3770+`), `FromBytes` (`4382-5733+`), `IntoBytes` (`6029-6534`), `Unaligned` (`6669-6676`) | Real-crate `zerocopy` trait `dyn`-compatibility audit (`diff -u` verified zero diffs below line 12 between `907b9175` and `e86eb028`) |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean:75-92, 272-322` (`noncomputable` convention, `MirTy.unsupported` for `TyKind::Dynamic`); `trusted/audit/TrustedBoundary.lean` | Kernel purity rules and current MIR support status for `dyn` |

---

### 5.2 Complete Live `rustc 1.98.0-nightly` Execution Results (`support/probe_results.json`)

`Basis: execution`

All 30+ compiler probes and real `zerocopy` builds were executed on `2026-11-23` using `support/probe_dyn_compatibility_and_zerocopy.py` inside a clean `tempfile.TemporaryDirectory()` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), with `--remap-path-prefix` stripping temporary/sysroot paths. Exact outcomes in `support/probe_results.json`:

1. **`a_violations` (23 probes covering every `DynCompatibilityViolation` and exemption):**
   - `i_sized_self_supertrait_e0038` -> `rc=1`, `["E0038"]` (`...because it requires Self: Sized`)
   - `i_sized_self_where_e0038` -> `rc=1`, `["E0038"]` (`...because it requires Self: Sized`)
   - `i_supertrait_self_type_arg_e0038` -> `rc=1`, `["E0038", "E0277"]` (`trait Bad: Super<Self>`)
   - `i_supertrait_self_proj_input_e0038` -> `rc=1`, `["E0038"]` (`trait Bad: Sup<Self::Out> { type Out; }`)
   - `i_supertrait_self_proj_output_ok` -> `rc=0`, run `rc=0`, `SUPERTRAIT_PROJ_OUT=17` (`trait Sub: Sup<Item = Self::Out>`)
   - `ii_generic_method_e0038` -> `rc=1`, `["E0038"]` (`method foo has generic type parameters`)
   - `ii_generic_method_where_self_sized_ok` -> `rc=0`, run `rc=0`, `SIZED_EXEMPT_OK=7 DYN_OK=42`
   - `ii_generic_method_where_self_sized_dyn_call_rejected` -> `rc=1`, error `the foo method cannot be invoked on a trait object`
   - `iii_static_method_e0038` -> `rc=1`, `["E0038"]` (`associated function make has no self parameter`)
   - `iii_static_method_where_self_sized_ok` -> `rc=0`, run `rc=0`, `STATIC_EXEMPT_OK=11`
   - `iv_self_input_output_e0038` -> `rc=1`, `["E0038"]` (`references the Self type in this parameter` + `in its return type`)
   - `v_by_val_self_allowed_in_dyn_box_call_e0161` -> `rc=1`, `["E0161"]` (`cannot move a value of type dyn ByVal`)
   - `v_by_val_self_allowed_in_dyn_ref_call_e0161_e0507` -> `rc=1`, `["E0161", "E0507"]`
   - `v_by_val_self_allowed_in_dyn_unused_ok` -> `rc=0`, run `rc=0`, `BY_VAL_TYPE_ALLOWED_PEEK=41`
   - `v_by_val_where_self_sized_call_rejected` -> `rc=1`, `error: the by_val method cannot be invoked on a trait object` (not `E0161`)
   - `v_by_val_unsized_fn_params_nightly_ok` -> `rc=0`, run `rc=0`, `UNSIZED_FN_PARAMS_OK=42`
   - `v_box_dyn_fnonce_stable_ok` -> `rc=0`, run `rc=0`, `BOX_DYN_FNONCE_LEN=9`
   - `vi_assoc_const_e0038` -> `rc=1`, `["E0038"]` (`contains associated const C`)
   - `vi_assoc_const_where_self_sized_e0658` -> `rc=1`, `["E0658"]` (`generic const items are experimental`)
   - `vi_assoc_const_nightly_generic_const_items_self_sized_ok` -> `rc=0`, run `rc=0`, `GENERIC_CONST_ITEMS_SELF_SIZED_OK=99`
   - `vii_assoc_ty_non_gat_missing_e0191` -> `rc=1`, `["E0191"]`
   - `vii_assoc_ty_non_gat_specified_ok` -> `rc=0`, run `rc=0`, `ASSOC_TY_OK=123`
   - `vii_gat_e0038` -> `rc=1`, `["E0038"]` (`contains generic associated type Item`)
   - `vii_gat_where_self_sized_ok` -> `rc=0`, run `rc=0`, `GAT_EXEMPT_TAG=55 CONCRETE_BORROW=55`
   - `vii_gat_where_self_sized_unused_bound_lint` -> `rc=0`, warning `unused_associated_type_bounds`
   - `viii_rpitit_and_async_fn_e0038` -> `rc=1`, `["E0038"]` (both `ReferencesImplTraitInTrait` and `AsyncFn`)
   - `viii_rpitit_and_async_fn_where_self_sized_ok` -> `rc=0`, run `rc=0`, `RPITIT_EXEMPT=88 ASYNC_EXEMPT=88`
   - `ix_where_self_clone_elaborates_to_sized_ok` -> `rc=0`, run `rc=0`, `CLONE_ELAB_SIZED_TAG=30 CONCRETE_F=31`
   - `ix_where_self_clone_dyn_call_rejected` -> `rc=1`, `error: the f method cannot be invoked on a trait object ... this has a Sized requirement`
   - `ix_where_self_non_auto_unsized_e0038` -> `rc=1`, `["E0038"]` (`method f references the Self type in its where clause`)
   - `ix_where_self_static_and_auto_ok` -> `rc=0`, run `rc=0`, `PLAIN=10 SEND=12 STATIC=11 RC_PLAIN=20`
   - `ix_where_self_send_called_without_send_e0277` -> `rc=1`, `["E0277"]` (`dyn WhereSend cannot be sent between threads safely`)
   - `x_async_fn_traits_stable_e0038_vs_e0191` -> `rc=1`, `["E0038", "E0191"]` (`E0038` on `AsyncFn`/`AsyncFnMut`, `E0191` on `AsyncFnOnce`)
   - `x_box_dyn_async_fn_once_nightly_ok` -> `rc=0`, run `rc=0`, `BOX_DYN_ASYNC_FN_ONCE=64`
2. **`b_receivers` (5 receiver probes):**
   - `valid_std_dyn_receivers` -> `rc=0`, run `rc=0`, `REF=40 MUT=42 BOX=42 RC=43 ARC=44 PIN_REF=42 PIN_MUT=42 PIN_BOX=45 PIN_RC=46 PIN_ARC=47`
   - `undispatchable_double_indirection_e0038` -> `rc=1`, `["E0038"]` (`dbl_ref` and `rc_box`)
   - `raw_ptr_receiver_stable_e0658` -> `rc=1`, `["E0658"]`
   - `raw_ptr_receiver_nightly_arbitrary_ok` -> `rc=0`, run `rc=0`, `RAW_PTR_DYN=99`
   - `custom_dispatch_from_dyn_wrapper_nightly_ok` -> `rc=0`, run `rc=0`, `CUSTOM_DISPATCH_FROM_DYN=77`
3. **`c_vtable_ir` (`SlotProbe` LLVM IR):** `compile_returncode=0`, `vtable_count=2` (`@vtable.0` and `@vtable.1`), confirming `7` logical words with `m_sized` absent, `[8 x i8] undef` vacant slot at index `4` of `@vtable.0`, and `...8m_by_val6vtable...` shim at index `5`.
4. **`d_zerocopy_traits` (`zerocopy` `0.8.64`, `CARGO_PKG_VERSION=0.8.64`, `--edition=2021` compile `rc=0`):**
   - `Immutable_dyn_ok` -> `rc=0`, run `rc=0`, `ZC_IMMUTABLE_DYN_OK=1 SIZE=4`
   - `Unaligned_dyn_ok` -> `rc=0`, run `rc=0`, `ZC_UNALIGNED_DYN_OK=1 SIZE=1`
   - `KnownLayout_e0038` -> `rc=1`, `["E0038"]` (assoc const `LAYOUT` + 7 static fns)
   - `TryFromBytes_e0038` -> `rc=1`, `["E0038"]` (13 static fns starting at `is_safe<A>`)
   - `FromZeros_e0038` -> `rc=1`, `["E0038"]` (13 inherited static fns from `TryFromBytes`)
   - `FromBytes_e0038` -> `rc=1`, `["E0038"]` (27 static fns: 13 inherited + 14 `FromBytes`)
   - `IntoBytes_e0038` -> `rc=1`, `["E0038"]` (6 methods hitting `WhereClauseReferencesSelf` and 3 `write_to*` hitting `ReferencesSelfOutput` + `WhereClauseReferencesSelf`)

---

### 5.3 Preserved Lean `v4.34.1` Formalization & Kernel Audit

`Basis: derived` (machine-checked by Lean `v4.34.1` kernel)

- Artifact: `support/DynCompatibilityVtableSlotSoundness.lean` (`2,483` LOC, `prelude` + `Init.Core`, `Init.Data.Bool`, `Init.Data.Nat.Basic`, `Init.Data.List.Basic` only).
- Verified with strict Lean kernel checking (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) exiting `0`.
- Independently inspected via Lean MetaM environment & axiom traversal:
  `AUDIT_SUMMARY localDecls=983 localTheorems=266 localUnsafeRecs=0 localPartials=0 localUnsafeConsts=0 badAxioms=0 propext=true quot=false`

## Revalidation

To cheaply revalidate all primary claims on a newer `rustc`, `google/zerocopy`, or `leanprover/lean4` toolchain without repeating the full literature search:

1. **Upstream Source Diff Guard:** Check the narrow compiler functions and doc locations that determine dyn-compatibility and vtable slots:
   ```bash
   git -C /path/to/rust-lang/rust diff <OLD_SHA> <NEW_SHA> -- \
     compiler/rustc_trait_selection/src/traits/dyn_compatibility.rs \
     compiler/rustc_trait_selection/src/traits/vtable.rs \
     compiler/rustc_middle/src/ty/vtable.rs \
     compiler/rustc_hir_analysis/src/coherence/builtin.rs \
     compiler/rustc_mir_transform/src/shim.rs
   ```
   Verify whether `receiver_ty != tcx.types.self_param` (`520`/`526`), `WhereClauseReferencesSelf`, `gca_min_const_items`, or `own_existential_vtable_entries_iter` changed semantics.
2. **Re-run Live `rustc` + `zerocopy` Probe Suite:** Run the self-contained script inside a temporary directory (zero persistent files outside `--out`):
   ```bash
   python3 support/probe_dyn_compatibility_and_zerocopy.py \
     --zerocopy-root /path/to/google/zerocopy \
     --out /tmp/reval_probe_results.json
   ```
   Confirm `Immutable_dyn_ok` and `Unaligned_dyn_ok` exit `0`, `KnownLayout`/`TryFromBytes`/`FromZeros`/`FromBytes`/`IntoBytes` emit `E0038`, `@vtable.0` keeps `[8 x i8] undef` while omitting `m_sized`, `v_by_val_self_allowed_in_dyn_box_call_e0161` hits `E0161`, and `x_async_fn_traits_stable_e0038_vs_e0191` matches expected diagnostics.
3. **Re-verify Lean `v4.34.1` Formalization & Kernel Purity:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/DynCompatibilityVtableSlotSoundness.lean
   ```
   Confirm exit code `0`, `0` `sorry`s, `0` `omega`/`bv_decide`/`native_decide`/`Classical.choice`/`._unsafe_rec`, and `propext`-only kernel axioms.
4. **Validate Corpus Package Contract:** Run from corpus root:
   ```bash
   python3 tools/reference.py catalog && python3 tools/reference.py check
   ```
