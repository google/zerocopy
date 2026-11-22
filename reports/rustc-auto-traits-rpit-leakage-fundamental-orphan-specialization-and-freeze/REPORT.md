# rustc Auto-Trait Synthesis, RPIT Leakage, `#[fundamental]` Orphan Coherence, `min_specialization`, `#[marker]`, Negative Coherence, and `Freeze` ELF Placement

## Summary

This report establishes primary-source compiler evidence, live `rustc` + `readelf` execution results (18 core test cases plus 8 supplementary discriminators), and a kernel-checked Lean `v4.34.1` formalization (23 theorems, zero `sorry`, zero `Classical.choice`, zero `._unsafe_rec`) for six tightly coupled trait-system and codegen invariants in `rustc` that sit directly upstream of post-monomorphization MIR verification boundaries such as Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):

1. **Return-Position `impl Trait` (`RPIT`) Auto-Trait Leakage vs. `dyn Trait` Erasure:** Outside the defining scope and outside coherence checking, `rustc` reveals the concrete hidden type of an opaque `impl Trait` (`ty::Alias` with `ty::Opaque`) to synthesize `Send`, `Sync`, `Unpin`, and `Freeze` structurally (`constituent_types_for_auto_trait` via `tcx.type_of_opaque(def_id)`). In contrast, trait objects (`ty::Dynamic`) never receive an `AutoImplCandidate`; they implement an auto trait if and only if that trait appears explicitly in the object's existential predicates or as a supertrait of its principal trait (`assemble_candidates_from_object_ty`). Thus `fn mk() -> impl Debug { 42u32 }` leaks `Send + Sync + Unpin + Freeze`, `Cell<u32>` leaks `Send` while blocking `Sync` and `Freeze`, `Rc<u32>` blocks `Send`, `PhantomPinned` blocks `Unpin`, and `Box<dyn Debug>` blocks `Send` unconditionally regardless of its boxed value.
2. **`#[fundamental]` Orphan Rules & Uncovered Generic Parameters:** `rustc_next_trait_solver::coherence::orphan_check_trait_ref` (re-exported by `rustc_trait_selection::traits::coherence`) performs a strict left-to-right tree walk across `[Self, T1, ..., Tn]`, looking through built-in references (`&T`, `&mut T`) and `#[fundamental]` ADTs (`Box<T, A>`, `Pin<Ptr>`) while halting at non-fundamental foreign ADTs (`Vec<T>`, `Option<T>`). A local impl of a foreign trait succeeds only if it reaches a crate-local nominal type before any uncovered generic type parameter (`E0210`) and without stalling on non-fundamental foreign wrappers (`E0117`). Consequently, `Box<Local>`, `&Local`, `&mut Local`, and `Pin<Box<Local>>` are admitted; `Vec<Local>` and `Option<Local>` fail `E0117`; `impl<T> ForeignTr for Box<T>` fails `E0210`. Foreign auto traits additionally bypass `#[fundamental]` and require a directly local nominal `struct`/`enum`/foreign type (`E0321`), so `unsafe impl Send for Box<Local>` is rejected.
3. **Two-Layer `min_specialization` Soundness Defense Against Region Erasure:** Because Rust erases lifetimes before monomorphization, any specialization dispatch that depends on region bounds or region equalities is unsound. `rustc` blocks lifetime-dependent specialization in two distinct compiler layers:
   - *Layer 1 (Specialization Graph Ordering):* `rustc_trait_selection::traits::specialize::specializes` evaluates parent predicates via `evaluate_obligations_error_on_ambiguity()` without resolving region constraints. When two impls differ only by `'static` bounds (`impl<T> BadSpec for T` vs. `impl<T: 'static> BadSpec for T`) or lifetime equalities (`(&'a u8, &'b u8)` vs. `(&'a u8, &'a u8)`), both `specializes(child, parent)` and `specializes(parent, child)` return `true` (`le == ge`), causing `specialization_graph::Children::insert` to reject the impl immediately with `E0119`.
   - *Layer 2 (`check_always_applicable`):* Even when strict ordering `le && !ge` holds (such as `impl Tr for &'static u8`, `impl<T> Tr for (T, T)`, or `impl<T: Clone> Tr for T` over `impl<T> Tr for T`), `rustc_hir_analysis::impl_wf_check::min_specialization::check_always_applicable` rejects direct `'static` lifetimes, repeated unconstrained parameters, empty specializations, and non-`#[rustc_specialization_trait]` / non-marker trait bounds.
4. **`#[marker]` Overlapping Blanket Impls & the Zero-Item Invariant (`E0714` / `E0715`):** `TyCtxt::impls_are_allowed_to_overlap` permits arbitrary same-polarity overlap among impls of `#[marker]` traits (`ImplOverlapKind::Permitted { marker: true }`), enabling simultaneous `impl<T: Copy> MyMark for T` and `impl<T: Clone> MyMark for T`. Coherence remains sound solely because well-formedness checking (`rustc_hir_analysis::check::wfcheck::check_trait`) rejects any associated item on a `#[marker]` trait with `E0714` (backed by `enforce_empty_impls_for_marker_traits` emitting `E0715`), eliminating associated-item dispatch ambiguity.
5. **Negative Impls & `with_negative_coherence` (`OverlapMode::Stable` vs. `OverlapMode::WithNegative`):** Explicit negative auto-trait impls (`impl !Send for NoSend {}`) suppress `AutoImplCandidate` assembly (`for_each_relevant_impl`) and cannot be specialized (`E0366` / `E0367` in `always_applicable::check_negative_auto_trait_impl`). Under `#![feature(with_negative_coherence)]`, `OverlapMode::get` selects `OverlapMode::WithNegative`, enabling `coherence::overlap` to prove negated where-clauses (`impl_intersection_has_negative_obligation` + `try_prove_negated_where_clause`). This unlocks disjoint impls against foreign negative-impl types such as `impl<T: Send> Classify for T` + `impl<T> Classify for Rc<T>`, which fails `E0119` under `OverlapMode::Stable` (due to upstream future-compatibility rules) but compiles and executes cleanly under `OverlapMode::WithNegative`.
6. **`Freeze` Auto-Trait & `UnsafeCell` ELF `.rodata` (`A`) vs. `.data`/`.bss` (`WA`) Codegen Seam:** `core::marker::Freeze` is an internal unsafe auto trait negatively implemented for `UnsafeCell<T>` and positively overridden for indirections and zero-sized markers (`&T`, `&mut T`, `*const T`, `*mut T`, `PhantomData<T>`). During constant interning of immutable statics (`InternKind::Static(Mutability::Not)` in `rustc_const_eval/src/interpret/intern.rs`), `ret.layout.ty.is_freeze(...)` selects `Mutability::Not` vs. `Mutability::Mut`; LLVM codegen (`rustc_codegen_llvm/src/consts.rs`) forwards `alloc.mutability.is_not()` to `llvm::set_global_constant(g, true)`. Empirically on `x86_64-unknown-linux-gnu`, `static FROZEN_STAT: u32` and `static PHANTOM_FREEZE_STAT` (wrapping `PhantomData<UnsafeCell<u32>>`) land in `.rodata.*` (`PROGBITS`, flags `A`), whereas `static UNFROZEN_STAT` (non-zero `UnsafeCell<u32>`) lands in `.data.UNFROZEN_STAT` (`PROGBITS`, flags `WA`) and zero-initialized `static ZERO_UNFROZEN_STAT` lands in `.bss.ZERO_UNFROZEN_STAT` (`NOBITS`, flags `WA`).

## Applicability

### Studied Subjects and Relationships

This report synthesizes evidence across five durable upstream subjects recorded in `REPORT.json`:

1. **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, 2026-05-31, LLVM `22.1.6`, host `x86_64-unknown-linux-gnu`):** Used for both direct primary-source code inspection and live compilation/execution of all 18 core probe cases, 8 supplementary discriminators, and ELF object inspection via GNU `readelf` 2.47 (`support/probe_auto_traits_orphan_spec.py` and `support/probe_results.json`).
2. **`rust-lang/rust` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (upstream `main` as of 2026-11-22):** Audited side-by-side at the source level against `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` to verify structural continuity and document exact file/line drift across the six-month window between the executed nightly and upstream `main`.
3. **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:** Audited at `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/rustc-capture/src/driver.rs` (which pins `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`, commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, one day prior to the executed nightly) to map how these `rustc` type-system and codegen guarantees relate to Anneal's fail-closed `Runtime(PostCleanup)` MIR trusted boundary.
4. **`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:** Consulted for normative language rules covering trait coherence, orphan rules, `#[fundamental]` types, auto traits, `impl Trait`, trait objects, and interior mutability (`UnsafeCell`).
5. **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):** Used to kernel-check the standalone soundness formalization in `support/AutoTraitsOrphanAndSpecializationSoundness.lean` with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

### Shared vs. Revision-Specific Behavior (`14210df0e` vs. `342d74463`)

All six semantic mechanisms, diagnostic codes (`E0277`, `E0117`, `E0210`, `E0119`, `E0714`, `E0715`, `E0321`, `E0366`), and codegen pathways (`is_freeze` -> `intern_const_alloc_recursive` -> `llvm::set_global_constant`) are preserved between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`. Confirmed source-level structural differences between the two revisions are limited to code organization and refactoring:

- `library/alloc/src/rc.rs` (`14210df0e`, `Rc` at L320, `impl !Send` at L330) moved into a directory module `library/alloc/src/rcs/rc.rs` on `342d74463` (`Rc` at L325, `impl !Send` at L338, `impl !Sync` at L346).
- `library/core/src/cell.rs` added an explicit `#[rustc_assert_variance(invariant)]` annotation on `UnsafeCell` (`342d74463` L2313 vs. `14210df0e` L2323).
- `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs` extracted opaque-type auto-trait leakage into a dedicated helper `consider_auto_trait_candidate_for_opaque_ty` (`342d74463` L1321) alongside `consider_auto_trait_candidate` (`14210df0e` L201 vs. `342d74463` L194).
- `compiler/rustc_trait_selection/src/traits/coherence.rs` contracted from 868 lines (`14210df0e`) to 744 lines (`342d74463`), shifting `impl_intersection_has_negative_obligation` from L494 to L388 and `try_prove_negated_where_clause` from L663 to L561 while retaining the same `OverlapMode::WithNegative` negated-where-clause logic.

### Configuration, Edition, and Feature-Gate Scope

- All Rust probes were compiled with `--edition=2024` on `x86_64-unknown-linux-gnu`.
- Part A (`RPIT` leakage vs. `dyn Trait`) and Part B (`#[fundamental]` orphan rules) use strictly stable Rust features (except the supplementary `Freeze` RPIT check, which uses `#![feature(freeze)]`).
- Part C requires nightly `#![feature(min_specialization)]` and `#![feature(marker_trait_attr)]`.
- Part D requires nightly `#![feature(negative_impls)]` and `#![feature(with_negative_coherence)]` for negative-impl coherence; the ELF `.rodata`/`.data`/`.bss` `Freeze` probe compiles on stable 2024 Rust syntax with `--crate-type=lib --emit=obj -C opt-level=2`.
- ELF section flags (`A`, `WA`) and section types (`PROGBITS`, `NOBITS`) are specific to ELF targets (`x86_64-unknown-linux-gnu`); Mach-O (`__TEXT,__const` vs. `__DATA,__data`) and PE/COFF (`.rdata` vs. `.data`) use different section naming conventions for the same LLVM `constant` global flag.
- Execution results were acquired under the default classic trait solver (with `-Znext-solver=coherence` enabled by `rustc` where configured in coherence). Source inspection covers both the classic solver (`rustc_trait_selection`) and the next-generation trait solver (`rustc_next_trait_solver`).

## Findings

### 1. Structural Auto-Trait Synthesis, `RPIT` Leakage, and `dyn Trait` Erasure

Basis: normative + source + execution + derived (Lean mechanization)

#### 1.1 Auto-Trait Definitions and Core Negative/Positive Overrides

In `library/core/src/marker.rs` (`14210df0e` / `342d74463`), the four primary language auto traits are declared as:

| Auto Trait | Declaration (`14210df0e` / `342d74463`) | Safety / Stability | Key Library Overrides |
| :--- | :--- | :--- | :--- |
| `Send` | `pub unsafe auto trait Send` (`marker.rs` L92 / L93) | `unsafe`, stable | `impl<T: ?Sized, A: Allocator> !Send for Rc<T, A>` (`rc.rs` L330 / `rcs/rc.rs` L338); `!Send` for `*const T`, `*mut T`; `Send` for `&T` iff `T: Sync`; `Send` for `&mut T` iff `T: Send`. |
| `Sync` | `pub unsafe auto trait Sync` (`marker.rs` L657 / L658) | `unsafe`, stable | `impl<T: ?Sized> !Sync for UnsafeCell<T>` (`cell.rs` L2328 / L2318), `Cell<T>` (`cell.rs` L325 / L330), `RefCell<T>` (`cell.rs` L1439 / L1444), `Rc<T, A>` (`rcs/rc.rs` L346), `*const T`, `*mut T`. |
| `Unpin` | `pub auto trait Unpin {}` (`marker.rs` L1014 / L1015) | safe, stable | `impl !Unpin for PhantomPinned {}` (`marker.rs` L1029 / L1031); unconditional `Unpin` for `&T`, `&mut T`, `*const T`, `*mut T`, `Box<T, A>`, `Rc<T, A>`; movable coroutines get `BuiltinCandidate`, immovable (`Static`) coroutines suppress `AutoImplCandidate` (`candidate_assembly.rs` L811-824). |
| `Freeze` | `pub unsafe auto trait Freeze {}` (`marker.rs` L906 / L907) | `unsafe`, `#[lang = "freeze"]`, unstable (`feature(freeze)`) | `impl<T: PointeeSized> !Freeze for UnsafeCell<T> {}` (`marker.rs` L909 / L910); unconditional `unsafe impl Freeze` for `PhantomData<T>`, `*const T`, `*mut T`, `&T`, `&mut T` (`marker.rs` L910-918 / L911-919). Manual user impls are forbidden unless `#![feature(freeze_impls)]` is enabled (`rustc_hir_analysis/src/coherence/mod.rs` L62-71). |

The normative Rust Reference (`src/special-types-and-traits.md` L156-184, `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`) specifies that auto traits are automatically implemented for compound types when all constituent fields implement the trait, unless overridden by an explicit positive or negative implementation (`impl !AutoTrait for T`).

#### 1.2 Candidate Assembly Divergence: `RPIT` (`ty::Opaque`) vs. `dyn Trait` (`ty::Dynamic`)

In `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs` (`14210df0e` L738-977; `342d74463` L740-983), `assemble_candidates_from_auto_impls` handles opaque return types and trait objects on completely different branches:

1. **Explicit-impl preemption (`check_impls`, L749-764):** For concrete structural types (`ty::Adt`, primitives, references, raw pointers, tuples, arrays, closures), `rustc` queries `tcx.for_each_relevant_impl(def_id, self_ty, |_| has_impl = true)`. If *any* explicit impl (positive or negative) matches the root type constructor, `AutoImplCandidate` is **not** pushed. A negative impl such as `impl !Send for NoSend {}` or `impl<T: PointeeSized> !Freeze for UnsafeCell<T> {}` therefore blocks structural synthesis outright without providing a positive candidate.
2. **Unsafe-field guard (L891-895; next solver `trait_goals.rs` L216-220):** Unsafe auto traits (`Send`, `Sync`, `Freeze`) suppress `AutoImplCandidate` whenever `self_ty.has_unsafe_fields()`.
3. **Opaque `RPIT` leakage (`ty::Alias(ty::AliasTy { kind: ty::Opaque { def_id }, .. })`, L841-864):**
   - If the opaque type's declared item bounds already contain the auto trait (`ProjectionCandidate`), `rustc` skips leaking the hidden type to avoid unnecessary query cycles.
   - During coherence (`self.typing_mode().is_coherence()`, L852-855), `rustc` sets `candidates.ambiguous = true` rather than emitting `AutoImplCandidate`—preventing coherence from observing hidden types or triggering cycles with type checking.
   - Inside the opaque's defining scope (`self.infcx.can_define_opaque_ty(def_id)`, L856-860), `rustc` sets `candidates.ambiguous = true` because the hidden type is still being inferred.
   - **Outside the defining scope and outside coherence (L861-863):** `rustc` pushes `AutoImplCandidate`. When `confirm_auto_impl_candidate` invokes `constituent_types_for_auto_trait` (`compiler/rustc_trait_selection/src/traits/select/mod.rs` `14210df0e` L2427-2439; `342d74463` L2301-2313), `rustc` calls `self.tcx().type_of_opaque(def_id)` and returns `[ty.instantiate(self.tcx(), args)]` as the single constituent type. The trait solver then recursively checks the auto trait against the concrete hidden type.
   - The next-generation trait solver (`compiler/rustc_next_trait_solver/src/solve/trait_goals.rs` `14210df0e` L201-266; `342d74463` L194-260 and `consider_auto_trait_candidate_for_opaque_ty` L1321) mirrors this exact rule: outside the defining scope, rigid opaque types skip leakage if the auto trait is already in `item_self_bounds`, otherwise delegate to `structural_traits::instantiate_constituent_tys_for_auto_trait`.
4. **Trait object erasure (`ty::Dynamic(..)`, L768-773 & `assemble_candidates_from_object_ty` L907-977):**
   - `assemble_candidates_from_auto_impls` explicitly does **nothing** for `ty::Dynamic(..)` ("For object types, we don't know what the closed over types are. This means we conservatively say nothing"). Calling `constituent_types_for_auto_trait` on `ty::Dynamic(..)` triggers an internal `bug!` (`select/mod.rs` L2353).
   - Instead, `assemble_candidates_from_object_ty` (`candidate_assembly.rs` L928-944) emits `BuiltinObjectCandidate` **only** when `data.auto_traits().any(|did| did == obligation.predicate.def_id())`, or `ObjectCandidate` when the auto trait is a supertrait of the object's principal trait (L960-974).
   - Furthermore, `orphan_check_impl` (`compiler/rustc_hir_analysis/src/coherence/orphan.rs` L95-122, L166-170) prohibits even the crate defining an auto trait from writing `impl AutoTrait for dyn Trait` or `impl<T: ?Sized> AutoTrait for T`. This preserves the biconditional invariant: `dyn Principal + AutoBounds` implements an auto trait if and only if that auto trait is explicitly in `AutoBounds` or a supertrait of `Principal` (preventing unsound dispatch to `where Self: AutoTrait` methods on erased types).

#### 1.3 Live Empirical Verification (Part A + Supplementary `Freeze` Leakage)

Executed via `support/probe_auto_traits_orphan_spec.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (recorded in `support/probe_results.json`):

| Case ID | Return Signature / Hidden Value | Queried Bound | `compile_rc` | Observed Diagnostic / Stdout |
| :--- | :--- | :--- | ---: | :--- |
| `rpit_leaks_send_sync_unpin_for_u32` | `fn mk() -> impl Debug { 42u32 }` | `Send + Sync + Unpin` | `0` | `RPIT_U32_LEAKS_ALL=ok` |
| `rpit_blocks_send_for_rc` | `fn mk() -> impl Debug { Rc::new(42u32) }` | `Send` | `1` | `error[E0277]`: `` `Rc<u32>` cannot be sent between threads safely `` (`within impl Debug`) |
| `rpit_send_not_sync_for_cell` | `fn mk() -> impl Debug { Cell::new(42u32) }` | `Send` | `0` | `RPIT_CELL_SEND=ok` |
| `rpit_blocks_sync_for_cell` | `fn mk() -> impl Debug { Cell::new(42u32) }` | `Sync` | `1` | `error[E0277]`: `` `Cell<u32>` cannot be shared between threads safely `` (`within impl Debug`) |
| `rpit_blocks_unpin_for_phantom_pinned` | `fn mk() -> impl Debug { PhantomPinned }` | `Unpin` | `1` | `error[E0277]`: `` `PhantomPinned` cannot be unpinned `` (`within impl Debug`) |
| `dyn_trait_does_not_leak_send` | `fn mk() -> Box<dyn Debug> { Box::new(42u32) }` | `Send` | `1` | `error[E0277]`: `` `dyn Debug` cannot be sent between threads safely `` |
| `rpit_leaks_freeze_for_u32` (supp.) | `fn mk() -> impl Debug { 42u32 }` (`feature(freeze)`) | `Freeze` | `0` | `RPIT_FREEZE_U32=ok` |
| `rpit_blocks_freeze_for_cell` (supp.) | `fn mk() -> impl Debug { Cell::new(42u32) }` (`feature(freeze)`) | `Freeze` | `1` | `error[E0277]`: `` `UnsafeCell<u32>: Freeze` is not satisfied in `impl Debug` `` |

Note the subtle `PhantomData` asymmetry directly verified in `support/probe_results.json` and `library/core/src/marker.rs`: `constituent_types_for_auto_trait` (`select/mod.rs` L2415-2420) treats `PhantomData<T>` structurally by returning `[T]`, so `PhantomData<UnsafeCell<u32>>` inherits `!Sync` from `UnsafeCell<u32>` (blocking `static` without `unsafe impl Sync`), yet `marker_impls! { unsafe Freeze for PhantomData<T> }` (`marker.rs` L910-913) preempts `AutoImplCandidate` for `Freeze`, making `PhantomData<UnsafeCell<u32>>` **`Freeze`**.

---

### 2. `#[fundamental]` Orphan Rules, Uncovered Parameters, and Auto-Trait Restrictions

Basis: normative + source + execution + derived (Lean mechanization)

#### 2.1 Normative Rule and `OrphanChecker` Algorithm

The Rust Reference (`src/items/implementations.md` L161-174, `r[items.impl.trait.orphan-rule.def]` and `r[items.impl.trait.fundamental]`) states that `impl<P1..=Pn> Trait<T1..=Tn> for T0` is admissible if either `Trait` is local, or:
1. At least one input type among `T0, T1, ..., Tn` is a local type (let `Ti` be the first such input), and
2. No uncovered type parameter `Pj` appears in `T0..Ti` (prior to the first local type).

In `compiler/rustc_next_trait_solver/src/coherence.rs` (`14210df0e` L221-449; `342d74463` L222-452), re-exported at `compiler/rustc_trait_selection/src/traits/coherence.rs` (`14210df0e` L26; `342d74463` L23) and invoked by `compiler/rustc_hir_analysis/src/coherence/orphan.rs` (`14210df0e` L22-42, L285-361; `342d74463` L22-42, L299-375), `orphan_check_trait_ref` implements this check as a single left-to-right `TypeVisitor` (`OrphanChecker::visit_ty`, L324-449) over the trait reference's arguments (`Self` first, followed by trait type arguments):

- **Primitive, tuple, array, slice, raw pointer, function pointer, `str`, `!`, `UnsafeBinder` (L333-347):** Recorded as `non_local_tys`; traversal returns `ControlFlow::Continue(())` (does *not* descend into tuple/array/slice/raw-pointer elements).
- **Inference variables / placeholders / bound types representing impl generic parameters (L351-358):**
  - In `InCrate::Local` mode: immediately returns `ControlFlow::Break(UncoveredTyParam(ty))`, which `orphan.rs` translates into **`E0210`**.
  - In `InCrate::Remote` mode (used by `trait_ref_is_knowable`, L47-93, to ask whether a downstream/sibling crate *could* implement a trait ref): immediately returns `ControlFlow::Break(LocalTy(ty))` because the remote crate could instantiate the variable with one of its own local types.
- **Built-in fundamental references `ty::Ref(_, ty, _)` (L410):** Transparently recurses via `ty.visit_with(self)` (covering both `&T` and `&mut T`).
- **ADTs `ty::Adt(def, args)` (L411-419):**
  - If `self.def_id_is_local(def.def_id())`: returns `ControlFlow::Break(LocalTy(ty))` (admissible!).
  - Else if `def.is_fundamental()` (set via `#[fundamental]` on `Box<T, A>` at `library/alloc/src/boxed.rs` `14210df0e` L228 / `342d74463` L302 and `Pin<Ptr>` at `library/core/src/pin.rs` `14210df0e` L1088 / `342d74463` L1087): transparently recurses into `args.visit_with(self)`.
  - Else (non-fundamental foreign ADTs such as `Vec<T>` and `Option<T>`): records `found_non_local_ty(ty)` and returns `ControlFlow::Continue(())` **without** visiting `args`. If no subsequent input produces `LocalTy`, `orphan_check_trait_ref` returns `Err(OrphanCheckErr::NonLocalInputType(...))`, which `orphan.rs` reports as **`E0117`**.
- **Opaque types `ty::Alias(ty::Opaque)` (L365-407):** When containing no infer/placeholder/bound type flags, opaque types are deliberately treated as **non-local** even inside their defining crate (L389-405), preventing callers from observing whether an opaque hides a local vs. foreign type and avoiding coherence/typeck cycles.
- **Trait objects `ty::Dynamic(tt, ..)` (L427-434):** Local if and only if the principal trait's `DefId` is local.
- **Constant generic parameters `visit_const` (L451-468):** Always return `ControlFlow::Continue(())` (non-local, never uncovered).
- **Backward-compatibility projection mode (`OrphanCheckMode::Compat`, L20-32, L372-379):** In `Compat` mode, type parameters inside projections are treated as covered (`Continue(())`) while emitting the `UNCOVERED_PARAM_IN_PROJECTION` lint (`orphan.rs` L29-41), whereas `Proper` mode rejects them as uncovered (referencing upstream soundness issues around normalizing projections).

#### 2.2 Why `#[fundamental]` Is a Semver/Coherence Promise

Marking a type `#[fundamental]` is not merely syntactic convenience; it permanently transfers coherence ownership of `Wrapper<DownstreamLocal>` to downstream crates and forbids the defining crate from adding blanket impls `impl<T> ForeignTrait for Wrapper<T>` in future releases (documented inline at `library/core/src/pin.rs` `14210df0e` L1697 / `342d74463` L1701). Conversely, `Vec<T>` and `Option<T>` are deliberately non-fundamental so `alloc`/`core` retain the right to add blanket impls for `Vec<T>` or `Option<T>` without breaking downstream crates—which is why `impl ForeignTr for Vec<Local>` must fail `E0117`.

#### 2.3 Stricter Orphan Rule for Foreign Auto Traits (`E0321`)

Immediately after `orphan_check`, `orphan_check_impl` (`compiler/rustc_hir_analysis/src/coherence/orphan.rs` `14210df0e` L85-271; `342d74463` L99-285) enforces an **additional** soundness restriction on all auto traits (`tcx.trait_is_auto(trait_def_id)`):
- If the auto trait is **remote** (e.g. `Send`, `Sync`, `Unpin`), the `Self` type MUST be a directly local `ty::Adt` (`struct`/`enum`/`union`) or local `ty::Foreign` type (`NonlocalImpl::Allow`, L146-164).
- Fundamental wrappers (`Box<Local>`, `&Local`, `Pin<Box<Local>>`) and tuples (`(LocalA, LocalB)`) are explicitly **disallowed** (`NonlocalImpl::DisallowBecauseNonlocal` / `DisallowOther`, emitting **`E0321`**). As documented in `orphan.rs` L48-77 (citing `#22978`), allowing `impl !Foo for (A, B)` in crate B would break generic reasoning `fn two_foos<A: Foo, B: Foo>()` in crate A, which validly assumes `(A, B): Foo` structurally.

#### 2.4 Live Empirical Verification (Part B + Supplementary Auto-Trait Orphan Check)

All crates in Part B link against an independently compiled upstream library `libforeign_tr.rlib` defining `pub trait ForeignTr { fn tag(&self) -> u32; }`:

| Case ID | Impl Header | `compile_rc` | Error Code | Observed Result |
| :--- | :--- | ---: | :--- | :--- |
| `fundamental_box_ref_pin_local_allowed` | `impl ForeignTr for Box<Local>`, `&Local`, `&mut Local`, `Pin<Box<Local>>` | `0` | — | `FUND_OK=11,22,32,43` (nested `Pin<Box<Local>>` unwraps two `#[fundamental]` layers cleanly) |
| `non_fundamental_vec_local_rejected_e0117` | `impl ForeignTr for Vec<Local>` | `1` | `E0117` | `` `Vec` is not defined in the current crate `` (`impl doesn't have any local type before any uncovered type parameters`) |
| `non_fundamental_option_local_rejected_e0117` | `impl ForeignTr for Option<Local>` | `1` | `E0117` | `` `Option` is not defined in the current crate `` |
| `fundamental_uncovered_generic_box_t_rejected_e0210` | `impl<T> ForeignTr for Box<T>` | `1` | `E0210` | `` type parameter `T` must be used as the type parameter for some local type `` |
| `auto_trait_orphan_rejects_box_local_e0321` (supp.) | `unsafe impl Send for Box<Local>` | `1` | `E0321` | `` cross-crate traits with a default impl, like `Send`, can only be implemented for a struct/enum type defined in the current crate `` |

---

### 3. `min_specialization` Soundness: Why Lifetime Specialization Is Blocked in Two Layers

Basis: source + execution + derived (Lean mechanization)

#### 3.1 The Region-Erasure Soundness Hazard

During monomorphization and MIR lowering, `rustc` erases all lifetime/region parameters (`Region<'tcx>` -> `ReErased`). Consider a hypothetical trait allowing specialization on `'static`:

```rust
trait ExtendLifetime<'a> {
    fn extend(x: &'a u8) -> &'static u8;
}
impl<'a, T> ExtendLifetime<'a> for T { ... }          // fallback
impl<'a, T: 'static> ExtendLifetime<'a> for T { ... } // specialized
```

Inside a generic function `fn f<T>(x: &u8)` that calls `<T as ExtendLifetime>::extend`, borrow checking verifies the call against the generic impl. If monomorphization later dispatches on a concrete type `T = &'local u8` vs. `T = &'static u8`, both types erase to the identical monomorphized type `&u8`—or worse, a type `S<'a>` with a `'static`-specialized `Clone` bound could be dispatched as `'static` after lifetime erasure, enabling safe use-after-free transmutes.

#### 3.2 Layer 1: Region-Blind Specialization Graph Ordering (`E0119`)

When inserting local trait impls into the specialization tree (`compiler/rustc_trait_selection/src/traits/specialize/specialization_graph.rs` `14210df0e` / `342d74463` L140-163), `Children::insert` checks overlapping impls `(impl_def_id, possible_sibling)` by computing:

```rust
let le = tcx.specializes((impl_def_id, possible_sibling));
let ge = tcx.specializes((possible_sibling, impl_def_id));

if le == ge { report_overlap_error(overlap, last_lint_mut) } else { Ok((le, ge)) }
```

Inside `specializes((specializing_impl_def_id, parent_impl_def_id))` (`compiler/rustc_trait_selection/src/traits/specialize/mod.rs` `14210df0e` L239-388; `342d74463` L234-396):
1. `rustc` instantiates `specializing_impl_def_id` with its identity parameters and assumes its `param_env`.
2. `rustc` instantiates `parent_impl_def_id` with fresh inference variables (`parent_args`), equates the two `TraitRef`s (`ocx.eq(...)`), and registers `parent_impl_def_id`'s predicates on `ocx`.
3. `rustc` runs `ocx.evaluate_obligations_error_on_ambiguity()` (L331) and returns `true` if `errors.is_empty()`—**crucially, `specializes` never invokes `infcx.resolve_regions(...)`**.

Because region obligations (`T: 'static`, `'a == 'b`) are deferred to region resolution and never checked inside `specializes`:
- For `impl<T> BadSpec for T` vs. `impl<T: 'static> BadSpec for T`: `specializes(static, generic) == true` AND `specializes(generic, static) == true`. Thus `le == ge` (`true == true`), triggering `report_overlap_error` -> **`E0119`** (`conflicting implementations of trait BadSpec`).
- For `impl<'a, 'b> SameLt for (&'a u8, &'b u8)` vs. `impl<'a> SameLt for (&'a u8, &'a u8)`: unifying `(&'a u8, &'b u8)` with `(&?0 u8, &?0 u8)` succeeds in the type checker (deferring `'a == ?0` and `'b == ?0` as unchecked region constraints), so again `le == true` AND `ge == true` (`le == ge`), emitting **`E0119`** (`conflicting implementations of trait SameLt for type (&u8, &u8)`).

Notice that `select/mod.rs` L2100-2108 explicitly relies on this design: trait selection checks `lhs_evaluation.must_apply_modulo_regions()` and `tcx.specializes((lhs, victim))` modulo regions, delegating residual lifetime soundness to Layer 2 (`min_specialization`).

#### 3.3 Layer 2: `check_always_applicable` in `min_specialization`

Even when two impls *do* differ in non-region structure so that `le == true` and `ge == false` (bypassing Layer 1's `E0119`), lifetime-dependent unsoundness can still sneak in via:
- Direct `'static` in a specialized type header (`impl<T> Tr for T` vs. `impl Tr for &'static u8`),
- Repeated generic parameters (`impl<T> Tr for T` vs. `impl<T> Tr for (T, T)`, which would equate lifetimes when `T = &'a u8` is matched against `(&'a u8, &'b u8)`), or
- Arbitrary trait bounds on the specializing impl (`impl<T> Tr for T` vs. `impl<T: Clone> Tr for T`, because a user crate could implement `Clone` only for `MyRef<'static>`).

Accordingly, `rustc_hir_analysis::impl_wf_check::check_impl_wf` (`14210df0e` L71-73) invokes `check_min_specialization` -> `check_always_applicable` (`compiler/rustc_hir_analysis/src/impl_wf_check/min_specialization.rs` `14210df0e` L85-476; `342d74463` L85-474), which enforces four conjunctive checks (L133-136) after translating `impl1`'s parameters into `impl2`'s unconstrained generic arguments:
1. **`check_has_items` (L139-152):** A specializing impl cannot be empty (`EmptySpecialization`).
2. **`check_static_lifetimes` (L297-306):** Calls `tcx.any_free_region_meets(parent_args, |r| r.is_static())`, emitting `"cannot specialize on 'static lifetime"`.
3. **`check_duplicate_params` (L271-287):** Sorts and deduplicates `cgp::parameters_for(tcx, parent_args, true)`; any repeated unconstrained parameter emits `"specializing impl repeats parameter ..."`.
4. **`check_predicates` / `check_specialization_on` (L319-457):** Every predicate on `impl1` not already present on `impl2` (or implied by well-formedness of `impl1`'s trait arguments) must be either global (`clause.is_global()`), a `ConstArgHasType` clause, a trait marked `#[rustc_specialization_trait]` (`TraitSpecializationKind::AlwaysApplicable`, whose own impls are transitively checked for always-applicability), or an internal marker trait marked `#[rustc_unsafe_specialization_marker]` (`TraitSpecializationKind::Marker`). Any ordinary trait bound (like `T: Clone`) fails with `"cannot specialize on trait ..."`.

Additionally, `check_impl_items_against_trait` (`compiler/rustc_hir_analysis/src/check/check.rs` L1388-1415) forbids specializing async trait methods and return-position `impl Trait` in traits (`RPITIT`), and `check_specialization_validity` (L1170-1229) requires every overridden parent item to be marked `default`.

#### 3.4 Live Empirical Verification (Part C Specialization Cases + Layer-2 Discriminators)

| Case ID | Impl Pair (`#![feature(min_specialization)]`) | Layer Triggered | `compile_rc` | Observed Diagnostic / Stdout |
| :--- | :--- | :--- | ---: | :--- |
| `min_spec_type_concrete_ok` | `impl<T> Tag for T` (`default`) + `impl Tag for u32` | Admitted | `0` | `SPEC=generic,u32` |
| `min_spec_lifetime_static_rejected_soundness` | `impl<T> BadSpec for T` (`default`) + `impl<T: 'static> BadSpec for T` | Layer 1 (`specializes` `le == ge`) | `1` | `error[E0119]: conflicting implementations of trait BadSpec` |
| `min_spec_equal_ref_lifetimes_rejected` | `impl<'a, 'b> SameLt for (&'a u8, &'b u8)` (`default`) + `impl<'a> SameLt for (&'a u8, &'a u8)` | Layer 1 (`specializes` `le == ge`) | `1` | `error[E0119]: conflicting implementations of trait SameLt for type (&u8, &u8)` |
| `layer2_min_spec_static_ref_rejected` (supp.) | `impl<T> Tr for T` (`default`) + `impl Tr for &'static u8` | Layer 2 (`check_static_lifetimes`) | `1` | `error: cannot specialize on 'static lifetime` |
| `layer2_min_spec_duplicate_param_rejected` (supp.) | `impl<T> Tr for T` (`default`) + `impl<T> Tr for (T, T)` | Layer 2 (`check_duplicate_params`) | `1` | `error: specializing impl repeats parameter T` |
| `layer2_min_spec_non_spec_trait_bound_rejected` (supp.) | `impl<T> Tr for T` (`default`) + `impl<T: Clone> Tr for T` | Layer 2 (`check_specialization_on`) | `1` | `error: cannot specialize on trait Clone` |

---

### 4. `#[marker]` Traits: Overlapping Blanket Impls and the Zero-Associated-Item Invariant

Basis: source + execution + derived (Lean mechanization)

When a trait carries `#[marker]` (`#![feature(marker_trait_attr)]`, setting `trait_def.is_marker = true` in `compiler/rustc_middle/src/ty/trait_def.rs` L42):
1. **Permitted Overlap in Coherence (`compiler/rustc_middle/src/ty/mod.rs` `14210df0e` L1689-1728; `342d74463` L1935-1974):** `TyCtxt::impls_are_allowed_to_overlap(def_id1, def_id2)` checks polarity compatibility (rejecting positive-vs-negative overlap at L1711-1715) and, when both impls target a `#[marker]` trait with matching polarity, returns `Some(ImplOverlapKind::Permitted { marker: true })`. `specialization_graph::Children::insert` (`specialization_graph.rs` L148-156) treats this return value as non-conflicting and inserts both impls as siblings without entering `specializes`.
2. **Inference-Safety Guard in Selection (`compiler/rustc_trait_selection/src/traits/select/mod.rs` L2110-2145):** When selecting among multiple overlapping `#[marker]` candidates, `rustc` forbids discarding one candidate in favor of another if the predicate still contains inference variables (`_#0t: MyMark`), preventing arbitrary unification of `_#0t` with `u8` vs. `bool`.
3. **Zero-Item Well-Formedness Enforcement (`E0714` & `E0715`):**
   - `compiler/rustc_hir_analysis/src/check/wfcheck.rs` (`14210df0e` L1179-1191; `342d74463` L1118-1130) iterates over `tcx.associated_item_def_ids(def_id)` whenever `trait_def.is_marker || matches!(trait_def.specialization_kind, TraitSpecializationKind::Marker)` and emits **`E0714`** (`"marker traits cannot have associated items"`) for every method, associated type, or associated constant.
   - `compiler/rustc_hir_analysis/src/coherence/mod.rs` (`14210df0e` L116-137; `342d74463` L118-139) runs `enforce_empty_impls_for_marker_traits` as defense-in-depth, emitting **`E0715`** (`"impls for marker traits cannot contain items"`).
   - `min_specialization.rs` (L107-110) exempts `trait_def.is_marker` from specialization checking because overlapping marker impls have no items to specialize or dispatch.

Live execution confirms both sides of this contract:
- `marker_overlapping_blanket_impls_ok`: `#[marker] trait MyMark {}` with overlapping `impl<T: Copy> MyMark for T {}` and `impl<T: Clone> MyMark for T {}` compiles (`compile_rc = 0`) and executes cleanly for both `7u32` (matching *both* blanket impls) and `String::from("hi")` (`MARKER_OVERLAP=ok`).
- `marker_with_assoc_item_rejected_e0714`: `#[marker] trait BadMarker { const X: u32 = 1; }` fails with `compile_rc = 1` and **`E0714`** (`"marker traits cannot have associated items"`).

---

### 5. Negative Impls & `with_negative_coherence`

Basis: source + execution + derived (Lean mechanization)

#### 5.1 Negative Auto-Trait Impls Are Always-Applicable (`E0366` / `E0367`)

A negative impl `impl !Trait for Ty {}` (gated behind `#![feature(negative_impls)]`) cannot contain associated items (`E0749` in `rustc_hir_analysis/src/check/check.rs` L1263-1275) and cannot overlap a positive impl for the same type (`report_negative_positive_conflict` in `specialize/mod.rs` L451-470, `impls_are_allowed_to_overlap` in `ty/mod.rs` L1711-1715).

For negative auto-trait impls on ADTs, `always_applicable::check_negative_auto_trait_impl` (`compiler/rustc_hir_analysis/src/check/always_applicable.rs` `14210df0e` L88-139; `342d74463` L84-135) enforces the same generality invariants as `Drop`:
1. Every generic parameter of the ADT must appear uniquely in the impl header (`uses_unique_generic_params`, L147-180 -> **`E0366`**: `` `!Send` impls cannot be specialized ``, empirically verified in supplementary case `negative_auto_trait_cannot_be_specialized_e0366` on `impl !Send for Wrapper<u32> {}`).
2. Every where-clause on the negative impl must be implied by the ADT definition itself (`ensure_impl_predicates_are_implied_by_item_defn`, L254-370 -> **`E0367`**).

#### 5.2 Disjoint Coherence Reasoning: `OverlapMode::Stable` vs. `OverlapMode::WithNegative`

In `compiler/rustc_middle/src/traits/specialization_graph.rs` (`14210df0e` / `342d74463` L51-86), `OverlapMode::get(tcx, trait_id)` chooses between:
- `OverlapMode::Stable` (default): `use_negative_impl() == false`, `use_implicit_negative() == true`.
- `OverlapMode::WithNegative` (when `#![feature(with_negative_coherence)]` is active): `use_negative_impl() == true`, `use_implicit_negative() == true`.
- `OverlapMode::Strict` (`with_negative_coherence` + internal `#[rustc_strict_coherence]`): `use_negative_impl() == true`, `use_implicit_negative() == false`.

In `compiler/rustc_trait_selection/src/traits/coherence.rs` (`14210df0e` L243-306, L494-699; `342d74463` L243-299, L388-597), `overlap()` tests disjointness in two steps:
1. **Explicit negative-impl disjointness (`use_negative_impl()`, L252-263):** Calls `impl_intersection_has_negative_obligation` in both directions `(impl1, impl2)` and `(impl2, impl1)`. It unifies fresh impl headers in `TypingMode::Coherence`, plugs remaining inference variables with placeholders (`plug_infer_with_placeholders`, L555-661), elaborates `impl2`'s where-clauses, flips each predicate's polarity (`clause.as_predicate().flip_polarity(tcx)`, L668), and tries to prove the resulting negative predicate (`try_prove_negated_where_clause`, L663-699) under `TypingMode::non_body_analysis()`, including full `ocx.resolve_regions` verification (L693-696). If *any* negated predicate holds (e.g., `Rc<?T>: !Send` from `alloc`'s `impl<T, A> !Send for Rc<T, A>`), `overlap()` returns `None` (disjoint).
2. **Implicit negative reasoning (`use_implicit_negative()`, L299-306 & `impl_intersection_has_impossible_obligation` L404-476):** Evaluates obligations in intercrate coherence mode. A missing impl proves disjointness *only* when `trait_ref_is_knowable` guarantees no upstream or downstream crate can ever add the impl.

This exact distinction is sharply exposed by our empirical probes (`support/probe_results.json`):
- `negative_impl_blocks_send`: `struct NoSend(u32); impl !Send for NoSend {}` fails `assert_send(NoSend(1))` with `E0277`.
- `with_negative_coherence_disjoint_impls_ok`: `impl<T: Send> Classify for T { fn id() -> u32 { 1 } }` + `impl Classify for NoSend { fn id() -> u32 { 2 } }` compiles (`compile_rc = 0`) and prints `NEG_COH=1,2`.
- **Crucial `Stable` vs. `WithNegative` discriminator (supplementary cases `s4` and `s5`):** Writing `impl<T: Send> Classify for T` + `impl<T> Classify for Rc<T>` **without** `#![feature(with_negative_coherence)]` is **rejected with `E0119`** (`note: upstream crates may add a new impl of trait std::marker::Send for type std::rc::Rc<_> in future versions`), because under `OverlapMode::Stable`, `rustc` ignores `alloc`'s explicit `impl !Send for Rc<T, A>` during overlap checking and treats `Rc<_>: Send` as an intercrate upstream ambiguity! Enabling `#![feature(with_negative_coherence)]` switches to `OverlapMode::WithNegative`, proves `Rc<!0>: !Send` via `try_prove_negated_where_clause`, and compiles/executes cleanly (`RC_NEG_COH=1,2`).

---

### 6. `Freeze` Auto-Trait & `UnsafeCell` ELF `.rodata` (`A`) vs. `.data`/`.bss` (`WA`) Codegen Seam

Basis: normative + source + execution + derived (Lean mechanization)

#### 6.1 End-to-End Compiler Pipeline from `UnsafeCell` to ELF Section Flags

The Rust Reference (`src/interior-mutability.md` L1-15) designates `core::cell::UnsafeCell<T>` (`#[lang = "unsafe_cell"]`, `library/core/src/cell.rs` `14210df0e` L2319-2323 / `342d74463` L2309-2313) as the **sole** language primitive permitting mutation through a shared reference. The compiler translates this type-level property into hardware page-permission bits across five exact source locations:

1. **Trait & Negative-Impl Root (`library/core/src/marker.rs` `14210df0e` L904-918; `342d74463` L905-919):**
   - `#[lang = "freeze"] pub unsafe auto trait Freeze {}`
   - `impl<T: PointeeSized> !Freeze for UnsafeCell<T> {}`
   - Positive indirection/ZST overrides: `unsafe Freeze` for `PhantomData<T>`, `*const T`, `*mut T`, `&T`, `&mut T`.
2. **Type-System Fast Path & Query (`compiler/rustc_middle/src/ty/util.rs` `14210df0e` L1144-1180; `342d74463` L1184-1220 & `compiler/rustc_ty_utils/src/common_traits.rs` L25-55):**
   - `Ty::is_freeze(self, tcx, typing_env)` first checks `is_trivially_freeze()` (returning `true` in O(1) for scalars, `str`, `!`, `Ref`, `RawPtr`, `FnDef`, `FnPtr`, and structurally for tuples/arrays/slices of trivially-frozen elements; returning `false` conservatively for all ADTs, closures, trait objects, opaques, params).
   - Otherwise it queries `tcx.is_freeze_raw(typing_env.as_query_input(self))`, implemented in `common_traits.rs` L25-27 via `traits::type_known_to_meet_bound_modulo_regions(&infcx, param_env, query.value, LangItem::Freeze)`.
3. **CTFE Allocation Interning (`compiler/rustc_const_eval/src/interpret/intern.rs` `14210df0e` L85-94, L221-234; `342d74463` L85-94, L222-235):**
   - Inside `intern_const_alloc_recursive`:
     ```rust
     InternKind::Static(Mutability::Not) => {
         (
             // Outermost allocation is mutable if `!Freeze` i.e. contains interior mutable types.
             if ret.layout.ty.is_freeze(*ecx.tcx, ecx.typing_env) {
                 Mutability::Not
             } else {
                 Mutability::Mut
             },
             Mutability::Not,
             true,
         )
     }
     ```
   - `prepare_alloc` (`intern.rs` L85-93) assigns `alloc.mutability = Mutability::Not` when `base_mutability == Mutability::Not`, and asserts `alloc.mutability == Mutability::Mut` when `base_mutability == Mutability::Mut`. (Separately, CTFE shared-reference retagging in `compiler/rustc_const_eval/src/const_eval/machine.rs` L949 also consults `ty.is_freeze(...)` to mark `CtfeProvenance::as_immutable` vs. `as_shared_ref`, rejecting CTFE writes through immutable pointers at L990.)
4. **LLVM Global Constant Flag (`compiler/rustc_codegen_llvm/src/consts.rs` `14210df0e` L410-477; `342d74463` L473-540):**
   - `codegen_static_item` retrieves `(v, alloc)` from `codegen_static_initializer(self, def_id)` and forwards the interned mutability directly to LLVM:
     ```rust
     // Forward the allocation's mutability (picked by the const interner) to LLVM.
     if alloc.mutability.is_not() {
         llvm::set_global_constant(g, true);
     }
     ```
5. **ELF Object Section Emission (LLVM 22.1.6 `x86_64-unknown-linux-gnu`):**
   - `constant` globals without dynamic relocations emit into `.rodata.<SYM>` (`SHT_PROGBITS`, flags `A` = `SHF_ALLOC`, mapped into read-only `PF_R` PT_LOAD segments at link/load time—writing to such memory at runtime faults with `SIGSEGV`).
   - Non-`constant` globals emit into `.data.<SYM>` (`SHT_PROGBITS`, flags `WA` = `SHF_WRITE | SHF_ALLOC`) when non-zero initialized, or `.bss.<SYM>` (`SHT_NOBITS`, flags `WA`) when zero-initialized.

#### 6.2 Live Empirical `readelf` Verification (Part D Case 18)

Compiled with `rustc --edition=2024 --crate-type=lib --emit=obj -C opt-level=2` and inspected with `readelf -S -W` and `readelf -s -W` (`support/probe_results.json`):

| Symbol | Rust Type | `Freeze`? | `Sync`? | ELF Section Name | Section Type | ELF Flags | Size (B) |
| :--- | :--- | :---: | :---: | :--- | :--- | :--- | ---: |
| `FROZEN_STAT` | `u32` (`0x1234_5678`) | Yes | Yes | `.rodata.FROZEN_STAT` | `PROGBITS` | `A` | `4` |
| `PHANTOM_FREEZE_STAT` | `FrozenWithPhantom(u32, PhantomData<UnsafeCell<u32>>)` (`unsafe impl Sync`) | Yes | Manual | `.rodata.PHANTOM_FREEZE_STAT` | `PROGBITS` | `A` | `4` |
| `UNFROZEN_STAT` | `SyncCell(UnsafeCell<u32>)` (`0x1234_5678`, `unsafe impl Sync`) | **No** | Manual | `.data.UNFROZEN_STAT` | `PROGBITS` | `WA` | `4` |
| `ZERO_UNFROZEN_STAT` | `SyncCell(UnsafeCell<u32>)` (`0`, `unsafe impl Sync`) | **No** | Manual | `.bss.ZERO_UNFROZEN_STAT` | `NOBITS` | `WA` | `4` |

`PHANTOM_FREEZE_STAT` empirically confirms the exact indirection/ZST boundary of `Freeze`: even though `PhantomData<UnsafeCell<u32>>` suppresses `Sync` (requiring `unsafe impl Sync` to declare the `static`), `core::marker`'s explicit `unsafe impl<T: PointeeSized> Freeze for PhantomData<T>` overrides `!Freeze`, keeping `PHANTOM_FREEZE_STAT` in read-only `.rodata` (`A`).

---

### 7. Kernel-Checked Lean `v4.34.1` Formalization and Connection to Anneal's TCB

Basis: derived (Lean kernel check) + source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

#### 7.1 Mechanized Theorems and Constructive Counterexamples

`support/AutoTraitsOrphanAndSpecializationSoundness.lean` (960 lines, 40,644 bytes) formalizes all three domains in standalone Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with:
- **0** compiler errors/warnings under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`;
- **0** `sorry`, **0** `Classical.choice`, **0** `Quot.sound`, **0** `Lean.ofReduceBool`, **0** `omega`, **0** `bv_decide`, **0** `native_decide`, **0** `partial def`;
- **0** `._unsafe_rec` auxiliary constants and **0** `partial`/`unsafe` definitions across all 712 local environment declarations (verified via direct `Lean.Environment` inspection). Every recursive term definition carries `noncomputable` solely to suppress Lean's `._unsafe_rec` codegen synthesis while remaining purely constructive.

| Lean Declaration (`AutoTraitsOrphanSpecialization.*`) | Formal Property Established | Kernel Axioms |
| :--- | :--- | :--- |
| `freeze_implies_no_unsafe_cell` | `ImplementsAuto neg .freeze ty → ¬ ContainsDirectUnsafeCell ty` (structural induction over pairs, named ADTs, and RPIT hidden types, while permitting indirections `&T`, `&mut T`, `*const T`, `Box<T>`, `Rc<T>`, and `PhantomData<T>`). | *(none)* |
| `freeze_rodata_placement_sound` | Read-only `.rodata` (`A`) static placement gated by `ImplementsAuto neg .freeze ty` satisfies `StaticSectionSound ty .rodataReadOnly`. | *(none)* |
| `unsafe_cell_not_freeze` | `¬ ImplementsAuto neg .freeze (.unsafeCell t)` for every `neg` and `t`. | *(none)* |
| `rpit_u32_leaks_all`, `rpit_rc_not_send`, `rpit_cell_send_not_sync_not_freeze`, `rpit_phantom_pinned_not_unpin`, `dyn_debug_does_not_leak_send`, `phantom_unsafe_cell_freeze_not_sync`, `negative_impl_blocks_send` | Exact mechanized counterparts to Part A, Part D (`!Send`), and `PhantomData<UnsafeCell<u32>>` empirical cases. | *(none)* except `negative_impl_blocks_send`: `[propext]` |
| `orphan_check_prevents_cross_crate_overlap` | **Global Link-Safety Theorem:** For any two mutually unknowing crates `c₁ ≠ c₂` (`TraitRefAvoidsCrate`), if `OrphanAdmissible c₁ tr₁` and `OrphanAdmissible c₂ tr₂` (with built-in `&`/`&mut` and `#[fundamental]` unwrapping, non-fundamental cutoff, and left-to-right uncovered-param rejection), then no substitutions `(σ₁, σ₂)` satisfy `instantiateTraitRef σ₁ tr₁ = instantiateTraitRef σ₂ tr₂`. Proved via ordered fundamental-leaf precedence (`AppearsBefore c₁ c₂` vs. `AppearsBefore c₂ c₁` in `fundOwnersList`). | *(none)* |
| `pin_box_local_orphan_admissible`, `ref_mut_local_orphan_admissible`, `vec_local_orphan_rejected`, `box_uncovered_param_rejected` | Mechanized witnesses for Part B (`Pin<Box<Local>>`, `&mut Local`, `Vec<Local>`, `Box<T>`). | *(none)* except `vec_local_orphan_rejected`: `[propext]` |
| `lifetime_free_specialization_commutes_with_erasure` & `min_specialization_monomorphization_deterministic` | For every `MinSpecRule` chain matching via region-erased linear patterns (`ErasedSpecPat`), surface dispatch equals post-erasure monomorphization dispatch (`selectSurface (toSurfaceRules rules) defaultImpl t = selectErased rules defaultImpl (eraseRegions t)`), making dispatch invariant under `eraseRegions t₁ = eraseRegions t₂`. | `[propext]` |
| `marker_empty_overlap_coherent` | Overlapping `#[marker]` impls with `Unit` item payload (zero associated items) trivially agree on every applicable type. | *(none)* |
| `negative_coherence_disjoint_impls` | An impl bounded by `ImplementsAuto neg .send` and an impl for `NoSend` (`neg noSendId .send = true`) have empty intersection. | `[propext]` |
| `ce1_lifetime_specialization_unsound_after_region_erasure` (+ `ce1b_equal_lifetime_specialization_unsound_after_region_erasure`) | **Constructive Counterexample 1:** Exhibits `&'static u8` vs. `&'local u8` (and `(&'a u8, &'a u8)` vs. `(&'a u8, &'b u8)`) with identical `eraseRegions` yet distinct surface dispatch, proving `¬ ∃ f : ErasedTy → ImplId` factoring surface dispatch through region erasure. | `[propext]` |
| `ce2_non_fundamental_wrapper_orphan_conflict` | **Constructive Counterexample 2:** Exhibits `impl<T> ForeignTr for Vec<T>` (admissible in `stdCrate = 0`) colliding with `impl ForeignTr for Vec<Local>` (rejected in `localCrate = 2`) on ground instance `ForeignTr for Vec<Local>` if non-fundamental cutoff is violated. | `[propext]` |
| `ce3_marker_trait_with_assoc_const_ambiguous_dispatch` | **Constructive Counterexample 3:** Exhibits overlapping `Copy` (`itemVal = 1`) and `Clone` (`itemVal = 2`) blanket impls on a `#[marker]` trait carrying an illicit `Nat` associated constant, colliding with distinct values on `u32`. | `[propext]` |

#### 7.2 Architectural Mapping to `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`

Direct inspection of `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` shows the exact boundary between `rustc`'s type/coherence/specialization/Freeze passes and Anneal's Lean MIR TCB:

- `trusted/rustc-capture/src/driver.rs` (L25, L75-84) hooks `rustc_driver::Callbacks::after_analysis` on pinned `1.98.0-nightly (f8a08b688 2026-05-30)` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), running *after* trait resolution, coherence, orphan checking, `min_specialization` validation, and borrow checking.
- `trusted/lean/Trusted/MirAst.lean` (L304-321, L469-475) represents post-monomorphization, region-erased `MirTy` values (`MirTy.ref` explicitly omits regions: *"regions are erased at runtime"*). Currently, `MirTy.unsupported` fails closed (`FaultKind.unsupported`) on `TyKind::Dynamic`, non-fieldless-enum `Adt`s (including `UnsafeCell`, `Box`, `Pin`, `Rc`, `Cell`), `TyKind::Alias` (including opaque `RPIT`), and statics; `ProjectionElem.unsupported` fails closed on `OpaqueCast`.
- **Verification consequence (derived):** As Anneal expands `Trusted.MirAst` and `Trusted.MirSemantics` beyond scalar/fieldless-enum fragments to cover `UnsafeCell`, statics, trait objects, `RPIT` return values, and generic/specialized functions, the soundness of post-monomorphization MIR verification depends directly on the six invariants formalized here:
  1. `min_specialization` guarantees that monomorphizing away regions before constructing `MirAst` cannot silently pick a different impl body than surface typing checked.
  2. Orphan-rule link-safety (`orphan_check_prevents_cross_crate_overlap`) and `#[marker]` zero-item enforcement (`E0714`) guarantee that linking independently verified crates cannot introduce conflicting trait/vtable/associated-item resolutions for a monomorphized `DefId`.
  3. `Freeze` (`freeze_implies_no_unsafe_cell`) is the exact type-level boundary determining whether a shared static allocation in a verified MIR/object model may be marked immutable (`Mutability::Not` -> `.rodata` `A`) vs. mutable (`Mutability::Mut` -> `.data`/`.bss` `WA`).
  4. `RPIT` leakage vs. `dyn` erasure establishes that any verified front-end or MIR extractor translating opaque return types must treat `ty::Opaque` auto traits transparently (matching `type_of_opaque`) while treating `ty::Dynamic` auto traits strictly from explicit existential bounds.

## Boundaries

To prevent over-generalization, negative space is classified strictly using the four `reference-corpus/1` distinctions:

1. **Lean Model Isolation from `Trusted.MirSemantics` (`known not to apply` / `not examined`):** `support/AutoTraitsOrphanAndSpecializationSoundness.lean` is a standalone formalization of `rustc`'s type-system, coherence, specialization, and static-section invariants; it does **not** import `Trusted.MirAst` or `Trusted.MirSemantics` from `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (which currently fail closed on `UnsafeCell`, `Dynamic`, `Opaque`, and `static` items). Bridging these invariants into a full verified `rustc` front-end (`rustc_trait_selection` -> `Trusted.MirAst` -> `rustc_codegen_llvm`) was **not examined**.
2. **Coherence `OrphanCheckMode::Compat` Projection Unsoundness (`not examined`):** Our Lean orphan-coherence proof (`orphan_check_prevents_cross_crate_overlap`) models `OrphanCheckMode::Proper` over nominal ADTs, references, and generic type variables without associated-type projection aliases (`ty::Projection`). `rustc`'s legacy `OrphanCheckMode::Compat` mode (`compiler/rustc_next_trait_solver/src/coherence.rs` L23-31, L372-379), which treats type parameters inside projections as covered for backward compatibility (emitting a lint rather than an error, linked to upstream issues `#99554` and `#124559`), is **known not to apply** to our link-safety theorem and was **not examined** empirically.
3. **Full Unsound `#![feature(specialization)]` vs. `#![feature(min_specialization)]` (`known not to apply` / `unsupported`):** Our determinism theorem (`lifetime_free_specialization_commutes_with_erasure`) models only the sound `min_specialization` fragment (`check_always_applicable`). The broader nightly `#![feature(specialization)]` gate omits `check_always_applicable` and is **known not to apply** (it admits known soundness holes when combining trait bounds with lifetime-restricted impls). Likewise, the internal standard-library escape hatch `#[rustc_unsafe_specialization_marker]` (`min_specialization.rs` L58-66) is explicitly documented in `rustc` source as unsound in general (relying on manual audit of zero-method marker traits) and is **known not to apply** to our soundness proof.
4. **Recursive / Coinductive Auto Traits, Coroutine Witnesses, and `UnsafePinned` (`not examined`):** Our Lean `ImplementsAuto` inductive models finite acyclic type trees and does not formalize coinductive cycle handling for recursive ADTs (`struct Node(Option<Box<Node>>)`), coroutine witness types (`ty::CoroutineWitness`), `UnsafePinned<T>` / `UnsafeUnpin` (`marker.rs` L926-940, RFC 3467), or `unsafe` struct fields (`has_unsafe_fields()`). Those cases were **not examined** empirically or mechanically.
5. **Relocation-Bearing `Freeze` Statics & RELRO (`.data.rel.ro`) (`known not to apply`):** On PIC/PIE ELF targets, a `Freeze` static whose initializer contains a pointer relocation (for example `pub static REF: &'static u32 = &FROZEN_STAT;`) is marked `constant` in LLVM IR but cannot be placed in `.rodata` (`A`) because the dynamic linker must patch the address at load time; it lands in `.data.rel.ro` (`WA`, promoted to read-only by `PT_GNU_RELRO` after dynamic relocation). Our `readelf` probe tested relocation-free integer/cell statics; `.rodata` (`A`) placement is **known not to apply** to relocation-bearing `Freeze` statics under PIC.
6. **Non-ELF Object Formats & Next Trait Solver Full-Crate Mode (`not examined`):** Mach-O (macOS), PE/COFF (Windows), and WebAssembly (`wasm.custom_sections` in `rustc_codegen_llvm/src/consts.rs` L487-504) section lowering and full-crate `-Znext-solver=globally` empirical probe execution were **not examined**.
7. **Known Upstream `FIXME` Caveats in `with_negative_coherence` (`unknown`):** `compiler/rustc_trait_selection/src/traits/coherence.rs` (`14210df0e` L519-525, L676-678; `342d74463` L417-423, L574-576) contains open upstream `FIXME`s noting that `impl_intersection_has_negative_obligation` drops header-unification constraints rather than assuming them and forks with `TypingMode::non_body_analysis()` (which may reveal opaque types during negative-coherence checks, recorded upstream as `#132279`). Whether edge-case interactions between opaque `RPIT` auto-trait leakage and `with_negative_coherence` can trigger spurious cycles or completeness gaps remains **unknown** from this investigation.

## Evidence

All evidence below was freshly acquired on `2026-11-22`.

### 1. Upstream Primary Sources (Pinned 40-Hex Commits)

#### `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` executed nightly; `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` `main`)

| File Path | Key Symbol / Logic | `14210df0e` Lines | `342d74463` Lines |
| :--- | :--- | :--- | :--- |
| `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs` | `assemble_candidates_from_auto_impls` (`ty::Dynamic` no-op, `ty::Opaque` leakage outside defining scope / coherence, `for_each_relevant_impl` preemption) | L738-904 | L740-910 |
| `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs` | `assemble_candidates_from_object_ty` (`BuiltinObjectCandidate`, `ObjectCandidate`) | L907-977 | L913-983 |
| `compiler/rustc_trait_selection/src/traits/select/mod.rs` | `constituent_types_for_auto_trait` (`PhantomData`, `Adt`, `ty::Opaque` -> `type_of_opaque(def_id)`) | L2317-2440 | L2188-2314 |
| `compiler/rustc_trait_selection/src/traits/select/mod.rs` | Specialization / `#[marker]` candidate dominance (`must_apply_modulo_regions`, `impls_are_allowed_to_overlap`) | L2095-2145 | L1968-2018 |
| `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs` | `consider_auto_trait_candidate` (+ `consider_auto_trait_candidate_for_opaque_ty` on `342d74463`) | L201-266 | L194-260, L1321 |
| `compiler/rustc_next_trait_solver/src/coherence.rs` | `trait_ref_is_knowable`, `orphan_check_trait_ref`, `OrphanChecker::visit_ty` (`ty::Ref`, `def.is_fundamental()`, `ty::Alias` non-local opaques, `UncoveredTyParam`) | L47-97, L221-469 | L47-97, L222-472 |
| `compiler/rustc_trait_selection/src/traits/coherence.rs` | Re-export `rustc_next_trait_solver::coherence::*`, `overlap`, `impl_intersection_has_impossible_obligation`, `impl_intersection_has_negative_obligation`, `try_prove_negated_where_clause` | L26, L243-346, L404-699 | L23, L243-346, L388-597 |
| `compiler/rustc_hir_analysis/src/coherence/orphan.rs` | `orphan_check_impl`, auto-trait nominal-type restriction (`E0321`), `orphan_check`, `emit_orphan_check_error` (`E0117`, `E0210`) | L22-42, L85-274, L285-420 | L22-42, L99-288, L299-420 |
| `compiler/rustc_trait_selection/src/traits/specialize/mod.rs` | `specializes` (region-blind predicate evaluation), `specialization_graph_provider`, `report_conflicting_impls` (`E0119`) | L239-388, L391-598 | L234-396, L399-617 |
| `compiler/rustc_trait_selection/src/traits/specialize/specialization_graph.rs` | `Children::insert` (`impls_are_allowed_to_overlap`, `if le == ge` conflict check) | L76-193 | L76-193 |
| `compiler/rustc_middle/src/traits/specialization_graph.rs` | `OverlapMode::{Stable, WithNegative, Strict}` and `OverlapMode::get` | L51-86 | L51-86 |
| `compiler/rustc_hir_analysis/src/impl_wf_check/min_specialization.rs` | `check_min_specialization`, `check_always_applicable`, `check_has_items`, `check_duplicate_params`, `check_static_lifetimes`, `check_predicates`, `check_specialization_on` | L85-476 | L85-474 |
| `compiler/rustc_hir_analysis/src/check/wfcheck.rs` | `check_trait` (`E0714` zero-item check on `#[marker]` traits) | L1169-1192 | L1108-1131 |
| `compiler/rustc_hir_analysis/src/coherence/mod.rs` | `enforce_trait_manually_implementable` (`Freeze` gate), `enforce_empty_impls_for_marker_traits` (`E0715`), `check_object_overlap` (`E0371`) | L54-137, L190-246 | L54-139, L192-248 |
| `compiler/rustc_middle/src/ty/mod.rs` | `TyCtxt::impls_are_allowed_to_overlap` | L1689-1728 | L1935-1974 |
| `compiler/rustc_hir_analysis/src/check/always_applicable.rs` | `check_negative_auto_trait_impl` (`E0366`, `E0367`) | L88-181, L254-370 | L84-177, L250-366 |
| `compiler/rustc_middle/src/ty/util.rs` | `Ty::is_freeze`, `Ty::is_trivially_freeze` | L1144-1180 | L1184-1220 |
| `compiler/rustc_ty_utils/src/common_traits.rs` | `is_freeze_raw` (`LangItem::Freeze`) | L25-55 | L25-55 |
| `compiler/rustc_const_eval/src/interpret/intern.rs` | `prepare_alloc`, `intern_const_alloc_recursive` (`InternKind::Static(Mutability::Not)` consulting `is_freeze`) | L82-94, L214-240 | L82-94, L215-241 |
| `compiler/rustc_const_eval/src/const_eval/machine.rs` | `retag_ptr_value` (`is_freeze` -> `CtfeProvenance::as_immutable`) | L929-964 | L929-964 |
| `compiler/rustc_codegen_llvm/src/consts.rs` | `codegen_static_item` (`alloc.mutability.is_not()` -> `llvm::set_global_constant(g, true)`) | L410-477 | L473-540 |
| `library/core/src/marker.rs` | `Send`, `Sync`, `Freeze`, `!Freeze for UnsafeCell<T>`, `marker_impls! { unsafe Freeze for PhantomData, *const, *mut, &, &mut }`, `Unpin`, `PhantomPinned`, `!Unpin for PhantomPinned` | L92, L657, L904-918, L1014-1030 | L93, L658, L905-919, L1015-1032 |
| `library/core/src/cell.rs` | `#[lang = "unsafe_cell"] pub struct UnsafeCell`, `impl !Sync` for `Cell`, `RefCell`, `UnsafeCell` | L325, L1439, L2319-2328 | L330, L1444, L2309-2318 |
| `library/core/src/pin.rs` | `#[fundamental] pub struct Pin<Ptr>` | L1088-1092 | L1087-1091 |
| `library/alloc/src/boxed.rs` | `#[fundamental] pub struct Box<T, A>` | L228-234 | L302-308 |
| `library/alloc/src/rc.rs` / `library/alloc/src/rcs/rc.rs` | `pub struct Rc`, `impl !Send for Rc`, `impl !Sync for Rc` | `rc.rs` L320-335 | `rcs/rc.rs` L325-346 |

#### `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)

- `trusted/rustc-capture/src/driver.rs` L25 (`COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"`, verified `rust-lang/rust` commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and L75-84 (`Callbacks::after_analysis`).
- `trusted/lean/Trusted/MirAst.lean` L75-92 (`noncomputable` convention preventing `._unsafe_rec`), L304-321 (`MirTy` region erasure and fail-closed `.unsupported`), L469-475 (`ProjectionElem.unsupported` covering `OpaqueCast`).
- `trusted/lean/Trusted/MirSemantics.lean` L49-52 (`FaultKind.unsupported` / `FaultKind.undefined`).

#### `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`) and `rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`)

- `rust-lang/reference`: `src/items/implementations.md` (L143-175), `src/special-types-and-traits.md` (L19-24, L37-49, L137-184), `src/types/impl-trait.md` (L60-99), `src/types/trait-object.md` (L1-88), `src/interior-mutability.md` (L1-29).
- Historical design context in `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/1023-rebalancing-coherence.md`, `text/1210-impl-specialization.md`, `text/1522-conservative-impl-trait.md`, `text/1951-expand-impl-trait.md`, `text/2451-re-rebalancing-coherence.md`.

### 2. Preserved Package Support Artifacts

1. **`support/probe_auto_traits_orphan_spec.py`:** Self-contained Python 3 standard-library probe script that compiles an independent upstream `foreign_tr` rlib, compiles and runs all 18 core test cases across Parts A–D plus 8 supplementary discriminators using live `rustc`, inspects emitted ELF object sections and symbol bindings via `readelf -S -W` and `readelf -s -W`, and scrubs host-specific temporary/sysroot paths before writing JSON.
2. **`support/probe_results.json`:** Exact machine-recorded execution output captured on `2026-11-22T08:09:13Z` under `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (LLVM `22.1.6`) and `GNU readelf (GNU Binutils for Debian) 2.47` (`core_case_count = 18`, zero host-path leaks).
3. **`support/AutoTraitsOrphanAndSpecializationSoundness.lean`:** 960-line standalone Lean `v4.34.1` formalization containing all 23 kernel-checked theorems (`freeze_implies_no_unsafe_cell`, `orphan_check_prevents_cross_crate_overlap`, `lifetime_free_specialization_commutes_with_erasure`, `ce1_lifetime_specialization_unsound_after_region_erasure`, `ce1b_equal_lifetime_specialization_unsound_after_region_erasure`, `ce2_non_fundamental_wrapper_orphan_conflict`, `ce3_marker_trait_with_assoc_const_ambiguous_dispatch`, and 16 supporting/witness theorems). Verified with exit code `0`, `0` warnings, `0` `Classical.choice` / `sorryAx` / `Lean.ofReduceBool` axioms, `0` `._unsafe_rec`, and `0` `partial`/`unsafe` declarations across all 712 local environment declarations.

## Revalidation

To cheaply verify whether these findings still hold on a newer `rustc` nightly, alternative target, or newer Lean 4 toolchain:

### 1. Re-run the Live `rustc` + `readelf` Probe Suite (~4 seconds)

From the package directory:

```bash
python3 support/probe_auto_traits_orphan_spec.py --out /tmp/probe_reval.json
```

Verify the key invariants against `support/probe_results.json`:
- Part A: `rpit_leaks_send_sync_unpin_for_u32` and `rpit_send_not_sync_for_cell` exit `0`; `rpit_blocks_send_for_rc`, `rpit_blocks_sync_for_cell`, `rpit_blocks_unpin_for_phantom_pinned`, and `dyn_trait_does_not_leak_send` fail with `E0277`.
- Part B: `fundamental_box_ref_pin_local_allowed` prints `FUND_OK=11,22,32,43`; `Vec<Local>` and `Option<Local>` fail `E0117`; `Box<T>` fails `E0210`; supplementary `unsafe impl Send for Box<Local>` fails `E0321`.
- Part C: concrete `min_specialization` prints `SPEC=generic,u32`; `'static`-bound and equal-lifetime specializations fail `E0119` (while supplementary `&'static u8`, `(T, T)`, and `T: Clone` fail Layer-2 `min_specialization` diagnostics); `#[marker]` overlapping blanket impls print `MARKER_OVERLAP=ok`; `#[marker]` with `const X` fails `E0714`.
- Part D: `impl !Send for NoSend` blocks `Send` (`E0277`); `with_negative_coherence` admits both `NEG_COH=1,2` and `RC_NEG_COH=1,2` (whereas omitting `with_negative_coherence` on `Rc<T>` fails `E0119`); `readelf` reports `FROZEN_STAT` and `PHANTOM_FREEZE_STAT` in `.rodata.*` (`PROGBITS`, `A`), `UNFROZEN_STAT` in `.data.UNFROZEN_STAT` (`PROGBITS`, `WA`), and `ZERO_UNFROZEN_STAT` in `.bss.ZERO_UNFROZEN_STAT` (`NOBITS`, `WA`).

### 2. Re-verify the Lean `v4.34.1` Formalization & Axiom/Codegen Audit (~3 seconds)

```bash
export LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1"
"$LEAN_SYSROOT/bin/lean" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/AutoTraitsOrphanAndSpecializationSoundness.lean
```

To re-confirm axiom purity and zero `._unsafe_rec` synthesis, append `#print axioms <thm>` for each theorem in a temporary scratch copy under `/tmp` and confirm every theorem prints either `does not depend on any axioms` or `depends on axioms: [propext]`.

### 3. Narrow Upstream Source Diffs

When `rust-lang/rust` advances past `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, diff only the six decision-bearing regions before assuming continuity:
1. `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs` (`assemble_candidates_from_auto_impls`, `assemble_candidates_from_object_ty`) and `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs` (`consider_auto_trait_candidate*`).
2. `compiler/rustc_next_trait_solver/src/coherence.rs` (`orphan_check_trait_ref`, `OrphanChecker::visit_ty`) and `compiler/rustc_hir_analysis/src/coherence/orphan.rs` (`orphan_check_impl`).
3. `compiler/rustc_trait_selection/src/traits/specialize/mod.rs` (`specializes`) and `compiler/rustc_hir_analysis/src/impl_wf_check/min_specialization.rs` (`check_always_applicable`).
4. `compiler/rustc_middle/src/ty/mod.rs` (`impls_are_allowed_to_overlap`) and `compiler/rustc_hir_analysis/src/check/wfcheck.rs` (`check_trait` `E0714`).
5. `compiler/rustc_trait_selection/src/traits/coherence.rs` (`overlap`, `impl_intersection_has_negative_obligation`, `try_prove_negated_where_clause`).
6. `compiler/rustc_const_eval/src/interpret/intern.rs` (`intern_const_alloc_recursive`) and `compiler/rustc_codegen_llvm/src/consts.rs` (`codegen_static_item`).
