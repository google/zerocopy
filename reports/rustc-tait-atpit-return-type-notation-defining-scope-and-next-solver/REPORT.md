# `rustc` Opaque Types (`TAIT` `#[define_opaque]`, `ATPIT`, and `RTN`): Explicit Defining-Scope Bijectivity, Three-Phase Visibility & Layout Transparency, and `-Z next-solver` Divergences

## Summary

In `rustc` across `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), and upstream `HEAD` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), opaque types—return-position `impl Trait` (`RPIT`), return-position `impl Trait` in traits (`RPITIT`), type-alias `impl Trait` (`TAIT`, `#![feature(type_alias_impl_trait)]`), and `impl Trait` in associated types (`ATPIT`, `#![feature(impl_trait_in_assoc_type)]`)—obey a strict separation between **defining-scope authorization**, **higher-order pattern bijectivity**, and a **three-phase visibility regime** whose internal representation has superseded the historical two-variant `Reveal::{UserFacing, All}` flag with the exhaustive `TypingMode` state machine (`compiler/rustc_type_ir/src/infer_ctxt.rs`).

Seven core technical invariants govern compiler soundness, cross-solver compatibility, and verified MIR capture:

1. **Explicit `#[define_opaque(...)]` Authorization and Unconstrained Checks**: By default, `OpaqueTypeCollector` (`compiler/rustc_ty_utils/src/opaque_types.rs`) collects only `RPIT` and `async fn` opaque types for free functions (`CollectionMode::RpitAndAsyncFnOnly`) and same-`impl` final `ATPIT` opaques for trait-impl methods and associated constants (`CollectionMode::ImplTraitInAssocTypes`). Free functions attempting to define a `TAIT` without `#[define_opaque(Hidden)]` treat the alias as rigid (`IsRigid::Yes`) and fail with `E0308` plus an `unconstrained opaque type` diagnostic. Conversely, annotating an item with `#[define_opaque(Hidden)]` without actually constraining `Hidden` fails with the unnumbered diagnostic `item does not constrain Hidden::{opaque#0}`, and attaching an explicit `#[define_opaque(...)]` (including empty `#[define_opaque()]`) resets the collector's mode to `RpitAndAsyncFnOnly`, suppressing implicit `ATPIT` capture.
2. **Higher-Order Pattern Bijectivity and Exception Boundaries**: Every defining use of a parameterized opaque type `GenOpaque<A_0, ..., A_{k-1}>` must pass pairwise-distinct universal generic parameters (`opaque_type_has_defining_use_args`, `compiler/rustc_trait_selection/src/opaque_types.rs`) so that `ReverseMapper` (`compiler/rustc_middle/src/ty/opaque_types.rs`) can uniquely invert caller generic parameters back to declaration-site parameters. One explicit semantic exception exists: duplicate lifetime parameters (or `'static`) are permitted when the opaque's own explicit or implied bounds force those lifetimes to be mutually equal (`LazyOpaqueTyEnv::params_equal` / `param_equal_static`), as verified live on `EqLt<'a: 'b, 'b: 'a>` instantiated as `EqLt<'x, 'x>`.
3. **Genuine Acceptance-vs.-Rejection and Diagnostic Divergences Between `-Z next-solver=globally` and `-Z next-solver=no`**:
   - **Coexisting defining and non-defining uses (`tait_12`)**: Under `-Z next-solver=globally`, `FnCtxt::compute_definition_site_hidden_types` (`compiler/rustc_hir_typeck/src/opaque_types.rs`) classifies non-universal instantiations (such as `GenOpaque<u32>`) as `UsageKind::NonDefiningUse` and accepts them whenever another defining use (such as `GenOpaque<T>`) exists in the same body (`rc = 0`, executes cleanly natively and under `Miri -Zmiri-tree-borrows`). Under `-Z next-solver=no`, `WritebackCtxt::visit_opaque_types` (`compiler/rustc_hir_typeck/src/writeback.rs`) eagerly rejects every non-defining use with `E0792` (`rc = 1`).
   - **Lone non-defining or duplicate-parameter uses (`tait_10`, `tait_11`)**: Both solvers reject, but `-Z next-solver=globally` reports unnumbered `item does not constrain ...` with a secondary note (`does not have unique universal generic arguments`), whereas `-Z next-solver=no` emits `E0792` (`expected generic type parameter, found u32`) for non-parameter arguments and unnumbered `non-defining opaque type use in defining scope` (`type used multiple times`) for duplicate parameters.
   - **Self-referential cyclic opaques (`tait_08`: `Rec = (u32, Option<Box<Rec>>)` )**: Under `-Z next-solver=no`, both `1.98.0-nightly` and `1.102.0-nightly` detect the cycle via `HasRecursiveOpaque` in `writeback.rs` and emit `E0720` (`cannot resolve opaque type`). Under `-Z next-solver=globally`, behavior diverges across compiler versions: `1.98.0-nightly` (`14210df0e`) hits `UsageKind::UnconstrainedHiddenType` (`E0282: type annotations needed`), whereas `1.102.0-nightly` (`3ef0c22cd`)—after the `normalizes_to -> project_goals` and `deeply_resolve_ignoring_regions` refactor—unrolls the recursive `AliasRelate` expansion to default `recursion_limit = 128` and emits `E0275` (`overflow assigning (u32, Option<Box<...>>)`).
4. **Three-Phase Visibility Split (`TypingMode` Replacement of `Reveal`)**:
   - **Phase 1 — User-facing rigidity** (`TypingMode::Typeck` outside defining scope, historically `Reveal::UserFacing`): Non-defined opaques are rigid; concrete trait implementations (`Add<u32>` -> `E0369`, indexing `s[0]` -> `E0608`) and concrete type equalities are hidden.
   - **Phase 2 — Auto-trait leakage without witness leakage**: Outside defining scopes, `Send`, `Sync`, and `Unpin` leak through the hidden witness (`consider_auto_trait_candidate_for_opaque_ty`, `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs`; `assemble_candidates_from_auto_trait`, `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs`), accepting `u64` (`Send + Sync + Unpin`) and rejecting `Rc<u32>` (`E0277`), guarded by an explicit `var_values_is_identity == IsIdentity::No` anti-leakage check that forces ambiguity rather than constraining caller inference variables.
   - **Phase 3 — Post-analysis layout and ABI transparency** (`TypingMode::PostAnalysis` and `TypingMode::Codegen`, historically `Reveal::All`): `layout_of` (`compiler/rustc_ty_utils/src/layout.rs`) unconditionally upgrades any earlier `TypingMode` via `with_post_analysis_normalized_invalidating_rigid_aliases` (`compiler/rustc_middle/src/ty/mod.rs`), revealing exact concrete `size_of`, `align_of`, and ABI layout to CTFE, MIR monomorphization, and codegen across crate boundaries (`libdep.rlib` exporting `Secret = [u64; 3]` exposes `SIZE=24, ALIGN=8` while still rejecting `s[0]` with `E0608`). Between `1.98.0-nightly` and `1.102.0-nightly`/`HEAD`, `rustc` split `TypingMode::Codegen` out of `TypingMode::PostAnalysis` so that `ty::Coroutine` layouts return `Err(LayoutError::TooGeneric)` in `PostAnalysis` and are revealed only in `Codegen`, whereas non-coroutine opaque types remain layout-transparent in `PostAnalysis`.
5. **RTN (`return_type_notation`) Lowering**: Both trait-bound (`W: Worker<run(..): Send>`) and type-qualified where-clause (`where W::run(..): Send` / `where <W as Worker>::run(..): Send`) forms converge in `lower_return_type_notation_ty` (`compiler/rustc_hir_analysis/src/hir_ty_lowering/bounds.rs`), which converts method lifetime parameters into late-bound regions, rejects method type/const parameters (`ReturnTypeNotationIllegalParam`), rejects equality bounds (`ReturnTypeNotationEqualityBound`), requires the method return type to be an RPITIT synthetic projection (`tcx.is_impl_trait_in_trait`), and emits a `ty::AliasTy` projection bound whose auto-trait check inspects every captured upvar and every local held across `.await` in the lowered coroutine witness.
6. **Anneal Trusted-Boundary Relevance (`joshlf/anneal@c131b320e`)**: At `c131b320eeeb26ef692e5afd5ec8db49ee518613`, Anneal pins `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` in `trusted/rustc-capture/src/driver.rs` and deliberately excludes opaque projections (`ProjectionElem::OpaqueCast`) and coroutine types (`TyKind::Coroutine`, `TyKind::CoroutineWitness`, `TyKind::CoroutineClosure`) from `trusted/lean/Trusted/MirAst.lean`. Extending `after_analysis` MIR capture to support TAIT/ATPIT/RPITIT/RTN requires normalizing captured types strictly under `TypingEnv::post_analysis` / `TypingEnv::fully_monomorphized` (`TypingMode::Codegen` for coroutines) and treating `TypingMode` rigidity boundaries as sound abstractions of post-erasure MIR semantics.
7. **Mechanized Soundness and Sharpness (`Lean v4.34.1`)**: A 2,107-LOC standalone formalization (`support/OpaqueTypeDefiningScopeAndRevealSoundness.lean`) kernel-checks under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, and `0` `._unsafe_rec` constants across all 677 compiled constants in `env.constants.map₁`. It proves witness uniqueness (`coherentDefiningUses_unique_concrete_witness`, zero axioms), three-tier entailment monotonicity (`userFacing_refines_revealAll`, `[propext]`), exact auto-trait leakage soundness (`autoTrait_leakage_sound_iff_witness`, `[propext]`), and four constructive sharpness counterexamples (`ce1`–`ce4`).

## Applicability

This report characterizes the interaction among seven durable upstream subjects identified in `REPORT.json`:

1. **Primary compiler source (`rust-lang/rust` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, `2026-11-22`)**: Audited directly for exact HIR lowering, defining-scope collection, old/new trait solver opaque normalization, borrowck member constraints, auto-trait leakage, `TypingMode`/`TypingEnv` state transitions, and `layout_of` transparency.
2. **Executed nightly toolchain (`rust-lang/rust` `1.98.0-nightly` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `2026-05-31`, `LLVM 22.1.6`, `Miri 0.1.0`, `x86_64-unknown-linux-gnu`)**: Both audited in source and executed live across 22 single- and two-crate test cases under both `-Z next-solver=globally` and `-Z next-solver=no` (`--edition=2024`), plus 15 live `cargo miri run` executions under `-Zmiri-tree-borrows` (`support/probe_tait_atpit_rtn_and_next_solver.py`, `support/probe_results_1_98_nightly.json`).
3. **Comparison nightly toolchain (`rust-lang/rust` `1.102.0-nightly` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`, `LLVM 23.1.5`, `x86_64-unknown-linux-gnu`)**: Audited directly in source and compared 1:1 across 14 shared test cases recorded in `support/baseline_1_102_nightly.json` under both `-Z next-solver=globally` and `-Z next-solver=no`.
4. **Anneal pinned compiler (`rust-lang/rust` `1.98.0-nightly` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-30`)** and **Anneal verification framework (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `2026-11-19`)**: Inspected to ground how `trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, and `trusted/audit/TrustedBoundary.lean` currently gate opaque/coroutine MIR features and Lean purity.
5. **Normative language specification (`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `2026-11-17`)**: Inspected for normative stable `impl Trait`, `RPITIT`, and `use<..>` capture rules, noting where unstable features (`type_alias_impl_trait`, `impl_trait_in_assoc_type`, `return_type_notation`) extend beyond the stable Reference.
6. **Proof checker (`leanprover/lean4` `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`)**: Used to kernel-check `support/OpaqueTypeDefiningScopeAndRevealSoundness.lean` and audit its compiled `.olean` environment (`env.constants.map₁`).

### Version Scope Matrix (Shared vs. Version-Specific Behavior)

| Architectural Aspect | `1.98.0-nightly` (`14210df0e`) | `1.102.0-nightly` (`3ef0c22cd`) | `HEAD` (`342d74463`) | Shared or Version-Specific |
| :--- | :--- | :--- | :--- | :--- |
| `TypingMode` variants (`compiler/rustc_type_ir/src/infer_ctxt.rs`) | `Coherence`, `Analysis`, `Borrowck`, `PostBorrowckAnalysis`, `PostAnalysis`, `ErasedNotCoherence` | `Coherence`, `Typeck`, `PostTypeckThroughBorrowck`, `PostBorrowck`, `Reflection`, `PostAnalysis`, `Codegen`, `ErasedNotCoherence` | Identical to `1.102.0-nightly` | **Version-specific** (split `Codegen` from `PostAnalysis`, renamed analysis/borrowck modes, added `Reflection`) |
| Next-solver opaque normalization module path | `compiler/rustc_next_trait_solver/src/solve/normalizes_to/opaque_types.rs` (`NormalizesTo`) | `compiler/rustc_next_trait_solver/src/solve/project_goals/opaque_types.rs` (`ProjectionClause` + `ty::IsRigid`) | Byte-for-byte identical to `1.102.0-nightly` | **Version-specific** (path and predicate refactor between `1.98` and `1.102`) |
| `FnCtxt::compute_definition_site_hidden_types` resolution call | `self.resolve_vars_if_possible(*entry)` | `self.deeply_resolve_ignoring_regions(*entry)` + `E0282` hidden-type note | Byte-for-byte identical to `1.102.0-nightly` | **Version-specific** |
| Self-referential `Option<Box<Rec>>` (`tait_08`) under `-Z next-solver=globally` | `E0282` (`type annotations needed`) | `E0275` (`overflow assigning (u32, Option<Box<...>>)` at recursion limit 128) | Same code path as `1.102.0-nightly` (source identical; binary not executed at `HEAD`) | **Version-specific** (`E0282` vs. `E0275`); both reject |
| Self-referential `Option<Box<Rec>>` (`tait_08`) under `-Z next-solver=no` | `E0720` (`cannot resolve opaque type`) | `E0720` (`cannot resolve opaque type`) | Identical `HasRecursiveOpaque` visitor in `writeback.rs` | **Shared** |
| Unmarked definer (`E0308`), unconstrained `#[define_opaque]`, conflicting definers, auto-trait leakage (`E0277`), non-defining concrete op (`E0369`), `GenOpaque<u32>` (`item does not constrain` vs. `E0792`), `ATPIT`, `RTN` | Verified by live source + execution | Verified by live source + execution (14 cases) | Verified by live source (exact code parity with `1.102.0-nightly` on audited opaque modules) | **Shared** across all three revisions |

### Feature Flags and Invocation Modes

All empirical compiler observations require nightly feature gates (`#![feature(type_alias_impl_trait)]`, `#![feature(impl_trait_in_assoc_type)]`, and `#![feature(return_type_notation)]`), `--edition=2024`, and explicit solver flags `-Z next-solver=globally` or `-Z next-solver=no` on `x86_64-unknown-linux-gnu`. Claims about `HEAD` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`) execution behavior are **derived** from byte-for-byte source equality with `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) on `compiler/rustc_hir_typeck/src/opaque_types.rs` and `compiler/rustc_next_trait_solver/src/solve/project_goals/opaque_types.rs`, not from executing a compiled `HEAD` binary. Claims about `joshlf/anneal`'s pinned `1.98.0-nightly` (`f8a08b688`, dated one day prior to executed `14210df0e`) apply to its verified `MirAst.lean` and `driver.rs` gates and are not inferred to have identical `rustc` diagnostics without rerunning `support/probe_tait_atpit_rtn_and_next_solver.py` against `f8a08b688`.

## Findings

### 1. Explicit Defining-Scope Collection (`#[define_opaque]`, `ATPIT`, and `RPIT`/`RPITIT`)

Basis: normative + source + execution

#### 1.1 Normative Baseline vs. Unstable Extensions

In the stable Rust Reference (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/types/impl-trait.md:68-173` and `src/items/type-aliases.md:12-43`), `impl Trait` in abstract (existential) position is restricted to return types of non-`extern` free/inherent functions (`RPIT`) and trait methods (`RPITIT`), where every return path in the owning body must resolve to a single concrete hidden type (`r[type.impl-trait.return.constraint-body]`) and every `impl Trait` return type in a trait method desugars to an anonymous associated type (`r[type.impl-trait.return-in-trait.desugaring]`). Stable Rust explicitly forbids `impl Trait` inside `type` aliases (`r[type.impl-trait.constraint]`).

The unstable `type_alias_impl_trait` (`TAIT`) and `impl_trait_in_assoc_type` (`ATPIT`) features lift this restriction by separating **where an opaque type is declared** (a free `type Alias = impl Trait;` or trait-impl `type Assoc = impl Trait;`) from **which item bodies are authorized to constrain its hidden concrete witness**.

#### 1.2 `OpaqueTypeCollector` and `CollectionMode` Dispatch

The authoritative compiler query determining which opaque types an item may define is `opaque_types_defined_by` in `compiler/rustc_ty_utils/src/opaque_types.rs:314-383` (at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`; structurally equivalent at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65:300-370` apart from `super::sig_types::walk_types` -> `rustc_ty_walk::walk_types`). Every closure, coroutine, inline non-type-system const, or `SyntheticCoroutineBody` (`tcx.is_typeck_child(item)`) inherits its parent's defining set (`opaque_types.rs:322-324`), while delegated signatures (`hir_opt_delegation_sig_id`) define no opaques (`opaque_types.rs:327-329`).

For all other items, `OpaqueTypeCollector::new` selects an initial `CollectionMode` solely from the item's `DefKind` (`opaque_types.rs:30-50`):

```rust
enum CollectionMode {
    /// For impl trait in assoc types we only permit collecting them from
    /// associated types of the same impl block.
    ImplTraitInAssocTypes,
    /// When collecting for an explicit `#[define_opaque]` attribute, find all TAITs
    Taits,
    /// By default collect RPITs and async function return types defined by this item
    RpitAndAsyncFnOnly,
}

fn new(tcx: TyCtxt<'tcx>, item: LocalDefId) -> Self {
    let mode = match tcx.def_kind(item) {
        DefKind::AssocConst | DefKind::AssocFn | DefKind::AssocTy => {
            CollectionMode::ImplTraitInAssocTypes
        }
        DefKind::TyAlias => CollectionMode::Taits,
        _ => CollectionMode::RpitAndAsyncFnOnly,
    };
    ...
}
```

Next, `opaque_types_defined_by` runs three collection phases in order (`opaque_types.rs:333-351`):

1. **Explicit `#[define_opaque(...)]` walk (`collect_taits_from_defines_attr`, lines 175–196)**: Reads `tcx.hir_attr_map(hir_id.owner).define_opaque`. For each listed item `(span, define)`, it temporarily replaces `self.mode` with `CollectionMode::Taits`, calls `rustc_ty_walk::walk_types(self.tcx, define, self)`, and emits `"item does not contain any opaque types"` if no new opaques were collected. Crucially, once the attribute loop finishes, line 195 unconditionally sets `self.mode = CollectionMode::RpitAndAsyncFnOnly`. This allows an engineer to place an empty `#[define_opaque()]` on a trait-impl method or type alias to suppress implicit `ATPIT` or nested-`TAIT` capture when the method merely *uses* the associated type without defining it.
2. **Signature type walk (`rustc_ty_walk::walk_types`, line 335)**: Walks the item's own signature types under `self.mode`. In `visit_opaque_ty` (lines 94–128):
   - `OpaqueTyOrigin::FnReturn` and `OpaqueTyOrigin::AsyncFn` are always collected.
   - `OpaqueTyOrigin::TyAlias { in_assoc_ty, .. }` is filtered strictly by `self.mode`:
     - `ImplTraitInAssocTypes`: accepts ONLY `in_assoc_ty == true` (rejecting free `TAIT`s).
     - `Taits`: accepts ONLY `in_assoc_ty == false` (rejecting `ATPIT`s, which can only be defined by items of the same `impl`).
     - `RpitAndAsyncFnOnly`: rejects all `TyAlias` opaques (both `TAIT` and `ATPIT`).
   - When walking a `ty::Projection` (`Self::AssocTy`, lines 230–280), if the current item belongs to a trait `impl` (`tcx.trait_impl_of_assoc`) whose `impl_trait_ref` matches `alias_ty.trait_ref(tcx)` and the associated type is final (`assoc.defaultness(tcx).is_final()`, preventing unsound capture of specializable defaults), `OpaqueTypeCollector` rebases the projection arguments onto the `impl`'s identity generics and visits `tcx.type_of(assoc.def_id)` to discover the `ATPIT` opaque.
   - For default trait methods returning an `RPITIT` (lines 281–307), it checks `tcx.opt_rpitit_info(alias_def_id)` and extracts the synthetic associated type's underlying `ty::Opaque`.
3. **Body-local `TAIT` declarations (`collect_taits_declared_in_body`, lines 66–91, 337–351)**: For bodies (`Fn`, `AssocFn`, `Static`, `Const`, `AssocConst`, `AnonConst`), a nested HIR visitor collects any `type` alias declared *inside* the body itself so body-local TAITs do not require external attributes.

#### 1.3 Why Unmarked Definers Fail `E0308` While Unconstrained `#[define_opaque]` Fails Separate Checks

The interaction between `opaque_types_defined_by` and `find_opaque_ty_constraints_for_tait` (`compiler/rustc_hir_analysis/src/collect/type_of/opaque.rs:75-99`) produces two distinct, complementary rejection paths—verified identically across both solvers and both `1.98.0-nightly` and `1.102.0-nightly`:

- **Unmarked definer (`tait_02_missing_define_opaque_rejected`)**:
  ```rust
  #![feature(type_alias_impl_trait)]
  pub type Hidden = impl Copy;
  pub fn unmarked_definer() -> Hidden { 42u32 }
  ```
  Because `unmarked_definer` lacks `#[define_opaque(Hidden)]`, `opaque_types_defined_by(unmarked_definer)` returns `[]`. During type checking, `can_define_opaque_ty(Hidden)` is `false` (old solver: `compiler/rustc_infer/src/infer/opaque_types/mod.rs:134-136`) and `defining_opaque_types.contains(&Hidden)` is `false` (next solver: `project_goals/opaque_types.rs:45-56`), so `Hidden` is treated as rigid (`ty::IsRigid::Yes`). Equating the return expression `42u32` with rigid `Hidden` fails with **`error[E0308]: mismatched types`** (accompanied by a diagnostic note: `this item must have a #[define_opaque(Hidden)] attribute to be able to define hidden types`). Subsequently, `find_opaque_ty_constraints_for_tait` walks the crate (`TaitConstraintLocator`, `collect/type_of/opaque.rs:80-98`), finds no defining item (`locator.found == None`), and emits **`error: unconstrained opaque type`** (`Hidden must be used in combination with a concrete type within the same crate`).
- **Annotated non-constrainer (`tait_03_unconstrained_define_opaque_rejected`)**:
  ```rust
  #![feature(type_alias_impl_trait)]
  pub type Hidden = impl Copy;
  #[define_opaque(Hidden)]
  pub fn claims_to_define_but_does_not() -> u32 { 7 }
  ```
  Here `opaque_types_defined_by` returns `[Hidden]`, so the compiler expects `claims_to_define_but_does_not` to produce a defining use of `Hidden`.
  - Under `-Z next-solver=globally`, `FnCtxt::compute_definition_site_hidden_types` (`compiler/rustc_hir_typeck/src/opaque_types.rs:163-174`) ends with `usage_kind == UsageKind::None` and immediately calls `report_item_does_not_constrain_error` (`compiler/rustc_trait_selection/src/opaque_types.rs:213-235`).
  - Under `-Z next-solver=no`, `typeck` produces an empty `hidden_types` entry for `Hidden`, so `TaitConstraintLocator::check` (`collect/type_of/opaque.rs:180-198`) invokes `non_defining_use_in_defining_scope` (lines 130–137), which calls the same `report_item_does_not_constrain_error`.
  - Both paths emit the unnumbered error **`error: item does not constrain Hidden::{opaque#0}`** with note `consider removing #[define_opaque] or adding an empty #[define_opaque()]`.
- **Conflicting concrete witnesses (`tait_04_conflicting_concrete_witnesses_rejected`)**:
  When `def_u32() -> Hidden { 1u32 }` and `def_u64() -> Hidden { 2u64 }` both carry `#[define_opaque(Hidden)]`, `TaitConstraintLocator::insert_found` (`collect/type_of/opaque.rs:118-128`)—and `add_hidden_type` during borrowck (`compiler/rustc_borrowck/src/region_infer/opaque_types/mod.rs:157-180`)—compares remapped declaration-site hidden types (`hidden_ty.ty != prev.ty`) and rejects with **`error: concrete type differs from previous defining opaque type use`** (`expected u32, got u64`).

### 2. Higher-Order Pattern Bijectivity, `ReverseMapper`, and `-Z next-solver` Divergences

Basis: source + execution + derived

#### 2.1 Why Bijective Generic Parameters Are Required (`opaque_type_has_defining_use_args` & `ReverseMapper`)

A parameterized opaque type `type GenPair<A, B> = impl Copy;` defines a single crate-global type function $\mathrm{GenPair} : (A, B) \mapsto W(A, B)$ whose hidden witness $W$ may depend only on the declaration parameters $(A, B)$. Inferring $W$ from a defining-use equation $\mathrm{GenPair}\langle t_0, \dots, t_{k-1}\rangle = R$ is a higher-order unification problem, which is undecidable and non-unique in general unless restricted to Miller's higher-order pattern fragment: every captured argument $t_i$ must be a distinct universal generic parameter, and every caller generic parameter occurring in $R$ must lie in $\{t_0, \dots, t_{k-1}\}$.

`rustc` enforces these two halves in separate, tightly coupled passes:

1. **Forward injectivity & universality (`opaque_type_has_defining_use_args`, `compiler/rustc_trait_selection/src/opaque_types.rs:66-126`)**:
   Iterates over `opaque_type_key.iter_captured_args(tcx)`:
   - For `GenericArgKind::Type(ty)`: requires `matches!(ty.kind(), ty::Param(_))` (line 96).
   - For `GenericArgKind::Const(ct)`: requires `matches!(ct.kind(), ty::ConstKind::Param(_))` (line 97).
   - For `GenericArgKind::Lifetime(lt)`: skipped during `DefiningScopeKind::HirTypeck` (line 90), and checked during `DefiningScopeKind::MirBorrowck` (lines 91–94) to require `ReEarlyParam(_) | ReLateParam(_)` OR `(lt.is_static() && opaque_env.param_equal_static(i))`.
   - Any non-parameter argument returns `Err(NonDefiningUseReason::NotAParam { .. })` (line 111).
   - Duplicate parameters are tracked in `seen_params: FxIndexMap<GenericArg, Vec<usize>>` (lines 100–123), returning `Err(NonDefiningUseReason::DuplicateParam { .. })` whenever `param_indices.len() > 1`—*except* when `opaque_env.params_equal(i, prev_i)` holds.
2. **Semantic lifetime-equality exception (`LazyOpaqueTyEnv`, `compiler/rustc_trait_selection/src/opaque_types.rs:128-211`)**:
   If the opaque's own explicit or implied bounds force two lifetime parameters to be mutually outliving (`'a: 'b` and `'b: 'a`) or equal to `'static` (`'a: 'static`), `LazyOpaqueTyEnv::get_canonical_args` canonicalizes equivalent universal regions via `OutlivesEnvironment::free_region_map().sub_free_regions` so that `params_equal(i, prev_i)` returns `true`. Live probe `tait_14_lifetime_equality_exception_accepted` confirms that:
   ```rust
   pub type EqLt<'a: 'b, 'b: 'a> = impl Copy + use<'a, 'b>;
   #[define_opaque(EqLt)]
   pub fn make_eq<'x>(r: &'x u32) -> EqLt<'x, 'x> { r }
   ```
   compiles and runs identically (`EQLT_SIZE=8`) under both `-Z next-solver=globally` and `-Z next-solver=no` as well as under `Miri -Zmiri-tree-borrows`.
3. **Reverse parameter mapping (`ReverseMapper`, `compiler/rustc_middle/src/ty/opaque_types.rs:16-216`)**:
   Once `opaque_type_has_defining_use_args` succeeds, `ProvisionalHiddenType::remap_generic_params_to_declaration_params` folds the concrete RHS with `ReverseMapper`, replacing each caller parameter `p` with the corresponding opaque declaration parameter `map[p]`.
   - If the hidden type mentions a caller type parameter (`fold_ty`, lines 163–186), const parameter (`fold_const`, lines 192–215), or non-closure lifetime (`fold_region`, lines 123–143) not present in `map`, `ReverseMapper` emits a hard error (`type parameter ... is part of concrete type but not used in parameter list`, `ConstNotUsedTraitAlias`, or `non-defining opaque type use in defining scope`).
   - **Notable closure/coroutine region quirk (`fold_closure_args`, lines 49–88)**: Because closure and coroutine `GenericArgs` carry all parent function lifetimes even when unused by the closure body, `ReverseMapper` sets `do_not_error = true` on `index < generics.parent_count` and replaces unmapped parent regions with `tcx.lifetimes.re_static` (line 126). Similarly, `ToArgRegionsFolder` in borrowck (`compiler/rustc_borrowck/src/region_infer/opaque_types/mod.rs:412-520`) sets `erase_unknown_regions = true` on closure/coroutine parent arguments and bivariant alias arguments, erasing unknown regions to `re_erased` (existential regions).
   - Unused captured lifetimes that *are* in the opaque's parameter list (`type WithLt<'a> = impl Copy + use<'a>; fn make<'a>(_x: &'a u8) -> WithLt<'a> { 123u32 }`, `tait_09`) are always legal because `ReverseMapper` requires only $\mathrm{FV}(R) \subseteq \mathrm{Im}(\mathrm{fwd})$, not surjectivity onto all captured parameters.

#### 2.2 Detailed Anatomy of `-Z next-solver=globally` vs. `-Z next-solver=no` Divergences

Our primary-source audit and 22-case live differential campaign uncovered **four concrete divergences** between `-Z next-solver=globally` and `-Z next-solver=no`—including **one genuine compilation accept-vs.-reject divergence** (`tait_12`) and **one cross-version diagnostic divergence** (`tait_08` between `1.98.0-nightly` and `1.102.0-nightly`):

| Case | Code Pattern | `-Z next-solver=no` (`1.98` & `1.102`) | `-Z next-solver=globally` (`1.98.0-nightly`, `14210df0e`) | `-Z next-solver=globally` (`1.102.0-nightly`, `3ef0c22cd`) | Root Mechanism in Source |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`tait_12`** | `fn define_and_reuse<T: Copy>(x: T) -> (GenOpaque<T>, GenOpaque<u32>) { (x, 7u32) }` | **REJECT (`rc=1`)**: `E0792` (`expected generic type parameter, found u32`) | **ACCEPT (`rc=0`)**: native `SIZES=2,4`, Miri `rc=0` `SIZES=2,4` | Not in 14-case baseline (`source` identical to `1.98` accept logic in `opaque_types.rs:125-153`) | Old solver (`writeback.rs:595-605`) reports `err.report()` on *every* non-defining entry. Next solver (`rustc_hir_typeck/src/opaque_types.rs:125-153`) treats `GenOpaque<u32>` as `UsageKind::NonDefiningUse`, finds defining use `GenOpaque<T> := T`, then instantiates `T[u32] = u32` and validates `demand_eqtype(u32, u32)`. |
| **`tait_10`** | `fn bad_inst() -> GenOpaque<u32> { 42u32 }` | **REJECT (`rc=1`)**: `E0792` (`expected generic type parameter, found u32`) | **REJECT (`rc=1`)**: unnumbered `item does not constrain GenOpaque::{opaque#0}` + note `does not have unique universal generic arguments` | **REJECT (`rc=1`)**: identical to `1.98.0-nightly` | Next solver defers non-defining uses to `UsageKind::NonDefiningUse`; when the loop finishes with no defining use (`opaque_types.rs:175-182`), it calls `report_item_does_not_constrain_error` instead of `NonDefiningUseReason::report` (`E0792`). |
| **`tait_11`** | `fn dup_param<T: Copy>(x: T) -> GenPair<T, T> { (x, x) }` | **REJECT (`rc=1`)**: unnumbered `non-defining opaque type use in defining scope` + note `type used multiple times` | **REJECT (`rc=1`)**: unnumbered `item does not constrain GenPair::{opaque#0}` + note `does not have unique universal generic arguments` | Not in 14-case baseline (same `report_item_does_not_constrain_error` path) | Old solver calls `NonDefiningUseReason::DuplicateParam::report` (`rustc_trait_selection/src/opaque_types.rs:43-55`). Next solver maps `DuplicateParam` to `UsageKind::NonDefiningUse` and falls through to `report_item_does_not_constrain_error`. |
| **`tait_08`** | `type Rec = impl Sized; #[define_opaque(Rec)] fn make_rec(b: Option<Box<Rec>>) -> Rec { (1u32, b) }` | **REJECT (`rc=1`)**: `E0720` (`cannot resolve opaque type`) | **REJECT (`rc=1`)**: **`E0282`** (`type annotations needed` on `b: Option<Box<Rec>>`) | **REJECT (`rc=1`)**: **`E0275`** (`overflow assigning (u32, Option<Box<...>>)` at recursion limit 128) | Old solver eagerly replaces top-level `Rec` with `?0` without re-normalizing `Rec` inside `Option<Box<Rec>>`, then catches the cycle via `HasRecursiveOpaque` (`writeback.rs:635-664, 1070-1097`) -> `E0720`. Next solver lazily normalizes every occurrence of `Rec` via `register_hidden_type_in_storage` (`project_goals/opaque_types.rs:80-82`): in `1.98`, `resolve_vars_if_possible` leaves `?0` unconstrained (`UsageKind::UnconstrainedHiddenType` -> `E0282`); in `1.102`, `deeply_resolve_ignoring_regions` + `ProjectionClause` normalization unrolls `(u32, Option<Box<...>>)` until hitting `recursion_limit = 128` -> `E0275`. |

This architectural split also explains `compiler/rustc_borrowck/src/region_infer/opaque_types/mod.rs:263-281`: in borrowck's `collect_defining_uses`, non-defining uses are pushed as `DeferredOpaqueTypeError::InvalidOpaqueTypeArgs(err)` when `!tcx.use_typing_mode_post_typeck_through_borrowck()` (old solver), whereas with `TypingMode::PostTypeckThroughBorrowck` (next solver) non-defining uses are ignored during hidden-type collection and subsequently verified against the inferred declaration-site hidden type by `apply_definition_site_hidden_types` (lines 528–622).

### 3. Three-Phase Visibility Split: `TypingMode` (Replacing `Reveal`), Auto-Trait Leakage, and Cross-Crate Layout Transparency

Basis: source + execution + derived

#### 3.1 Evolution from `Reveal::{UserFacing, All}` to Exhaustive `TypingMode`

Older `rustc` designs stored a two-valued `reveal: Reveal` (`Reveal::UserFacing` vs. `Reveal::All`) inside `ParamEnv`. By `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `enum Reveal` no longer exists anywhere in `rustc_type_ir` or `rustc_middle`; it was replaced by `TypingMode<I, S>` in `compiler/rustc_type_ir/src/infer_ctxt.rs`, paired with `ParamEnv` inside `TypingEnv` (`compiler/rustc_middle/src/ty/mod.rs:1233-1380`). Between `1.98.0-nightly` and `1.102.0-nightly`/`HEAD`, `TypingMode` underwent a further refinement (marked `#[rustc_must_match_exhaustively]` at `HEAD`):

```rust
// compiler/rustc_type_ir/src/infer_ctxt.rs:71-164 @ 342d74463af7dd3018ef6aa04dd5500c2deb5bd1
#[cfg_attr(feature = "nightly", rustc_must_match_exhaustively)]
pub enum TypingMode<I: Interner, S: TypingModeErasedStatus = MayBeErased> {
    Coherence,
    Typeck { defining_opaque_types_and_generators: I::LocalDefIds },
    PostTypeckThroughBorrowck { defining_opaque_types: I::LocalDefIds },
    PostBorrowck { defined_opaque_types: I::LocalDefIds },
    Reflection,
    PostAnalysis,
    Codegen,
    ErasedNotCoherence(S),
}
```

At `1.98.0-nightly` (`14210df0e`, `infer_ctxt.rs:66-145`), the variants were `Coherence`, `Analysis`, `Borrowck`, `PostBorrowckAnalysis`, `PostAnalysis`, and `ErasedNotCoherence` (without `Reflection` or `Codegen`).

In `compiler/rustc_next_trait_solver/src/solve/project_goals/opaque_types.rs:17-182` (`HEAD` and `1.102.0-nightly`; cf. `normalizes_to/opaque_types.rs:17-174` at `1.98.0-nightly`), `EvalCtxt::normalize_opaque_type` dispatches strictly on `TypingMode`:

- **`Coherence`**: Adds item bounds on `expected` (failing only if an item bound is impossible, e.g., `impl Copy := NotCopy`) and injects `PredicateKind::Ambiguous` so coherence remains complete.
- **`Typeck { defining_opaque_types_and_generators }` / `PostTypeckThroughBorrowck { defining_opaque_types }`**: If `def_id` is NOT in the local defining set, equates `goal.predicate.term` with `opaque_ty.to_term(cx, ty::IsRigid::Yes)`—**Phase 1 opacity**. If `def_id` IS in the defining set, structurally normalizes `opaque_ty.args`, looks up or inserts `OpaqueTypeKey { def_id, args: normalized_args }` in `OpaqueTypeStorage` (`compiler/rustc_infer/src/infer/opaque_types/table.rs:12-161`), equates duplicate registrations (`expected == prev`), initializes from `type_of_opaque_hir_typeck` with fresh region vars in `PostTypeckThroughBorrowck`, and enforces `add_item_bounds_for_hidden_type`.
- **`PostBorrowck { defined_opaque_types }`**: Reveals opaques defined by the completed body via `cx.type_of(def_id)` (folding `ReErased` into fresh region vars), while keeping all other opaques rigid.
- **`Reflection | PostAnalysis | Codegen`**: Unconditionally reveals every local and remote opaque via `cx.type_of(def_id).instantiate(cx, opaque_ty.args)` and recursively normalizes—**Phase 3 transparency**.
- **`ErasedNotCoherence`**: Treats opaques as rigid during canonicalization caching, immediately triggering a rerun (`RerunReason::NormalizeOpaqueType` for local opaques; `rerun_if_in_post_analysis` for foreign opaques) so cached canonical responses never leak defining-scope or post-analysis normalization across incompatible `TypingMode`s.

In the old solver (`-Z next-solver=no`), `needs_normalization` (`compiler/rustc_trait_selection/src/traits/normalize.rs:132-152`) strips `TypeFlags::HAS_TY_OPAQUE` in `Typeck`, `PostTypeckThroughBorrowck`, and `PostBorrowck`, and `AssocTypeNormalizer` (`compiler/rustc_trait_selection/src/traits/query/normalize.rs:231-249`) expands `ty::Opaque` only in `Reflection | PostAnalysis | Codegen` (guarded by `recursion_limit`).

#### 3.2 Phase 1 (User-Facing Opacity) vs. Phase 2 (Auto-Trait Leakage)

Outside an opaque's defining scope during `Typeck`, non-auto concrete traits and type equalities are completely concealed:
- `tait_07_nondefining_concrete_equality_probe`: `h + 1u32` on `Hidden = impl Copy` (witness `u32`) fails with **`E0369: cannot add u32 to Hidden`** in both solvers and both compiler versions.
- `tait_13_cross_crate_reveal_all_layout_and_abi`: `s[0]` on `dep::Secret = impl Copy + PartialEq` (witness `[u64; 3]` exported from `libdep.rlib`) fails with **`E0608: cannot index into a value of type dep::Secret`** in both solvers.

Yet built-in auto traits (`Send`, `Sync`, `Unpin`, `Freeze`, etc.) *do* leak through the hidden witness—even across module and crate boundaries:
- **Next solver (`compiler/rustc_next_trait_solver/src/solve/trait_goals.rs:243-248, 1321-1390`)**: When `consider_auto_trait_candidate` encounters a rigid opaque (`ty::IsRigid::Yes`), it calls `consider_auto_trait_candidate_for_opaque_ty`:
  1. **Cycle-avoidance short-circuit (lines 1330–1334)**: If `item_self_bounds(def_id)` already explicitly lists the auto trait (e.g., `impl Send`), it returns `Err(NoSolution)` so the item-bound candidate wins without invoking `type_of(def_id)` (preventing fatal query cycles during mutually recursive typeck).
  2. **Witness probe (lines 1336–1343)**: Queries `hidden_ty = cx.type_of(def_id.into()).instantiate(cx, args)` and evaluates the auto-trait goal with `hidden_ty` as `Self`.
  3. **Anti-type-leakage guard (lines 1345–1349)**: Checks `if candidate.result.value.var_values_is_identity == IsIdentity::No { return self.forced_ambiguity(MaybeInfo::AMBIGUOUS); }`. Proving an auto trait on the hidden type is **forbidden** from constraining any caller inference variable, preventing callers from exfiltrating the hidden concrete type through auto-trait unification.
  4. **Opaque-storage guard (lines 1362–1387)**: If proving the auto trait registered any new defining opaque uses during `TypingMode::Typeck`, forces ambiguity (`MaybeInfo::AMBIGUOUS`); new region-only registrations are permitted only during `PostTypeckThroughBorrowck`.
- **Old solver (`compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:846-867`)**: Skips `AutoImplCandidate` if a `ProjectionCandidate` (explicit item bound) already exists, marks `candidates.ambiguous = true` inside the defining scope (`can_define_opaque_ty(def_id)`), and pushes `AutoImplCandidate` outside the defining scope, which confirms against `type_of(def_id)`.

Live probes confirm exact parity across both solvers:
- `tait_05`: `OpaqueRc` hiding `Rc<u32>` fails `require_send::<m::OpaqueRc>()` with **`E0277`** (`within OpaqueRc, the trait Send is not implemented for Rc<u32>`).
- `tait_06`: `OpaqueU64` hiding `u64` satisfies `Send + Sync + Unpin` (`rc = 0`).
- `tait_13`: `dep::Secret` hiding `[u64; 3]` across a separate `libdep.rlib` crate satisfies `Send + Sync + Unpin` (`XC_AUTO=true`).
- `atpit_01` and `atpit_02`: `ATPIT` associated types leak `Send` identically—`[u32; 3]::IntoIter` passes (`ATPIT_SUM=12 SEND=true`), while `Rc<u32>` fails `E0277`.

#### 3.3 Phase 3 (`Reveal::All` / `PostAnalysis` / `Codegen`): Layout & ABI Transparency and the Coroutine Layout Split

Even when an opaque type is strictly rigid to user-facing type checking—including when imported from an upstream `.rlib` crate—its concrete size, alignment, niches, and calling-convention ABI are transparent to CTFE (`const { size_of::<Hidden>() }`), MIR monomorphization, and codegen.

The exact source mechanism is `layout_of` in `compiler/rustc_ty_utils/src/layout.rs:40-94` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`):

```rust
fn layout_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    query: ty::PseudoCanonicalInput<'tcx, Ty<'tcx>>,
) -> Result<TyAndLayout<'tcx>, &'tcx LayoutError<'tcx>> {
    let PseudoCanonicalInput { typing_env, value: original_ty } = query;
    let PseudoCanonicalInput { typing_env, value: unnormalized_ty } =
        typing_env.with_post_analysis_normalized_invalidating_rigid_aliases(tcx, original_ty);
    let normalized_ty = match tcx.try_normalize_erasing_regions(typing_env, unnormalized_ty) {
        Ok(t) => t,
        Err(normalization_error) => return Err(...),
    };
    ...
}
```

1. `with_post_analysis_normalized_invalidating_rigid_aliases` (`compiler/rustc_middle/src/ty/mod.rs:1332-1353`) upgrades any analysis/borrowck `TypingMode` to `TypingMode::PostAnalysis`, normalizes `param_env`, and calls `ty::set_aliases_to_non_rigid(tcx, value)` so previously rigid opaque aliases become normalizable again.
2. `tcx.try_normalize_erasing_regions` (`compiler/rustc_middle/src/ty/normalize_erasing_regions.rs:103-130`) expands every opaque alias—local or foreign via encoded crate metadata—to its concrete witness.
3. CTFE (`InterpCx` in `compiler/rustc_const_eval/src/interpret/eval_context.rs:42-44`) always holds a `TypingEnv` with `TypingMode::PostAnalysis`, and monomorphization collection (`compiler/rustc_monomorphize/src/collector.rs:437, 642`) runs in `TypingEnv::fully_monomorphized()` (`TypingMode::Codegen` at `1.102`/`HEAD`, `TypingMode::PostAnalysis` at `1.98`).
4. **Critical `1.102.0-nightly`/`HEAD` refinement (`layout.rs:76-85, 549-561`)**: Inside `layout_of_uncached`, computing the layout of a `ty::Coroutine(def_id, args)` explicitly requires `ty::TypingMode::Codegen`—in `TypingMode::PostAnalysis` (and all earlier modes), it returns `Err(LayoutError::TooGeneric(ty))` so that CTFE and pre-codegen MIR passes cannot observe optimized-MIR-dependent coroutine state-machine sizes prematurely. By contrast, non-coroutine TAITs and ATPITs normalize directly to their concrete witness types (e.g., `u32`, `[u64; 3]`) during `PostAnalysis`, so `const HIDDEN_SIZE: usize = size_of::<Hidden>()` (`tait_01`: `SIZE=4 ALIGN=4`) and cross-crate `const SECRET_SIZE: usize = size_of::<dep::Secret>()` (`tait_13`: `XC_SIZE=24 XC_ALIGN=8`) evaluate cleanly during compile-time constant evaluation and match runtime and `Miri` execution bit-for-bit.

### 4. `ATPIT` (`impl_trait_in_assoc_type`) and `RTN` (`return_type_notation`) Lowering

Basis: source + execution

#### 4.1 `ATPIT` Same-`impl` Scoped Defining Resolution

In `compiler/rustc_hir_analysis/src/collect/type_of/opaque.rs:15-54`, `find_opaque_ty_constraints_for_impl_trait_in_assoc_type` walks upward past nested opaques (`type Alias = impl Trait<Foo = impl Trait>`) to locate the enclosing `DefKind::Impl`, then checks *only* `ty::AssocKind::Const` and `ty::AssocKind::Fn` items belonging to that same `impl` block (`tcx.associated_item_def_ids(impl_def_id)`). Associated types themselves cannot constrain opaques because they lack bodies (line 40). If no associated function or constant of the `impl` constrains the `ATPIT`, `rustc` emits `UnconstrainedOpaqueType` with `what: "impl"`. Because `OpaqueTypeCollector` (`compiler/rustc_ty_utils/src/opaque_types.rs:237-254`) restricts implicit collection to `assoc.defaultness(tcx).is_final()`, specializable default associated types cannot silently acquire an `ATPIT` defining scope.

#### 4.2 `RTN` Lowering to Higher-Ranked `RPITIT` Projection Bounds

Both syntactic forms of `return_type_notation`—inline trait bounds (`W: Worker<run(..): Send>`, `rtn_01`, `rtn_02`) and type-qualified `where` clauses (`where W::run(..): Send` or `where <W as Worker>::run(..): Send`, `rtn_03`)—lower through `compiler/rustc_hir_analysis/src/hir_ty_lowering/bounds.rs` into the exact same helper `lower_return_type_notation_ty` (lines 756–828):

- **Trait-bound entry (`bounds.rs:396-466, 497-604`)**: When `constraint.gen_args.parenthesized == hir::GenericArgsParentheses::ReturnTypeNotation`, `assoc_tag` is set to `ty::AssocTag::Fn`. Equality constraints (`W: Worker<run(..) = ()>`, `rtn_04`) are rejected at lines 498–502 with `ReturnTypeNotationEqualityBound` (`return type notation is not allowed to use type equality`). Trait-bound constraints (`AssocItemConstraintKind::Bound`) bind the projection term returned by `lower_return_type_notation_ty` with `tcx.late_bound_vars(constraint.hir_id)` and lower each RHS bound (`Send`, etc.) onto that projection type.
- **Type-qualified entry (`bounds.rs:627-750`)**: `lower_ty_maybe_return_type_notation` handles both `QPath::Resolved` (`<W as Worker>::run(..)`) and `QPath::TypeRelative` (`W::run(..)`), recovering stashed explicit bound variables on the item segment (lines 680–693), rejecting uninferred higher-ranked trait refs on type-relative paths (lines 725–741), and calling `lower_return_type_notation_ty`.
- **Core RTN projection synthesis (`lower_return_type_notation_ty`, lines 756–828)**:
  1. Extends the trait ref's generic arguments to `item_def_id`: every method lifetime parameter becomes a fresh `ty::INNERMOST` `ty::BoundRegion` (making `run(..)` higher-ranked over all lifetime parameters of `run`), while any method type parameter (`rtn_06`) emits `ReturnTypeNotationIllegalParam::Type` (`return type notation is not allowed for functions that have type parameters`) and any method const parameter emits `ReturnTypeNotationIllegalParam::Const`.
  2. Inspects `tcx.fn_sig(item_def_id).skip_binder().output()` (lines 807–820) and requires it to be a `ty::Projection { def_id: projection_def_id }` satisfying `tcx.is_impl_trait_in_trait(projection_def_id)`. Calling RTN on a synchronous method returning a concrete type (`fn sync_fn(&self) -> u32`, `rtn_05`) fails with `ReturnTypeNotationOnNonRpitit` (`return type notation used on function that is not async and does not return impl Trait`).
  3. Shifts bound variable De Bruijn indices (`tcx.shift_bound_var_indices(num_bound_vars, output)`) and instantiates `EarlyBinder::bind(tcx, shifted_output)` with `args`, yielding the `ty::AliasTy` projection representing the method's opaque return future.

When instantiated at a concrete `impl Worker for RcWorker`, the synthetic RPITIT associated type projects to the `async fn`'s opaque `Future`, which reveals its underlying `ty::Coroutine` to auto-trait selection. In `candidate_assembly.rs:816-837` (old solver) and `trait_goals.rs:250-259` (next solver), proving `Send` on a coroutine checks every captured upvar and every local variable whose liveness spans an `.await` suspension point (`CoroutineWitness`). Consequently, `rtn_01` (`PureWorker` holding only `u32` across `.await`) compiles and executes identically under native execution (`RTN_READY=42`) and `Miri` (`RTN_READY=42`), `rtn_03` (`where W::run(..): Send`) passes natively and under `Miri` (`RTN_WHERE_READY=77`), and `rtn_02` (`RcWorker` holding `Rc<u32>` across `.await`) is rejected in both solvers with `error: future cannot be sent between threads safely` pointing directly at the `.await` suspension span.

### 5. Complete 22-Case Live `rustc` & `Miri` Differential Matrix (`1.98.0-nightly` vs. `1.102.0-nightly`)

Basis: execution

All 22 cases were compiled live by `support/probe_tait_atpit_rtn_and_next_solver.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with `--edition=2024` under both `-Z next-solver=globally` and `-Z next-solver=no`; all 8 runnable cases (15 passing solver/case combinations total, including `tait_12` under `-Z next-solver=globally` and the two-crate `dep` + `app` workspace `tait_13`) were executed both natively and under `miri 0.1.0 (14210df0e2 2026-05-31)` with `-Zmiri-tree-borrows`. The first 14 cases are compared 1:1 against `support/baseline_1_102_nightly.json` (`rustc 1.102.0-nightly`, `3ef0c22cd`).

| Case ID | Focus | `1.98` Next (`-Znext-solver=globally`) | `1.98` Old (`-Znext-solver=no`) | `1.98` Miri (`-Zmiri-tree-borrows`) | `1.102` Baseline (`3ef0c22cd`) | Parity Status |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `tait_01_valid_define_opaque_and_nondefining_size` | Valid `#[define_opaque]`, CTFE `size_of`/`align_of`, `Send` leak | `rc=0`, `EQ=true SIZE=4 ALIGN=4 SEND=true` | `rc=0`, `EQ=true SIZE=4 ALIGN=4 SEND=true` | Next `rc=0`, Old `rc=0` (exact stdout) | Both `rc=0`, `EQ=true SIZE=4 SEND=true` | Full parity |
| `tait_02_missing_define_opaque_rejected` | Missing `#[define_opaque]` | `rc=1`, `E0308` + unconstrained | `rc=1`, `E0308` + unconstrained | N/A | Both `rc=1`, `E0308` + unconstrained | Full parity (`1.98` next label wording `types differ` vs. `1.102` `expected opaque type, found u32`) |
| `tait_03_unconstrained_define_opaque_rejected` | `#[define_opaque]` without use | `rc=1`, unnumbered `item does not constrain` | `rc=1`, unnumbered `item does not constrain` | N/A | Both `rc=1`, unnumbered `item does not constrain` | Full parity |
| `tait_04_conflicting_concrete_witnesses_rejected` | Two definers (`u32` vs. `u64`) | `rc=1`, unnumbered `concrete type differs` | `rc=1`, unnumbered `concrete type differs` | N/A | Both `rc=1`, unnumbered `concrete type differs` | Full parity |
| `tait_05_non_send_rc_auto_trait_leak_rejected` | `Rc<u32>` auto-trait leak | `rc=1`, `E0277` | `rc=1`, `E0277` | N/A | Both `rc=1`, `E0277` | Full parity |
| `tait_06_send_u64_auto_trait_leak_accepted` | `u64` `Send+Sync+Unpin` leak | `rc=0` | `rc=0` | N/A | Both `rc=0` | Full parity |
| `tait_07_nondefining_concrete_equality_probe` | Concrete `+ 1u32` outside definer | `rc=1`, `E0369` | `rc=1`, `E0369` | N/A | Both `rc=1`, `E0369` | Full parity |
| `tait_08_Defining_self_cycle_in_box` | Cyclic `Rec = (u32, Option<Box<Rec>>)` | **`rc=1`, `E0282`** | **`rc=1`, `E0720`** | N/A | **Next `rc=1` `E0275`**, **Old `rc=1` `E0720`** | **SOLVER + VERSION DIVERGENCE** (`E0282` in `1.98` next, `E0275` in `1.102` next, `E0720` in old) |
| `tait_09_generic_lifetime_unused_in_witness` | Unused captured `'a` in `WithLt<'a>` | `rc=0`, `WITH_LT_SIZE=4` | `rc=0`, `WITH_LT_SIZE=4` | Next `rc=0`, Old `rc=0` (`WITH_LT_SIZE=4`) | Both `rc=0` (lib probe) | Full parity |
| `tait_10_generic_type_non_param_instantiation_rejected` | Non-param `GenOpaque<u32>` | **`rc=1`, unnumbered `item does not constrain`** | **`rc=1`, `E0792`** | N/A | **Next `rc=1` unnumbered**, **Old `rc=1` `E0792`** | **SOLVER DIVERGENCE** (diagnostic class) |
| `atpit_01_impl_trait_in_assoc_type_and_send_leak` | `ATPIT` + `Send` leak | `rc=0`, `ATPIT_SUM=12 SEND=true` | `rc=0`, `ATPIT_SUM=12 SEND=true` | Next `rc=0`, Old `rc=0` (exact stdout) | Both `rc=0`, `ATPIT_SUM=12 SEND=true` | Full parity |
| `rtn_01_async_fn_in_trait_send_bound` | `W: Worker<run(..): Send>` | `rc=0`, `RTN_READY=42` | `rc=0`, `RTN_READY=42` | Next `rc=0`, Old `rc=0` (`RTN_READY=42`) | Both `rc=0`, `RTN_READY=42` | Full parity |
| `rtn_02_non_send_local_rc_across_await_rejected` | `Rc<u32>` held across `.await` | `rc=1`, `future cannot be sent` | `rc=1`, `future cannot be sent` | N/A | Both `rc=1`, `future cannot be sent` | Full parity |
| `rtn_03_type_qualified_syntax_probe` | `where W::run(..): Send` | `rc=0`, `RTN_WHERE_READY=77` | `rc=0`, `RTN_WHERE_READY=77` | Next `rc=0`, Old `rc=0` (`RTN_WHERE_READY=77`) | Both `rc=0` (lib probe) | Full parity |
| `tait_11_duplicate_generic_param_rejected` | Duplicate `GenPair<T, T>` | **`rc=1`, `item does not constrain`** | **`rc=1`, `non-defining opaque type use`** | N/A | Not in 14-case baseline | **SOLVER DIVERGENCE** (diagnostic message) |
| `tait_12_nondefining_alongside_defining_in_same_scope` | `(GenOpaque<T>, GenOpaque<u32>)` in one fn | **`rc=0`, `SIZES=2,4`** | **`rc=1`, `E0792`** | **Next `rc=0` (`SIZES=2,4`)**, Old N/A | Not in 14-case baseline | **SOLVER DIVERGENCE (ACCEPT vs. REJECT)** |
| `tait_13_cross_crate_reveal_all_layout_and_abi` | Two-crate `libdep.rlib` (`[u64; 3]`) + consumer + neg `s[0]` | `dep=0`, `bin=0` (`XC_EQ=true XC_SIZE=24 XC_ALIGN=8 XC_AUTO=true`), `neg=1` (`E0608`) | Identical (`dep=0`, `bin=0`, `neg=1` `E0608`) | Next `rc=0`, Old `rc=0` (two-crate workspace, exact stdout) | Not in 14-case baseline | Full parity |
| `tait_14_lifetime_equality_exception_accepted` | `EqLt<'a: 'b, 'b: 'a>` as `EqLt<'x, 'x>` | `rc=0`, `EQLT_SIZE=8` | `rc=0`, `EQLT_SIZE=8` | Next `rc=0`, Old `rc=0` (`EQLT_SIZE=8`) | Not in 14-case baseline | Full parity |
| `atpit_02_non_send_atpit_auto_trait_rejected` | `ATPIT` hiding `Rc<u32>` | `rc=1`, `E0277` | `rc=1`, `E0277` | N/A | Not in 14-case baseline | Full parity |
| `rtn_04_equality_bound_rejected` | `W: Worker<run(..) = ()>` | `rc=1`, `not allowed to use type equality` | `rc=1`, `not allowed to use type equality` | N/A | Not in 14-case baseline | Full parity |
| `rtn_05_non_rpitit_method_rejected` | `W: Plain<sync_fn(..): Send>` | `rc=1`, `not async and does not return impl Trait` | `rc=1`, `not async and does not return impl Trait` | N/A | Not in 14-case baseline | Full parity |
| `rtn_06_method_type_param_rejected` | `async fn f<T>` with `f(..): Send` | `rc=1`, `not allowed for functions that have type parameters` | `rc=1`, `not allowed for functions that have type parameters` | N/A | Not in 14-case baseline | Full parity |

### 6. Kernel-Checked Lean `v4.34.1` Formalization (`OpaqueTypeDefiningScopeAndRevealSoundness.lean`)

Basis: source + execution + derived

To turn the empirical and compiler-source invariants above into machine-checked mathematical guarantees, `support/OpaqueTypeDefiningScopeAndRevealSoundness.lean` (2,107 lines, 97,826 bytes) mechanizes the core type-system semantics in standalone Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`).

#### 6.1 Kernel Purity Architecture and Why Recursor Encoding Eliminates `._unsafe_rec`

A subtle Lean `v4.34.1` elaborator property discovered and verified directly during mechanization is that **every equation-compiled computable recursive `def`** (even a trivial structurally recursive function over `Nat` or a custom inductive) causes Lean's LCNF compiler to emit an auxiliary constant `<fn>._unsafe_rec` into the compiled `.olean` environment (`env.constants.map₁`) for C/VM codegen—in addition to the `._unsafe_rec` helpers generated by `deriving DecidableEq, Repr` on inductives with `List`/`Option` fields.

To guarantee **strictly zero `._unsafe_rec` constants across the entire compiled module** (`env.constants.map₁` and `map₂` alike), `support/OpaqueTypeDefiningScopeAndRevealSoundness.lean`:

1. Defines `Ty` and `TyList` as a mutual inductive (`lines 110–127`) with zero `deriving` clauses.
2. Wraps the kernel mutual eliminators `@Ty.rec` and `@TyList.rec` in non-recursive fold combinators (`foldTy`, `foldTyList`, `foldTyProp`, `foldTyListProp`, `lines 129–182`), encoding all `Prop`-valued predicates (`HasParam`, `IsConcrete`, `MentionsOpaque`, `OpaqueRankLt`, `AutoTraitConcrete`) computably via `foldTyProp`/`foldTyListProp`, all `Ty`/`TyList` `Type`-valued functions (`TyList.length`, `TyList.get?`, `tyDepth`, `substTy`, `eraseRank.eraseRankStep`, `maxRankBound`, `eraseAllList`, `layoutOfConcrete`) directly via `foldTy`/`foldTyList`, and all `Nat`/`List` functions (`listMem`, `eraseRank`, `expandRecN`, `nextSolverUnrollRec`, `oldSolverCheckUnary`, `nextSolverCheckUnary`) directly via `Nat.rec`, `List.rec`, and `List.foldr`.
3. Discharges every arithmetic and structural step directly with `Nat` lemmas and inductive proofs—using **0 `sorry`**, **0 `Classical.choice`**, **0 `omega`**, **0 `bv_decide`**, **0 `native_decide`**, **0 `partial def`**, **0 `axiom`**, and **0 `opaque`**.

#### 6.2 Mechanized Theorems and Proof Structure

1. **Defining-Scope Authorization (`lines 550–590`)**:
   - `canDefine item oid origin` models `OpaqueTypeCollector`'s exact mode matrix (`CollectionMode::{ImplTraitInAssocTypes, Taits, RpitAndAsyncFnOnly}`), including the rule that an explicit `#[define_opaque(...)]` attribute sets `hasDefineOpaqueAttr = true`, enabling listed TAITs while suppressing implicit ATPIT capture.
   - `unmarked_item_cannot_define_tait` (`line 573`) proves that an item with `hasDefineOpaqueAttr = false` cannot define any `OpaqueOrigin.tait`.
   - `empty_define_opaque_suppresses_atpit` (`line 582`) proves that setting `hasDefineOpaqueAttr = true` (as with `#[define_opaque()]`) disables implicit `OpaqueOrigin.atpit` collection on an impl method.
2. **Defining-Scope Coherence & Witness Uniqueness (`coherentDefiningUses_unique_concrete_witness`, `lines 728–753`)**:
   - `BijectiveArgs arity args` (`line 600`) packages Miller's higher-order pattern condition (`fwd : Nat → ParamId`, `inv : ParamId → Nat`, `atIdx`, `leftInv`), and `CapturedByBijection bij rhs` (`line 609`) captures `ReverseMapper`'s requirement that every free parameter of `rhs` lies in `Im(fwd)`.
   - `reverseMap_wellKinded` (`line 617`), `instantiate_reverseMap_eq` (`line 660`), `reverseMap_instantiate_eq` (`line 678`), and `witness_unique_of_bijective_inst` (`line 696`) prove that `reverseMap` and `instantiate` form an exact section-retraction pair on well-kinded (`TyVarsIn arity`) declaration-site witnesses.
   - `coherentDefiningUses_unique_concrete_witness` proves—with **zero axioms** (`does not depend on any axioms`)—that for any non-empty `CoherentDefiningUses` family whose authorized bijective defining uses agree after `reverseMap`, there exists a **unique** well-kinded declaration-site witness `w` (`TyVarsIn arity w`) that instantiates to `u.use.rhs` at every defining use, commutes with every monomorphization substitution `σ`, and equals any other coherent well-kinded witness `w'`.
3. **Stratified `Reveal::All` Erasure (`eraseRank` & `eraseAll`, `lines 781–1310`)**:
   - In a stratified `World` (`stratified : ∀ oid, OpaqueRankLt rank (rank oid) (decls oid).witness`), `eraseRank world r t` applies outer `Nat.rec` on rank `r` and inner `foldTy`/`foldTyList` so that `.opaqueTy oid args` unfolds via `instantiate (recPrev (world.decls oid).witness) eArgs` in a single structural pass.
   - `eraseRank_isConcrete` (`line 864`) proves `OpaqueRankLt world.rank r t → IsConcrete (eraseRank world r t)`.
   - `eraseRank_succ_eq` (`line 903`) and `eraseRank_eq_eraseAll` (`line 1009`) prove that `eraseAll world t := eraseRank world (maxRankBound world.rank t) t` is **fuel-independent**, idempotent (`eraseAll_idempotent`), and satisfies exact substitution commutation (`eraseRank_substTy`, `line 1106`) and exact one-step opaque unfolding (`eraseAll_opaque_eq_witness`, `line 1284`):
     $$\mathrm{eraseAll}(\mathrm{opaqueTy}\;\mathit{oid}\;\mathit{args}) = \mathrm{eraseAll}(\mathrm{instantiate}(\mathit{witness}_{\mathit{oid}}, \mathit{args})).$$
4. **Three-Tier Reveal Monotonicity & Auto-Trait Soundness (`lines 1364–1640`)**:
   - `Entails world tier ob` (`line 1402`) models all five obligation classes (`userTrait`, `autoTrait`, `tyEq`, `hasLayout`, `rtnBound`) across `RevealTier.{userFacing, definingScope, revealAll}`:
     - `userFacing` exposes only declared `itemTraitBounds`, leaks `autoTrait` through the erased witness (`UserFacingAutoTrait`), forbids concrete `tyEq` on opaques, delegates `hasLayout` to `eraseAll` (mirroring `layout_of`'s upgrade to `PostAnalysis`), and lowers `rtnBound implTy m atr` to `UserFacingAutoTrait` on `world.rpititFuture implTy m`.
     - `revealAll` evaluates every obligation on fully erased concrete types (`eraseAll world t`).
   - `userFacing_refines_revealAll` (`line 1443`, `[propext]`) proves $\forall \mathit{ob},\; \mathrm{Entails}(\mathit{userFacing}, \mathit{ob}) \to \mathrm{Entails}(\mathit{revealAll}, \mathit{ob})$.
   - `definingScope_refines_revealAll` (`line 1523`, `[propext]`) extends monotonicity to the intermediate defining-scope tier.
   - `autoTrait_leakage_sound_iff_witness` (`line 1590`, `[propext]`) proves exact biconditional soundness:
     $$\mathrm{Entails}(\mathit{userFacing}, \mathrm{autoTrait}\;\mathit{atr}\;(\mathrm{opaqueTy}\;\mathit{oid}\;\mathit{args})) \iff \mathrm{AutoTraitConcrete}\;\mathit{atr}\;(\mathrm{eraseAll}(\mathrm{instantiate}(\mathit{witness}_{\mathit{oid}}, \mathit{args}))).$$
   - `layout_transparent_across_tiers` (`line 1604`) proves layout equivalence across tiers, `rtn_send_iff_coroutine_locals_send` (`line 1613`) characterizes RTN `Send` bounds in terms of coroutine captures and across-`.await` locals, and `three_phase_visibility_strict_separation` (`line 2075`) witnesses strictness of the refinement on `secretWorld` (`Secret = [u64; 3]`, matching `tait_13`: `Copy`, `Send`, and `{ size := 24, align := 8 }` hold under `userFacing`, whereas `Index` and `Secret = [u64; 3]` hold ONLY under `revealAll`).
5. **Solver Divergence Model (`solver_divergence_tait10_and_tait12`, `lines 1644–1699`)**:
   - Mechanizes `oldSolverCheckUnary` (eager `E0792` on any non-parameter use) vs. `nextSolverCheckUnary` (skips non-defining uses when a defining use exists; emits `itemDoesNotConstrain` if none exists) and proves both the diagnostic divergence (`tait_10`) and the accept-vs.-reject divergence (`tait_12`).
6. **Four Constructive Sharpness Counterexamples (`lines 1700–2050`)**:
   - **`ce1_conflicting_definers_break_transitivity_unsound` (`line 1704`)** and **`ce1_conflicting_definers_break_layout_soundness` (`line 1716`)**: Proves that admitting both `Hidden = u32` and `Hidden = u64` (`tait_04`) breaks equality transitivity (`Ty.prim .u32 = Ty.prim .u64`) and ABI layout consistency (`4 = 8`), deriving `False`.
   - **`ce2_non_injective_param_instantiation_breaks_coherence` (`line 1742`)**: Constructively exhibits TWO distinct well-kinded witnesses for BOTH duplicate-parameter (`GenPair<T, T> = (T, T)`: `w1 = (A, B)` vs. `w2 = (A, A)`, producing distinct layouts `16 B / align 8` vs. `8 B / align 4` at `GenPair<u32, u64>`) and non-parameter (`GenOpaque<u32> = u32`: `w1 = T` vs. `w2 = u32`, producing `8 B` vs. `4 B` at `GenOpaque<u64>`) instantiations.
   - **`ce3_self_referential_opaque_cycle_diverges_without_inductive_guard` (`line 1879`)**: For `Rec = (u32, Option<Box<Rec>>)` (`tait_08`), proves four simultaneous sharpness facts: (i) `MentionsOpaque recId` fires directly (`E0720`), (ii) no finite `Ty` satisfies `t = expandRecStep t` (because `tyDepth (expandRecStep t) = tyDepth t + 2`), (iii) `n`-step expansion has unbounded AST depth `≥ n`, and (iv) bounded-fuel unrolling (`nextSolverUnrollRec`) returns `none` (overflow) at EVERY finite recursion limit `L : Nat`.
   - **`ce4_rtn_rc_across_await_violates_send` (`line 1978`)**: In `rtnWorld` (modeling `rtn_01` `PureWorker` vs. `rtn_02` `RcWorker`), proves that `W: Worker<run(..): Send>` holds for `PureWorker`, fails for `RcWorker` (due to `Rc<u32>` in `acrossAwait`), and fails `Unpin` even for `PureWorker` (immovable coroutine future).

#### 6.3 Verified Kernel Audit Receipt (`Lean v4.34.1`)

Compiling `support/OpaqueTypeDefiningScopeAndRevealSoundness.lean` to `.olean` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` exited with code `0` and zero warnings. Inspecting the imported `.olean` via `#print axioms` and scanning `env.constants.map₁` produced:

```text
LOC: 2107
STRICT_OLEAN_BUILD_EXIT=0
'Anneal.OpaqueTypeSoundness.coherentDefiningUses_unique_concrete_witness' does not depend on any axioms
'Anneal.OpaqueTypeSoundness.userFacing_refines_revealAll' depends on axioms: [propext]
'Anneal.OpaqueTypeSoundness.definingScope_refines_revealAll' depends on axioms: [propext]
'Anneal.OpaqueTypeSoundness.autoTrait_leakage_sound_iff_witness' depends on axioms: [propext]
'Anneal.OpaqueTypeSoundness.layout_transparent_across_tiers' depends on axioms: [propext]
'Anneal.OpaqueTypeSoundness.rtn_send_iff_coroutine_locals_send' depends on axioms: [propext]
'Anneal.OpaqueTypeSoundness.solver_divergence_tait10_and_tait12' depends on axioms: [propext]
'Anneal.OpaqueTypeSoundness.ce1_conflicting_definers_break_transitivity_unsound' depends on axioms: [propext]
'Anneal.OpaqueTypeSoundness.ce1_conflicting_definers_break_layout_soundness' depends on axioms: [propext]
'Anneal.OpaqueTypeSoundness.ce2_non_injective_param_instantiation_breaks_coherence' depends on axioms: [propext]
'Anneal.OpaqueTypeSoundness.ce3_self_referential_opaque_cycle_diverges_without_inductive_guard' depends on axioms: [propext]
'Anneal.OpaqueTypeSoundness.ce4_rtn_rc_across_await_violates_send' depends on axioms: [propext]
'Anneal.OpaqueTypeSoundness.three_phase_visibility_strict_separation' depends on axioms: [propext]
MAP1_DECL_COUNT=677
MAP1_UNSAFE_REC_COUNT=0 #[]
MAP1_IS_UNSAFE_COUNT=0 #[]
MAP1_OPAQUE_INFO_COUNT=0 #[]
MAP1_AXIOM_INFO_COUNT=0 #[]
```

### 7. Implications for `joshlf/anneal` Trusted Boundary and Future Verified MIR Capture

Basis: source + derived

Inspecting `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes three concrete boundary facts for verified MIR capture and proof architecture:

1. **Current Fail-Closed Exclusion of Opaques and Coroutines**:
   - `trusted/lean/Trusted/MirAst.lean` (lines 286, 310, 461, 470, 709–711, 763, 784, 825) explicitly documents that `TyKind::{Closure, CoroutineClosure, Coroutine, CoroutineWitness}`, `ProjectionElem::OpaqueCast`, `TerminatorKind::CoroutineDrop`, and `Body.coroutine` are outside the admitted MIR fragment and rejected fail-closed during capture.
   - `trusted/rustc-capture/src/driver.rs` (lines 25, 45–47, 75–84) pins `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` and runs inside `Callbacks::after_analysis`, verifying a clean compilation before returning (`analysis_reached = tcx.dcx().has_errors().is_none()`).
2. **Exact Normalization Contract Needed to Admit `TAIT` / `ATPIT` / `RPITIT` / `RTN` in Post-Analysis Capture**:
   - Because `after_analysis` executes after `typeck`, `mir_borrowck`, and `TaitConstraintLocator` have already checked defining-scope authorization, higher-order pattern bijectivity, cross-definer witness agreement, and acyclicity, every non-error opaque type in the crate graph has a unique declaration-site witness retrievable via `tcx.type_of(opaque_def_id)`.
   - However, MIR bodies captured before monomorphization (e.g., `optimized_mir` or `mir_drops_elaborated_and_const_checked`) can still contain unnormalized `ty::Alias(_, ty::Opaque { .. })` and `ProjectionElem::OpaqueCast` nodes. A verified exporter MUST normalize all captured local, place, and callee types using `TypingEnv::post_analysis(tcx, def_id)` (for polymorphic non-coroutine opaque witnesses) or `TypingEnv::fully_monomorphized()` (`TypingMode::Codegen` on `1.102+`, required whenever computing `ty::Coroutine` state-machine layouts per `compiler/rustc_ty_utils/src/layout.rs:549-561`) and MUST invalidate rigid alias flags (`with_post_analysis_normalized_invalidating_rigid_aliases` / `with_codegen_normalized_invalidating_rigid_aliases`, `compiler/rustc_middle/src/ty/mod.rs:1332-1379`) whenever crossing from an analysis `TypingEnv` to post-analysis/codegen normalization.
   - Failing to upgrade `TypingMode` leaves foreign or non-defining opaques rigid, breaking ABI layout computation and creating a mismatch between captured MIR types and the monomorphized types actually executed by Miri and LLVM codegen.
3. **Solver-Flag Isolation in Capture Drivers**:
   - Because `-Z next-solver=globally` accepts programs that `-Z next-solver=no` rejects (`tait_12`: coexisting `GenOpaque<T>` and `GenOpaque<u32>` in one defining scope), a verified compiler or MIR capture driver must record the exact `-Z next-solver` mode in its build provenance; however, once accepted by either solver, the unique coherent witness theorem (`coherentDefiningUses_unique_concrete_witness`) and `Miri` execution parity (`tait_01`, `tait_09`, `tait_12`, `tait_13`, `tait_14`, `atpit_01`, `rtn_01`, `rtn_03`) confirm that post-analysis revealed MIR semantics are identical between solvers for all accepted programs.

## Boundaries

To prevent over-generalization, negative space is classified strictly under the four `reference-corpus/1` boundary categories:

### Known Not to Apply

- **Historical `Reveal::{UserFacing, All}` enum names in `rustc` `1.98.0-nightly` through `HEAD`**: Source inspection of `compiler/rustc_type_ir/src/infer_ctxt.rs` and `compiler/rustc_middle/src/ty/mod.rs` confirms that `enum Reveal` has been replaced by `TypingMode` (`Analysis`/`Borrowck`/`PostBorrowckAnalysis`/`PostAnalysis` in `1.98`; `Typeck`/`PostTypeckThroughBorrowck`/`PostBorrowck`/`Reflection`/`PostAnalysis`/`Codegen` in `1.102`/`HEAD`). Code targeting `rustc_middle` APIs on `1.98+` cannot import `ty::Reveal`.
- **Coroutine layout transparency during `TypingMode::PostAnalysis` on `1.102.0-nightly` and `HEAD`**: Directly refuted by `compiler/rustc_ty_utils/src/layout.rs:549-561`, which explicitly rejects `ty::Coroutine` layout with `LayoutError::TooGeneric` unless `typing_mode == TypingMode::Codegen`. Layout transparency in `PostAnalysis` applies to non-coroutine opaque witnesses, not to `async fn` coroutine state-machine layouts.
- **Unconditional rejection of duplicate lifetime arguments in defining uses**: Directly refuted by `LazyOpaqueTyEnv::params_equal` (`compiler/rustc_trait_selection/src/opaque_types.rs:104-107, 152-155`) and live execution of `tait_14_lifetime_equality_exception_accepted` (`EqLt<'a: 'b, 'b: 'a>` instantiated with `EqLt<'x, 'x>`).
- **Solver parity on non-defining uses inside defining scopes**: Directly refuted by live execution of `tait_12_nondefining_alongside_defining_in_same_scope` (`rc = 0` under `-Z next-solver=globally`, `rc = 1` `E0792` under `-Z next-solver=no`).
- **Connection of `OpaqueTypeDefiningScopeAndRevealSoundness.lean` to live `joshlf/anneal` `Trusted.MirSemantics`**: The Lean formalization is a standalone, self-contained PL/type-system model over an abstract `Ty`/`TyList`/`Layout`/`World` AST (`0` imports of `Trusted.MirSemantics`); it does NOT formally verify `rustc`'s Rust source code or Anneal's MIR small-step interpreter.

### Unsupported

- **RTN equality bounds (`W: Worker<run(..) = ()>`), RTN on non-RPITIT methods (`W: Plain<sync_fn(..): Send>`), and RTN on methods with type/const generic parameters (`async fn f<T>`)**: Explicitly unsupported by `rustc` (`compiler/rustc_hir_analysis/src/hir_ty_lowering/bounds.rs:498-502, 778-820`) and verified live in `rtn_04`, `rtn_05`, and `rtn_06`.
- **`TAIT`, `ATPIT`, and `RTN` on stable Rust toolchains**: All three require unstable `#![feature(...)]` gates (`type_alias_impl_trait`, `impl_trait_in_assoc_type`, `return_type_notation`) as documented in `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`src/types/impl-trait.md:172`).
- **Opaque types and coroutines in `joshlf/anneal@c131b320e` MIR capture**: Explicitly unsupported by `trusted/lean/Trusted/MirAst.lean` (`OpaqueCast`, `Coroutine`, `CoroutineWitness`, `CoroutineClosure` excluded).

### Not Examined

- **Const generic parameter defining-use edge cases (`GenConst<const N: usize>`)**: `opaque_type_has_defining_use_args` (`rustc_trait_selection/src/opaque_types.rs:97`) and `ReverseMapper::fold_const` (`rustc_middle/src/ty/opaque_types.rs:192-215`) were audited in source, but no live `rustc`/`Miri` probe was executed for const-parameter TAITs or `generic_const_exprs` interactions.
- **Member constraints and borrow-checker region-choice failures (`UnexpectedHiddenRegion`, `LifetimeMismatchOpaqueParam`)**: Source files `compiler/rustc_borrowck/src/region_infer/opaque_types/{mod.rs,member_constraints.rs,region_ctxt.rs}` were inspected for control flow, but live negative probes exercising borrowck NLL member-constraint errors, closure-parent region erasure (`ToArgRegionsFolder`), and Polonius interactions were not executed.
- **Higher-ranked trait bounds (`for<'a>`) and `dyn` compatibility interacting with `TAIT`/`ATPIT`/`RTN`**, **specialization interaction with `default type` (`is_final() == false`)**, **const-trait (`[const]` / `is_conditionally_const`) opaque bounds**, and **non-`x86_64-unknown-linux-gnu` target ABI layouts** (e.g., `aarch64`, `i686`, `windows-msvc`): Not examined empirically.
- **Live execution of `rustc` built from `HEAD` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`) or Anneal's pinned `1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`)**: Only `1.98.0-nightly` (`14210df0e`) and `1.102.0-nightly` (`3ef0c22cd`) binaries were executed; `HEAD` behavior is inferred solely from source inspection and byte-for-byte diffs against `1.102.0-nightly`.
- **Execution of the 8 extended cases (`tait_11`–`tait_14`, `atpit_02`, `rtn_04`–`rtn_06`) on `1.102.0-nightly`**: Those 8 cases were executed live on `1.98.0-nightly` (`14210df0e`) and checked against `1.102.0-nightly`/`HEAD` source, but not run on a `1.102.0-nightly` binary.

### Unknown

- **Exact intermediate commit between `14210df0e` (`2026-05-31`) and `3ef0c22cd` (`2026-11-11`) where `tait_08` transitioned from `E0282` to `E0275` under `-Z next-solver=globally`**: Source diffs narrow this transition to the `normalizes_to/opaque_types.rs` -> `project_goals/opaque_types.rs` and `resolve_vars_if_possible` -> `deeply_resolve_ignoring_regions` refactors, but no `git bisect` across intermediate commits was performed.
- **Whether the `FIXME` comment in `project_goals/opaque_types.rs:132-134` (`TypingMode::PostBorrowck` folding `ReErased` into `next_region_var` — "This is also probably unsound or sth") admits a concrete soundness exploit**: Noted in primary source, but no exploit reproducer was constructed.
- **Whether `FnCtxt::detect_opaque_types_added_during_writeback` (`compiler/rustc_hir_typeck/src/opaque_types.rs:270-292`) is reachable in practice**: Upstream source itself notes no known reproducer exists; not resolved here.

### Attractive Stronger Conclusions Not Established

- Passing `userFacing_refines_revealAll` in `OpaqueTypeDefiningScopeAndRevealSoundness.lean` does **not** prove `rustc` itself is free of opaque-type soundness bugs (for example, region-erasure soundness holes in `PostBorrowck` or borrowck member-constraint edge cases, which are outside the formal model's region-free `Ty` syntax).
- Observing `0` Miri UB diagnostics across 15 runnable probe executions establishes absence of UB only on those 8 concrete programs, not across arbitrary unsafe code interacting with opaque types or self-referential `!Unpin` coroutines.

## Evidence

### Primary Git Sources (All 40-Hex Commit SHAs Verified Live)

#### `rust-lang/rust` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`HEAD`, `2026-11-22`)

| Path | Lines | Symbols / Key Facts Verified |
| :--- | :--- | :--- |
| `compiler/rustc_ty_utils/src/opaque_types.rs` | `30–50`, `66–197`, `206–383` | `CollectionMode::{ImplTraitInAssocTypes, Taits, RpitAndAsyncFnOnly}`; `collect_taits_from_defines_attr` (`#[define_opaque]` resets mode to `RpitAndAsyncFnOnly`); `visit_opaque_ty`; `visit_ty` (`trait_impl_of_assoc` + `defaultness().is_final()` for ATPIT; `opt_rpitit_info` for RPITIT); `opaque_types_defined_by`. |
| `compiler/rustc_hir_analysis/src/collect/type_of/opaque.rs` | `15–54`, `75–203`, `237–288` | `find_opaque_ty_constraints_for_impl_trait_in_assoc_type` (same-`impl` `AssocKind::{Const, Fn}` walk); `find_opaque_ty_constraints_for_tait` (`UnconstrainedOpaqueType`); `TaitConstraintLocator::insert_found` (mismatch error) and `non_defining_use_in_defining_scope`; `find_opaque_ty_constraints_for_rpit`. |
| `compiler/rustc_hir_typeck/src/opaque_types.rs` | `58–87`, `90–268`, `270–292` | `UsageKind::{None, NonDefiningUse, UnconstrainedHiddenType, HasDefiningUse}`; `compute_definition_site_hidden_types` (`deeply_resolve_ignoring_regions`, skips non-defining uses when defining use exists, emits `report_item_does_not_constrain_error` or `E0282` with hidden-type note); `consider_opaque_type_use`; `detect_opaque_types_added_during_writeback`. |
| `compiler/rustc_hir_typeck/src/writeback.rs` | `564–665`, `1070–1097` | Old-solver `visit_opaque_types` (eager `err.report()` -> `E0792`, mismatch check, `HasRecursiveOpaque` cycle check -> `E0720`). |
| `compiler/rustc_hir_analysis/src/check/check.rs` | `2192–2250` | `opaque_type_cycle_error` (`E0720` diagnostic builder). |
| `compiler/rustc_trait_selection/src/opaque_types.rs` | `17–58`, `66–211`, `213–235` | `NonDefiningUseReason::{Tainted, NotAParam, DuplicateParam}` and `report()` (`E0792` `NonGenericOpaqueTypeParam`, `non-defining opaque type use in defining scope`); `opaque_type_has_defining_use_args`; `LazyOpaqueTyEnv` (`param_equal_static`, `params_equal`); `report_item_does_not_constrain_error`. |
| `compiler/rustc_middle/src/ty/opaque_types.rs` | `16–216` | `ReverseMapper` (`fold_closure_args` `do_not_error` -> `re_static`, `fold_region`, `fold_ty`, `fold_const`). |
| `compiler/rustc_infer/src/infer/opaque_types/mod.rs` | `25–171`, `217–385` | Old-solver `replace_opaque_types_with_inference_vars`, `handle_opaque_type`, `insert_hidden_type`, `add_item_bounds_for_hidden_type`. |
| `compiler/rustc_infer/src/infer/opaque_types/table.rs` | `12–161` | `OpaqueTypeStorage`, `OpaqueTypeTable::register` / `add_duplicate` with undo log. |
| `compiler/rustc_borrowck/src/region_infer/opaque_types/mod.rs` | `44–59`, `157–180`, `203–404`, `412–622`, `745–784` | `DeferredOpaqueTypeError`; `add_hidden_type`; `collect_defining_uses` (`use_typing_mode_post_typeck_through_borrowck` divergence); `ToArgRegionsFolder`; `apply_definition_site_hidden_types`; `infer_opaque_definition_from_instantiation`. |
| `compiler/rustc_next_trait_solver/src/solve/project_goals/opaque_types.rs` | `17–183` | `EvalCtxt::normalize_opaque_type` exhaustive dispatch over all 8 `TypingMode` variants (`Coherence`, `Typeck`, `PostTypeckThroughBorrowck`, `PostBorrowck`, `Reflection`, `PostAnalysis`, `Codegen`, `ErasedNotCoherence`). |
| `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs` | `194–260`, `1321–1390` | `consider_auto_trait_candidate`; `consider_auto_trait_candidate_for_opaque_ty` (item-bound cycle skip, `type_of` probe, `var_values_is_identity == IsIdentity::No` anti-leakage guard, `opaque_types` guard). |
| `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs` | `816–871` | Old-solver coroutine `Unpin`/auto-trait rules and opaque `AutoImplCandidate` leakage outside defining scope. |
| `compiler/rustc_trait_selection/src/traits/normalize.rs` & `traits/query/normalize.rs` | `132–152`, `231–249` | Old-solver `needs_normalization` stripping `HAS_TY_OPAQUE` outside `Reflection | PostAnalysis | Codegen`; `AssocTypeNormalizer` opaque reveal + `recursion_limit`. |
| `compiler/rustc_type_ir/src/infer_ctxt.rs` | `70–164` | Exhaustive `#[rustc_must_match_exhaustively] pub enum TypingMode`. |
| `compiler/rustc_middle/src/ty/mod.rs` | `1233–1380` | `TypingEnv::{fully_monomorphized, non_body_analysis, post_typeck_through_borrowck, post_analysis, codegen, with_post_analysis_normalized_invalidating_rigid_aliases, with_codegen_normalized_invalidating_rigid_aliases}`. |
| `compiler/rustc_middle/src/ty/normalize_erasing_regions.rs` | `42–130` | `normalize_erasing_regions`, `assert_fully_normalized`, `try_normalize_erasing_regions`. |
| `compiler/rustc_ty_utils/src/layout.rs` | `40–109`, `549–604` | `layout_of` unconditional upgrade to `TypingMode::PostAnalysis` (`with_post_analysis_normalized_invalidating_rigid_aliases`), fallback to `Codegen` on `TooGeneric`; `ty::Coroutine` gated strictly to `TypingMode::Codegen`. |
| `compiler/rustc_const_eval/src/interpret/eval_context.rs` & `compiler/rustc_monomorphize/src/collector.rs` | `42–44`; `437`, `642` | CTFE `InterpCx` running in `TypingMode::PostAnalysis`; monomorphization collector running in `TypingEnv::fully_monomorphized()`. |
| `compiler/rustc_hir_analysis/src/hir_ty_lowering/bounds.rs` | `396–502`, `596–604`, `627–828` | RTN lowering: `ReturnTypeNotationEqualityBound`, `lower_ty_maybe_return_type_notation`, `lower_return_type_notation_ty` (`ReturnTypeNotationIllegalParam`, `is_impl_trait_in_trait`, `ReturnTypeNotationOnNonRpitit`, `shift_bound_var_indices`). |

#### Cross-Version `rust-lang/rust` Diffs (`1.98.0-nightly` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` vs. `1.102.0-nightly` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` vs. `HEAD` `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`)

- `compiler/rustc_hir_typeck/src/opaque_types.rs` and `compiler/rustc_next_trait_solver/src/solve/project_goals/opaque_types.rs` have **empty diffs** between `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`.
- Between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`:
  - `compiler/rustc_type_ir/src/infer_ctxt.rs:66-145` (6-variant `TypingMode`) expanded to `71-164` (8-variant `TypingMode`, splitting `Codegen` from `PostAnalysis` and adding `Reflection`).
  - `compiler/rustc_next_trait_solver/src/solve/normalizes_to/opaque_types.rs` (`175` lines) was refactored into `compiler/rustc_next_trait_solver/src/solve/project_goals/opaque_types.rs` (`183` lines).
  - `compiler/rustc_hir_typeck/src/opaque_types.rs:96` switched from `self.resolve_vars_if_possible(*entry)` to `self.deeply_resolve_ignoring_regions(*entry)` and added the `"cannot infer type of hidden type of opaque"` note on `E0282`.

#### Other Audited Upstream Repositories

- **`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`** (`2026-11-17`): `src/types/impl-trait.md:1-176` (`r[type.impl-trait.*]`), `src/items/type-aliases.md:1-51` (`r[items.type.*]`).
- **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`** (`2026-11-19`): `trusted/rustc-capture/src/driver.rs:25, 45-47, 75-84` (pins `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `1.98.0-nightly 2026-05-30`); `trusted/lean/Trusted/MirAst.lean:286, 310, 461, 470, 709-711, 763, 784, 825`; `trusted/audit/TrustedBoundary.lean:84-103, 458-475, 2164`.
- **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`** (`v4.34.1`, `2026-09-24`): Kernel typechecker and `.olean` environment inspector.

### Preserved Support Material (`support/`)

| File | Size / Lines | Role & Observation Date |
| :--- | ---: | :--- |
| `support/probe_tait_atpit_rtn_and_next_solver.py` | 24,544 B / 810 lines | Standalone differential probe runner compiling all 22 cases (including two-crate `libdep.rlib` + `consumer` + `neg`) under both `-Znext-solver=globally` and `-Znext-solver=no`, executing binaries natively and under `cargo miri run` (`-Zmiri-tree-borrows`). |
| `support/probe_results_1_98_nightly.json` | 33,848 B / 594 lines | Live execution output from `2026-11-22` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `LLVM 22.1.6` / `miri 0.1.0 (14210df0e2 2026-05-31)`: 22 cases, 4 solver divergences (`tait_08`, `tait_10`, `tait_11`, `tait_12`), 15/15 Miri `-Zmiri-tree-borrows` passes (`rc = 0`, exact stdout parity). |
| `support/baseline_1_102_nightly.json` | 20,964 B / 306 lines | 14-case differential execution baseline on `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` / `LLVM 23.1.5`: documents `E0275` vs. `E0720` on `tait_08` and unnumbered `item does not constrain` vs. `E0792` on `tait_10`. |
| `support/OpaqueTypeDefiningScopeAndRevealSoundness.lean` | 97,826 B / 2,107 lines | Standalone kernel-checked Lean `v4.34.1` formalization (`2026-11-22`): 677 constants in `env.constants.map₁`, `0` `._unsafe_rec`, `0` `isUnsafe`, `0` `opaqueInfo`, `0` `axiomInfo`, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`; proves `coherentDefiningUses_unique_concrete_witness` (`[]` axioms), `userFacing_refines_revealAll`, `autoTrait_leakage_sound_iff_witness`, `solver_divergence_tait10_and_tait12`, `ce1`–`ce4`, and `three_phase_visibility_strict_separation` (`[propext]`). |

## Revalidation

Each claim class can be cheaply and independently revalidated against any newer `rustc`, `Miri`, `joshlf/anneal`, or `lean4` revision without repeating the full audit:

### 1. Re-run the 22-Case Live `rustc` + `Miri` Differential Suite

With any nightly `rustc` and `miri` component installed on `PATH`:

```bash
python3 support/probe_tait_atpit_rtn_and_next_solver.py /tmp/tait_probe_out.json
python3 - <<'PY'
import json
d = json.load(open("/tmp/tait_probe_out.json"))
print("rustc:", d["rustc_version"].splitlines()[0])
print("miri:", d["miri_version"])
print("cases:", d["case_count"], "divergences:", d["solver_divergences"])
for k, v in d["cases"].items():
    g, n = v["next_solver_globally"], v["next_solver_no"]
    print(f"  {k:54s} g={g.get('rc', g.get('consumer_rc'))} n={n.get('rc', n.get('consumer_rc'))} "
          f"g_err={g.get('error_codes', g.get('neg_concrete_op_error_codes'))} "
          f"n_err={n.get('error_codes', n.get('neg_concrete_op_error_codes'))} "
          f"miri=({g.get('miri', {}).get('rc', '-')},{n.get('miri', {}).get('rc', '-')})")
PY
```

**What to watch for**:
- If `tait_08` changes error code under `-Znext-solver=globally` (e.g., `E0282` -> `E0275` -> `E0720`), `-Znext-solver` cycle detection changed.
- If `tait_12` starts passing under `-Znext-solver=no` (or if `-Znext-solver=no` is retired once the new solver becomes default), the accept-vs.-reject solver divergence has closed.
- If `tait_13` fails `const SECRET_SIZE` or accepts `s[0]`, cross-crate `PostAnalysis` layout transparency or `Typeck` rigidity changed.

### 2. Diff the Six Load-Bearing Upstream `rustc` Implementation Files

Check whether upstream `rust-lang/rust` has altered defining-scope collection, `TypingMode` dispatch, auto-trait leakage, coroutine layout gating, or RTN lowering by diffing from `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` to target `<REV>`:

```bash
for path in \
  compiler/rustc_ty_utils/src/opaque_types.rs \
  compiler/rustc_hir_typeck/src/opaque_types.rs \
  compiler/rustc_next_trait_solver/src/solve/project_goals/opaque_types.rs \
  compiler/rustc_next_trait_solver/src/solve/trait_goals.rs \
  compiler/rustc_ty_utils/src/layout.rs \
  compiler/rustc_hir_analysis/src/hir_ty_lowering/bounds.rs; do
  echo "=== $path ==="
  git diff 342d74463af7dd3018ef6aa04dd5500c2deb5bd1..<REV> -- "$path" | head -n 40
done
```

### 3. Re-verify the Lean `v4.34.1` Formalization and `env.constants.map₁` Purity Gate

```bash
LEAN_BIN="${LEAN_SYSROOT:-$HOME/.elan/toolchains/leanprover--lean4---v4.34.1}/bin/lean"
"$LEAN_BIN" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  -R support -o /tmp/OpaqueTypeDefiningScopeAndRevealSoundness.olean \
  support/OpaqueTypeDefiningScopeAndRevealSoundness.lean

cat > /tmp/AuditOpaqueOlean.lean <<'EOF'
import Lean.Elab.Command
import OpaqueTypeDefiningScopeAndRevealSoundness
open Anneal.OpaqueTypeSoundness in
#print axioms coherentDefiningUses_unique_concrete_witness
open Anneal.OpaqueTypeSoundness in
#print axioms userFacing_refines_revealAll
open Anneal.OpaqueTypeSoundness in
#print axioms autoTrait_leakage_sound_iff_witness
open Anneal.OpaqueTypeSoundness in
#print axioms ce1_conflicting_definers_break_transitivity_unsound
open Anneal.OpaqueTypeSoundness in
#print axioms ce2_non_injective_param_instantiation_breaks_coherence
open Anneal.OpaqueTypeSoundness in
#print axioms ce3_self_referential_opaque_cycle_diverges_without_inductive_guard
open Anneal.OpaqueTypeSoundness in
#print axioms ce4_rtn_rc_across_await_violates_send
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut unsafeRecs : Array Name := #[]
  let mut opaqueDecls : Array Name := #[]
  for (n, ci) in env.constants.map₁ do
    let s := n.toString
    if s.startsWith "Anneal.OpaqueTypeSoundness" then
      if (s.splitOn "_unsafe_rec").length > 1 then unsafeRecs := unsafeRecs.push n
      if ci matches .opaqueInfo _ then opaqueDecls := opaqueDecls.push n
  IO.println s!"MAP1_UNSAFE_REC={unsafeRecs.size} MAP1_OPAQUE={opaqueDecls.size}"
EOF
LEAN_PATH=/tmp "$LEAN_BIN" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false /tmp/AuditOpaqueOlean.lean
```

**Expected output**: exit code `0`, `coherentDefiningUses_unique_concrete_witness` depends on no axioms, all remaining theorems depend solely on `[propext]`, and `MAP1_UNSAFE_REC=0 MAP1_OPAQUE=0`.
