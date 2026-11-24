# Coinductive Auto-Trait Selection (`Send`/`Sync`/`Unpin`/`Freeze`), the `PhantomData<UnsafeCell<u32>>` Four-Way Asymmetry, Async Coroutine Cross-`.await` `Send` Leaks, and `zerocopy::Immutable` Soundness

## Summary

Rust's compiler (`rustc`) resolves auto traits (`Send`, `Sync`, `Unpin`, `Freeze`, and unstable `UnsafeUnpin`) through **coinductive** structural decomposition rather than purely structural reachability or syntactic field absence. Across both the classic trait solver (`compiler/rustc_trait_selection/src/traits/select/{mod.rs, candidate_assembly.rs, confirmation.rs}`) and the next-generation trait solver (`compiler/rustc_next_trait_solver/src/solve/{assembly/structural_traits.rs, trait_goals.rs, eval_ctxt/mod.rs}`), proving `X: AutoTrait` follows a five-part decision procedure whose edge interactions produce counterintuitive, yet completely deterministic, type-level separations:

1. **Coinductive cycle acceptance vs. negative-leaf rejection (`evaluate_stack` + `coinductive_match`):** Because every predicate along a recursive path of auto-trait goals satisfies `tcx.trait_is_coinductive(def_id) == true`, cyclic ADTs whose indirections propagate auto traits (such as `struct Node { val: u32, next: Option<Box<Node>> }` and mutually recursive `CycleA`/`CycleB`) accept `Send`, `Sync`, `Unpin`, and `Freeze` without divergence—while any unoverridden negative constituent leaf reachable anywhere from the cycle (such as `*const u8` blocking `Send`/`Sync`, or `UnsafeCell<u32>` blocking `Sync`/`Freeze`) refutes the entire candidate (`E0277`). By contrast, explicit `#[derive(zerocopy::Immutable)]` on `struct RecImmNode { val: u32, next: Option<Box<RecImmNode>> }` succeeds not because `zerocopy::Immutable` is coinductive (it is a non-auto unsafe trait), but because `zerocopy` provides an unconditional `unsafe impl<T: Sized> Immutable for Box<T>` (`zerocopy/src/impls.rs:306`) that terminates recursion on `Immutable` by delegating only to `Sized` (which *is* coinductive via `tcx.trait_is_coinductive`).
2. **Preemption by explicit `impl` and `unsafe` fields (`assemble_candidates_from_auto_impls` / `consider_auto_trait_candidate`):** Structural decomposition is skipped whenever `for_each_relevant_impl` finds *any* explicit positive or negative impl for the outer type's root constructor, or when an unsafe auto trait (`Send`, `Sync`, `Freeze`) meets an ADT declaring any `unsafe` field (`self_ty.has_unsafe_fields()`). Safe auto traits (`Unpin`) remain allowed on structs with `unsafe` fields unless opted out (e.g., via `PhantomPinned`).
3. **The `PhantomData<UnsafeCell<u32>>` four-way asymmetry (`Send + Freeze + zerocopy::Immutable` yet `!Sync`):**
   - For `Send`, `Sync`, and `Unpin`, `PhantomData<T>` has *no* manual override in `core::marker`, so `constituent_types_for_auto_trait` feeds `[T]` directly to the structural auto-impl rule. `UnsafeCell<u32>` is `Send` (by structural descent over `value: u32` since `core::cell` adds only `impl<T: ?Sized> !Sync for UnsafeCell<T>`) and `Unpin`, yet `!Sync` -> hence `PhantomData<UnsafeCell<u32>>` is **`Send`** and **`!Sync`**.
   - For `Freeze`, `core::marker` declares both `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` (`library/core/src/marker.rs:910`) **and** `marker_impls! { unsafe Freeze for {T: PointeeSized} PhantomData<T>, ... }` (`911-919`), preempting structural inspection of `T` -> hence `PhantomData<UnsafeCell<u32>>` is **`Freeze`** (and `Ty::is_freeze` returns `true`), whereas bare `UnsafeCell<u32>` is **`!Freeze`**.
   - For `zerocopy::Immutable`, `zerocopy/src/impls.rs:654` implements `unsafe_impl!(T: ?Sized => Immutable for PhantomData<T>)` because `PhantomData<T>` is a zero-sized type (`size_of == 0`, `align_of == 1`) with zero fields and zero runtime interior-mutable bytes -> hence `PhantomData<UnsafeCell<u32>>` (and any `#[derive(Immutable)]` struct containing it) is **`Immutable`**, whereas `UnsafeCell<u32>`, `Cell<u32>`, `ManuallyDrop<UnsafeCell<u32>>`, and `Box<[UnsafeCell<u32>]>` (`[UnsafeCell<u32>]: !Sized`) are **`!Immutable`**.
4. **Async coroutine cross-`.await` `Send` leaks (`ty::Coroutine`, `ty::CoroutineWitness`, `mir_coroutine_witnesses`):** Each `async fn` lowers to a `ty::Coroutine` with `Movability::Static` (`!Unpin`). For `Send`/`Sync`/`Freeze`, structural auto-trait checking decomposes `[tupled_upvars_ty, CoroutineWitness]`, and `CoroutineWitness` decomposes via `tcx.coroutine_hidden_types(def_id)` -> `tcx.mir_coroutine_witnesses(def_id)` over `locals_live_across_suspend_points`, keeping only locals live across at least one `TerminatorKind::Yield` and not marked `ignore_for_traits` (`StaticRef { is_thread_local: false }` or `FakeBorrow`). Consequently, a `!Send` value such as `Rc<u32>` breaks `Future: Send` iff it can remain live across `.await`; holding `UnsafeCell<u32>` or `PhantomData<UnsafeCell<u32>>` **by value** across `.await` produces a **`Send`** future, while holding `&UnsafeCell<u32>` or `&PhantomData<UnsafeCell<u32>>` across `.await` **breaks `Send`** because `unsafe impl<T: Sync + PointeeSized> Send for &T` couples `&T: Send` to `T: Sync`.
5. **Formal soundness & Anneal trusted boundary:** A standalone kernel-checked Lean `v4.34.1` development (`support/AutoTraitsCoinductiveFreezeAndImmutableSoundness.lean`, `2,246` lines, `143` theorems, `[propext]`-only with zero `sorry`, zero `Classical.choice`, zero `Quot.sound`, and zero `._unsafe_rec`) formalizes Tarski greatest-fixpoint satisfaction `CoindSat`, equivalence to visited-stack DFS `checkWithStack` and Kleene fixpoints, the four-way `PhantomData<UnsafeCell<u32>>` separation, byte-level interior-mutability freedom (`CoindSat g .immutable n` implies zero reachable inline `UnsafeCell`s including `UnsafeCell<()>` and zero mutable bytes), and exact coroutine suspend-live `Send` preservation. Separately, Anneal's MIR translation (`Trusted.MirAst.MirTy` in `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`) maps non-fieldless ADTs, `Dynamic`, `Opaque`, `Closure`, `CoroutineClosure`, and `Coroutine` to `MirTy.unsupported` (failing closed with `FaultKind.unsupported`), placing coroutine witness, `UnsafeCell`, and marker-trait verification outside Anneal's current MIR subset.

## Applicability

This report combines primary-source analysis, live `rustc` + `zerocopy` execution, and Lean `v4.34.1` kernel mechanization across the subjects recorded in `REPORT.json`:

- **`rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, released as `rustc 1.98.0-nightly`, commit date `2026-05-31`, host `x86_64-unknown-linux-gnu`, LLVM `22.1.6`) and upstream `rust-lang/rust` `master` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`):**
  - All `rustc` compiler empirical probes and `zerocopy` crate builds in `support/probe_results.json` were executed on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` in Edition `2024` (for probe binaries) and Edition `2021` (for `zerocopy`, `zerocopy_derive`, and its proc-macro dependencies).
  - Primary source analysis spans both `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and upstream `master` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`). Where code shifted between the two revisions, both are distinguished explicitly below:
    - **Classic solver (`select/mod.rs`, `candidate_assembly.rs`, `confirmation.rs`):** Identical semantics across `14210df0e` and `f7da9a423`, with small line offsets (e.g., `coinductive_match` at `1268-1284` in `14210df0e` vs. `1183-1199` in `f7da9a423`; `constituent_types_for_auto_trait` at `2317-2442` vs. `2188-2319`; `assemble_candidates_from_auto_impls` at `738-904` vs. `740-910`). Note `ty::Alias` gained a leading `IsRigid` field (moved in the next-solver integration refactor, reflected at `f7da9a423` `select/mod.rs:2226`/`2301` vs. `14210df0e` `select/mod.rs:2427`).
    - **`library/alloc/src/rc.rs` path relocation:** Resided at `library/alloc/src/rc.rs` (`320-346`) in `14210df0e` and relocated to `library/alloc/src/rcs/rc.rs` (`325-351`) on `f7da9a423`; `!Send` and `!Sync` semantics for `Rc<T, A>` are unchanged.
    - **`library/core/src/cell.rs` variance assertion:** `UnsafeCell<#[rustc_assert_variance(invariant)] T: ?Sized>` is explicit at `f7da9a423` (`cell.rs:2313`), with `impl<T: ?Sized> !Sync for UnsafeCell<T> {}` at `2318` (and `2328` in `14210df0e`).
    - **Next-generation trait solver (`compiler/rustc_next_trait_solver`):** Deep inspection of `trait_goals.rs`, `structural_traits.rs`, and `eval_ctxt/mod.rs` was performed on `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`, while `-Znext-solver` execution (`next_solver_coinductive_and_phantom_freeze_ok`) was exercised live on `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.
  - Nightly-only features exercised in specific probes: `#![feature(freeze)]` (required to name `core::marker::Freeze` directly in user code, tracking issue `#121675`), `#![feature(unsafe_fields)]` (tracking issue `#132922`, testing `has_unsafe_fields()` gating), and `-Znext-solver`. All `Send`/`Sync`/`Unpin`, `zerocopy::Immutable`, `#[derive(Immutable)]`, and `async fn` probes compile on standard Edition `2024`/`2021` without unstable language gates.
- **`google/zerocopy` (`b4c1107fa213ab01d860d6cb24a12fd0834f0df7` executed/audited, crate `zerocopy` `0.8.64`, and upstream `main` `fafea210778339d0e2b8bd14b3097c139e176e50`):**
  - Live `rustc` compilation of `zerocopy` (`0.8.64`) and `zerocopy_derive` (`0.8.64`) ran directly against the `b4c1107fa213ab01d860d6cb24a12fd0834f0df7` tree with `CARGO_PKG_VERSION=0.8.64`, `--cfg feature="alloc"`, `--cfg feature="derive"`, and `--cfg no_zerocopy_allocator_api_1_100_0` (as dictated by `[package.metadata.build-rs]` in `zerocopy/Cargo.toml:58` because `rustc 1.98.0-nightly < 1.100.0`).
  - Commit-history queries against `fafea210778339d0e2b8bd14b3097c139e176e50` confirm `zerocopy/zerocopy-derive` was last touched at `2a2de7378759cdcc2ccb9e0d4b408cf6d9126b17` (`2026-11-21`, Release `0.8.64 (#3980)`) and `zerocopy/src` was last touched at `0b2ebead393851ebd9b6af76e343eea2f6fc0cba` (`2026-11-22`, `#4065`)—both strict ancestors of `b4c1107fa213ab01d860d6cb24a12fd0834f0df7`, establishing byte-for-byte identity of `zerocopy/src` and `zerocopy/zerocopy-derive` across `b4c1107fa2` and `fafea21077`.
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
  - Inspected `trusted/rustc-capture/src/driver.rs` (`rustc 1.98.0-nightly (f8a08b688 2026-05-30)` pin) and `trusted/lean/Trusted/MirAst.lean` (`MirTy` inductive lowering rules) purely to delineate the boundary between `rustc`'s type/trait-level guarantees and what Anneal's MIR semantics currently captures vs. fails closed on.
- **`leanprover/lean4` (`v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`):**
  - Kernel type-checking and MetaM axiom/codegen auditing of `support/AutoTraitsCoinductiveFreezeAndImmutableSoundness.lean` apply specifically to Lean `v4.34.1` and prove properties of the formalized `TypeGraph` / `StepF` / `CoindSat` / `CoroutineBody` model, not of the Rust compiler's full Rust implementation itself.

## Findings

### 3.1 Auto-Trait Architecture and Explicit Standard-Library Definitions

Basis: source (`library/core/src/marker.rs`, `library/core/src/cell.rs`, `library/alloc/src/rcs/rc.rs` / `library/alloc/src/rc.rs`).

Auto traits are marker traits declared with `auto trait` (with optional `unsafe`, meaning manual `impl`s require `unsafe impl` because downstream unsafe code may rely on the trait's invariants). Four language auto traits govern concurrency, pinning, and interior mutability across `library/core/src/marker.rs` (`f7da9a423` line numbers):

| Trait | `#[lang = "..."]` | Stability & Item Attrs | Explicit Positive / Negative Standard Library Impls Inspected | Core Invariant |
| --- | --- | --- | --- | --- |
| `Send` | `send` (`L87-95`) | Stable (`1.0.0`), `pub unsafe auto trait Send` | `impl<T: PointeeSized> !Send for *const T` (`L98`), `*mut T` (`L100`); `unsafe impl<T: Sync + PointeeSized> Send for &T` (`L106`); `!Send for Rc<T, A>` (`rc.rs:338`/`L330`) | Safe transfer of ownership across thread boundaries |
| `Sync` | `sync` (`L658-670`) | Stable (`1.0.0`), `pub unsafe auto trait Sync` | `impl<T: PointeeSized> !Sync for *const T` (`L673`), `*mut T` (`L675`); `impl<T: ?Sized> !Sync for UnsafeCell<T>` (`cell.rs:2318`); `!Sync for Rc<T, A>` (`rc.rs:346`/`L338`) | Safe sharing of `&Self` across threads (`T: Sync` iff `&T: Send`) |
| `Freeze` | `freeze` (`L905-907`) | Unstable (`feature(freeze)`, `#121675`), `pub unsafe auto trait Freeze` | `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` (`L910`); `unsafe Freeze` for `PhantomData<T>`, `*const T`, `*mut T`, `&T`, `&mut T` (`L911-919`) | Absence of unindirected inline interior mutability (`UnsafeCell` values outside pointer/ref/`PhantomData` indirections) |
| `Unpin` | `unpin` (`L1014-1015`) | Stable (`1.33.0`), `pub auto trait Unpin` (safe!) | `impl !Unpin for PhantomPinned` (`L1031`); special-cased for `ty::Coroutine` in solver on `Movability` | Safe to move/replace behind `Pin<&mut Self>` |

Two architectural rules in `library/core/src/marker.rs` explain most downstream surprises:

1. **Manual positive impls override structural decomposition, whereas negative impls unconditionally block auto impls.** For example, `unsafe impl<T: Sync + PointeeSized> Send for &T` (`marker.rs:106`, comment at `L102-104`) explicitly suppresses the default structural rule (`&T: T`), coupling `&T: Send` strictly to `T: Sync` so that sending `&UnsafeCell<u32>` or `&PhantomData<UnsafeCell<u32>>` across threads is rejected even though `UnsafeCell<u32>: Send` holds! Conversely, `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` (`marker.rs:910`) blocks `Freeze` on `UnsafeCell`, while `marker_impls! { unsafe Freeze for {T: PointeeSized} PhantomData<T>, *const T, *mut T, &T, &mut T }` (`L911-919`) unconditionally grants `Freeze` regardless of `T` because none of those five types store runtime `UnsafeCell` bytes inline (though note `rustc`'s `marker_impls!` makes `PhantomData<T>`, pointers, and references `Freeze` even when `T` contains `UnsafeCell`).
2. **`PhantomData<T>` (`marker.rs:810-812`) is `#[lang = "phantom_data"] pub struct PhantomData<T: PointeeSized>;` with zero runtime fields (`size_of == 0`, `align_of == 1`, `L806-807`), yet carries syntactic type-parameter variance/ownership semantics.** Because `core::marker` provides *neither* a positive nor negative override for `PhantomData<T>: Send`, `PhantomData<T>: Sync`, or `PhantomData<T>: Unpin`, auto-trait selection falls through to `constituent_types_for_auto_trait`, which explicitly extracts `[T]`.

### 3.2 Classic Trait Solver Coinductive Auto-Trait Selection (`rustc_trait_selection`)

Basis: source (`compiler/rustc_trait_selection/src/traits/select/{mod.rs, candidate_assembly.rs, confirmation.rs}`, `compiler/rustc_middle/src/ty/trait_def.rs`).

When the classic selection context evaluates a positive trait obligation `(param_env, X: Foo)` where `self.tcx().trait_is_auto(def_id)` is true (`trait_def.rs:44-51` notes `TraitDef::is_coinductive: bool` is true whenever a trait is an auto trait or carries `#[rustc_coinductive]`):

1. **Stack Cycle Detection (`evaluate_stack`, `select/mod.rs:1106-1116`):** Before assembling candidates, `evaluate_obligation_recursively` inspects the obligation stack. If the current predicate matches an ancestor on the stack with identical explicit regions (`cycle_depth`), it collects the intermediate cycle slice `stack.iter().skip(1).take_while(|s| s.depth >= cycle_depth)` mapped via `stack.obligation.predicate.upcast(tcx)` and calls `self.coinductive_match(cycle)` (`L1183-1199`):
   ```rust
   pub(crate) fn coinductive_match<I>(&mut self, mut cycle: I) -> bool
   where
       I: Iterator<Item = ty::Predicate<'tcx>>,
   {
       cycle.all(|p| match p.kind().skip_binder() {
           ty::PredicateKind::Clause(ty::ClauseKind::Trait(data)) => {
               self.infcx.tcx.trait_is_coinductive(data.def_id())
           }
           ty::PredicateKind::Clause(ty::ClauseKind::WellFormed(_)) => {
               self.infcx.tcx.features().generic_const_exprs()
           }
           _ => false,
       })
   }
   ```
   - If `coinductive_match(cycle)` returns `true`, the recursive edge immediately returns `Some(EvaluatedToOk)` (`L1111`), encoding greatest-fixpoint (coinductive) semantics: a self-referential obligation graph succeeds unless some non-cyclic branch fails!
   - If any predicate on `cycle` is non-coinductive (such as an explicit `where` clause or trait bound on `Copy`, `Eq`, or `zerocopy::Immutable` without `#[rustc_coinductive]`), `coinductive_match` returns `false`, yielding `Some(EvaluatedToAmbigStackDependent)` (`L1114`).
2. **Candidate Assembly (`assemble_candidates_from_auto_impls`, `candidate_assembly.rs:745-908`):**
   - `let check_impls = || ...`: Calls `self.tcx().for_each_relevant_impl(def_id, self_ty, |_| has_impl = true)` (`L761-765`). **If any explicit positive or negative impl matches `self_ty`, `AutoImplCandidate` is NOT emitted.** Thus `impl<T: ?Sized> !Sync for UnsafeCell<T>`, `unsafe impl<T: PointeeSized> Freeze for PhantomData<T>`, and `unsafe impl<T: Sync + PointeeSized> Send for &T` completely preempt structural field inspection.
   - `ty::Dynamic(..)`: Adds no auto-impl candidate (`L770-775`); object types satisfy auto traits only via explicit object bounds (`dyn Trait + Send`).
   - `ty::Foreign(..)`: Adds no candidate unless `is_implicit_trait` holds for `experimental_default_bounds` (`L776-786`).
   - Rigid generics/unnormalized aliases (`Param`, `Projection`/`Inherent`/`Free` aliases, `Placeholder`, `Bound`, `L788-811`): Add no auto candidate; must be satisfied via `param_env` assumptions.
   - Inference variables (`TyVar`/`IntVar`/`FloatVar`, `L812-815`): Mark `candidates.ambiguous = true`.
   - `ty::Coroutine(coroutine_def_id, _)` (`L816-837`):
     * For `LangItem::Unpin`: `Movability::Static` emits **no candidate** (`!Unpin`); `Movability::Movable` emits `BuiltinCandidate` unconditionally (`Unpin` with zero sub-obligations).
     * For all other auto traits (`Send`, `Sync`, `Freeze`): calls `self.should_stall_coroutine(coroutine_def_id)` (`select/mod.rs:2796-2810`). During `TypingMode::Typeck` on locally stalled generators whose witness layout isn't finalized yet, it marks `candidates.ambiguous = true` to avoid premature query cycles; post-typeck or non-stalled, it emits `AutoImplCandidate`.
   - `ty::Alias(..., Opaque { def_id })` (`L846-867`): If inside the defining scope (`can_define_opaque_ty(def_id)`), marks `candidates.ambiguous = true` so hidden types are not leaked prematurely; outside the defining scope, emits `AutoImplCandidate` (provided no `ProjectionCandidate` already exists on the opaque item bounds).
   - `ty::CoroutineWitness(..)` (`L869-871`): Unconditionally emits `AutoImplCandidate`.
   - `ty::Adt`, primitives, pointers, refs, arrays, tuples, closures, etc. (`L873-901`):
     * **Unsafe-field suppression gate (`L894-898`):**
       ```rust
       if self.tcx().trait_def(def_id).safety.is_unsafe()
           && self_ty.has_unsafe_fields()
       {
           return;
       }
       ```
       (`Ty::has_unsafe_fields` in `compiler/rustc_middle/src/ty/util.rs:1281-1287` returns `adt_def.all_fields().any(|x| x.safety.is_unsafe())`.) Therefore, an ADT containing any `unsafe` field suppresses `Send`, `Sync`, and `Freeze` (all `unsafe auto trait`s), while **allowing** `Unpin` (a safe `auto trait`)!
     * Otherwise calls `check_impls()`.
3. **Constituent Type Extraction and Confirmation (`confirm_auto_impl_candidate` in `confirmation.rs:325-367` -> `constituent_types_for_auto_trait` in `select/mod.rs:2188-2319`):**
   Once `AutoImplCandidate` wins selection, `confirm_auto_impl_candidate` calls `self.constituent_types_for_auto_trait(self_ty)` and maps each constituent type `Y` to a child predicate `(param_env, Y: AutoTrait)` via `collect_predicates_for_types` (and for `-Zhigher-ranked-assumptions`, registers normalized region outlives assumptions from `constituents.assumptions`). Exact constituent mappings in `constituent_types_for_auto_trait`:
   - Primitives (`Uint`, `Int`, `Bool`, `Float`, `FnDef`, `FnPtr`, `Error`, `IntVar`/`FloatVar`, `Never`, `Char`, `Foreign`): `types = []`.
   - `ty::Str`: `[u8]` (`Ty::new_slice(tcx, tcx.types.u8)`).
   - `ty::RawPtr(elem, _)` / `ty::Ref(_, elem, _)` / `ty::Pat(elem, _)` / `ty::Array(elem, _)` / `ty::Slice(elem)` / `ty::UnsafeBinder(elem)`: `[elem]` (only reached when no explicit impl exists; thus `&T` skips `Send` via `unsafe impl Send for &T`, falls through for `Sync` -> `[elem]`, and skips `Freeze`/`Unpin` if overridden).
   - `ty::Tuple(tys)`: `tys.iter().collect()`.
   - `ty::Closure` / `ty::CoroutineClosure`: `[tupled_upvars_ty]`.
   - `ty::Coroutine(def_id, args)`: `[tupled_upvars_ty, Ty::new_coroutine_witness_for_coroutine(tcx, def_id, args)]` (`L2267-2275`).
   - `ty::CoroutineWitness(def_id, args)`: `tcx.coroutine_hidden_types(def_id).instantiate(tcx, args)` (`L2277-2286`).
   - **`ty::Adt(def, args) if def.is_phantom_data()` (`L2289-2294`):** Explicitly special-cased! Even though `PhantomData<T>` has zero fields (`def.all_fields()` is empty), `def.is_phantom_data()` returns `args.types().collect()` -> **`[T]`**!
   - General `ty::Adt(def, args)` (`L2296-2299`): `def.all_fields().map(|f| f.ty(tcx, args).skip_norm_wip()).collect()` (all fields across all variants for enums, structs, unions). Notice `Box<T>` carries an explicit heap-pointer abstraction in `alloc` that propagates `Send`/`Sync`/`Unpin`/`Freeze` to `T` (verified live on `Node`/`CycleA`/`CycleB`), which is why `Box<Node>` introduces a coinductive auto-trait cycle on `Node`.
   - `ty::Alias(..., ty::Opaque { def_id })` (`L2301-2314`): Resolves `[tcx.type_of_opaque(def_id).instantiate(tcx, args)]` when outside defining scope.

### 3.3 Next-Generation Trait Solver Parity (`-Znext-solver`)

Basis: source (`compiler/rustc_next_trait_solver/src/solve/{trait_goals.rs, assembly/structural_traits.rs, eval_ctxt/mod.rs}` at `f7da9a423`) + execution (`probe_results.json` `next_solver_coinductive_and_phantom_freeze_ok`).

The next-generation trait solver preserves the exact same coinductive and constituent-type matrix:

1. **Candidate Guard (`consider_auto_trait_candidate`, `trait_goals.rs:194-260`):**
   - Rejects negative-polarity goals (`goal.predicate.polarity != ClausePolarity::Positive`, `L199-201`).
   - Calls `disqualify_auto_trait_candidate_due_to_possible_impl(goal)` (`L216-218`) to mirror `check_impls` preemption when any explicit positive or negative impl may match `self_ty`.
   - Enforces the identical unsafe-field gate: `if cx.trait_is_unsafe(goal.predicate.def_id()) && goal.predicate.self_ty().has_unsafe_fields() { return Err(NoSolution.into()); }` (`L222-226`).
   - Handles opaque types (`consider_auto_trait_candidate_for_opaque_ty`, `L243-248`) and stalled coroutines (`try_stall_coroutine`, `L251-253`), then invokes `probe_and_evaluate_goal_for_constituent_tys` with `instantiate_constituent_tys_for_auto_trait` (`L255-259`).
2. **Constituent Extraction (`instantiate_constituent_tys_for_auto_trait`, `structural_traits.rs:24-114`):** Matches the classic solver arm-by-arm, mapping `ty::Coroutine` -> `[tupled_upvars_ty, witness]` (`L87-90`), `ty::CoroutineWitness` -> `coroutine_hidden_types` (`L92-97`), `ty::Adt` with `def.is_phantom_data()` -> `[args.type_at(0)]` (`L102`), and general `ty::Adt` -> instantiated `all_field_tys` (`L104-109`). (Notice `CoroutineWitness` in `structural_traits.rs:92-97` maps `.map_bound(|bound| bound.types.to_vec())`, without classic's `-Zhigher-ranked-assumptions` registration branch in `confirmation.rs:349-364`.)
3. **Coinductive Cycle Classification (`eval_ctxt/mod.rs:59-95, 436-451`):**
   - `CurrentGoalKind::from_query_input` classifies trait goals with `cx.trait_is_coinductive(pred.trait_ref.def_id)` as `CurrentGoalKind::CoinductiveTrait` (`L88-89`).
   - `step_kind_to_nested` maps `CurrentGoalKind::CoinductiveTrait` to **`PathKind::Coinductive`** (`L440`), whereas `CurrentGoalKind::Misc` returns `PathKind::ForcedAmbiguity` (`L449`), and projections return `PathKind::Unknown` (`L443-445`).
4. **Live Verification:** Compiling our entire coinductive cycle + `*const u8` + `UnsafeCell<u32>` + `PhantomData<UnsafeCell<u32>>` + `PhantomData<*const u8>` suite with `rustc --edition=2024 -Znext-solver` compiles with exit code `0` and runs printing `AUTO_OK=1` (`probe_results.json`, `next_solver_coinductive_and_phantom_freeze_ok`).

### 3.4 `Ty::is_freeze`, `is_trivially_freeze`, and `is_freeze_raw`

Basis: source (`compiler/rustc_middle/src/ty/util.rs`, `compiler/rustc_ty_utils/src/common_traits.rs`) + execution.

In MIR codegen, const evaluation (`const_eval`), aliasing attributes (`noalias` metadata), and promotion (`promotable`), `rustc` tests immutability modulo interior mutability via `Ty::is_freeze(self, tcx, typing_env)` (`ty/util.rs:1184-1186`):

```rust
pub fn is_freeze(self, tcx: TyCtxt<'tcx>, typing_env: ty::TypingEnv<'tcx>) -> bool {
    self.is_trivially_freeze() || tcx.is_freeze_raw(typing_env.as_query_input(self))
}
```

- **Fast path (`Ty::is_trivially_freeze`, `util.rs:1192-1225`):** Returns `true` immediately without entering the trait solver for `Int`, `Uint`, `Float`, `Bool`, `Char`, `Str`, `Never`, `Ref`, `RawPtr`, `FnDef`, `Error`, `FnPtr`, and recursively for `Tuple`, `Pat`, `Slice`, and `Array`. Returns `false` conservatively for `Adt`, `Bound`, `Closure`, `CoroutineClosure`, `Dynamic`, `Foreign`, `Coroutine`, `CoroutineWitness`, `UnsafeBinder`, `Infer`, `Alias`, `Param`, and `Placeholder`.
- **Trait-solver fallback (`is_freeze_raw`, `common_traits.rs:25-27, 47-56`):** Calls `is_trait_raw(tcx, query, LangItem::Freeze)`, which creates an infcx ignoring regions and runs `traits::type_known_to_meet_bound_modulo_regions(&infcx, param_env, query.value, trait_def_id)`.
- **Consequence for `PhantomData<UnsafeCell<u32>>` vs. `UnsafeCell<u32>`:** Neither is trivially `Freeze` (both are `ty::Adt`), so `is_freeze` falls back to `is_freeze_raw` -> `LangItem::Freeze` solver check:
  - `UnsafeCell<u32>` hits `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` (`marker.rs:910`) -> **`is_freeze == false`**.
  - `PhantomData<UnsafeCell<u32>>` hits `unsafe impl<T: PointeeSized> Freeze for PhantomData<T>` (`marker.rs:914`) -> **`is_freeze == true`**, meaning a static or `const`-promoted binding holding `PhantomData<UnsafeCell<u32>>` can live in read-only memory (`.rodata`) safely!

### 3.5 The `PhantomData<UnsafeCell<u32>>` Four-Way Asymmetry and Trait Matrix

Basis: source + execution (`probe_results.json` parts A & B) + Lean mechanization (`asymmetryGraph` / `cycleGraph` theorems).

Combining all four auto traits (`Send`, `Sync`, `Unpin`, `Freeze`) with `zerocopy::Immutable` reveals sharp, independent separations across standard type constructors. Unparenthesized `yes`/`no` cells were directly compiled and executed on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`support/probe_results.json`); parenthesized cells denote properties derived from the inspected `library/core`, `compiler/rustc_*`, and `zerocopy/src/impls.rs` source rules (and checked in Lean `cycleGraph`/`asymmetryGraph`):

| Type `T` | `Send` | `Sync` | `Unpin` | `Freeze` | `zerocopy::Immutable` | Governing Mechanism (`rustc` / `zerocopy`) |
| --- | :---: | :---: | :---: | :---: | :---: | --- |
| `u32` (primitives) | (`yes`) | (`yes`) | (`yes`) | (`yes`) | (`yes`) | Empty constituents `[]`; `zerocopy::Immutable` primitive impl (also verified inline in `Node`/`HasPhantomCell`) |
| `Node` (`u32`, `Option<Box<Node>>`) | `yes` | `yes` | `yes` | `yes` | `yes` (`RecImmNode`) | Auto traits via coinduction (`coinductive_match`); `#[derive(Immutable)]` on `RecImmNode` terminates via `Box<T: Sized>: Immutable` + `RecImmNode: Sized` (coinductive) |
| `CycleA` <-> `CycleB` via `Option<Box<_>>` | `yes` | `yes` | (`yes`) | `yes` | (`yes`) | Mutual auto-trait cycle accepted by `coinductive_match`; (`Immutable` derive applies identically via `Box<T: Sized>`) |
| `BadNode` (`Box<BadNode>`, `*const u8`) | `no` | (`no`) | (`yes`) | (`yes`) | (`yes`) | Cycle cannot mask `*const u8` `!Send`/`!Sync` leaf (`E0277` on `Send`) |
| `CellNode` (`UnsafeCell<u32>`, `Box<CellNode>`) | (`yes`) | `no` | (`yes`) | (`no`) | (`no`) | Executed `!Sync` rejection (`E0277`); `UnsafeCell<u32>: Send` while blocking `Sync`/`Freeze`/`Immutable` |
| `*const u8` (`HasRaw`) / `*const UnsafeCell<u32>` | `no` | `no` | `yes` | `yes` | `yes` (`*const UnsafeCell<u32>`) | `!Send`/`!Sync` (`marker.rs:98, 673`); `unsafe Freeze` (`L915`); `unsafe_impl!(Immutable for *const T)` (`impls.rs:966`) |
| `PhantomData<*const u8>` (`HasPhantomRaw`) | `no` | (`no`) | `yes` | `yes` | (`yes`) | Constituent `[*const u8]` blocks `Send` (`E0277`) / `Sync`, `unsafe Freeze` (`L914`) and `Immutable` (`impls.rs:654`) hold |
| `UnsafeCell<u32>` (`HasCell`) | `yes` | `no` | `yes` | `no` | `no` | `!Sync` (`cell.rs:2318`), `!Freeze` (`marker.rs:910`), omits `Immutable` (`impls.rs:839-868`); `Send` via field `u32` |
| `ManuallyDrop<UnsafeCell<u32>>` | (`yes`) | (`no`) | (`yes`) | (`no`) | `no` | `UnsafeCell` field blocks `Immutable` (`E0277` `UnsafeCell<u32>: Immutable not satisfied`) |
| `Box<UnsafeCell<u32>>` | (`yes`) | (`no`) | (`yes`) | (`yes`) | `yes` | Pointer indirection + `T: Sized => Immutable for Box<T>` (`impls.rs:306`); live compiled `assert_imm::<Box<UnsafeCell<u32>>>()` (`ZC_PHANTOM_CELL_IMMUTABLE_OK=1`) |
| `Box<[UnsafeCell<u32>]>` | (`yes`) | (`no`) | (`yes`) | (`yes`) | `no` | `[UnsafeCell<u32>]: !Sized` fails `T: Sized` bound on `Box<T>: Immutable` (`E0277`, `impls.rs:306`, test `L2223`) |
| **`PhantomData<UnsafeCell<u32>>`** | **`yes`** | **`no`** | **`yes`** | **`yes`** | **`yes`** | **Four-way asymmetry:** `[UnsafeCell<u32>]` constituent makes `Send=yes, Sync=no`; explicit `unsafe Freeze` (`marker.rs:914`) & `Immutable` (`impls.rs:654`) ignore `UnsafeCell<u32>` |
| **`HasPhantomCell`** (`#[derive(Immutable)]`, `u32`, `PhantomData<UnsafeCell<u32>>`) | **`yes`** | **`no`** | **`yes`** | **`yes`** | **`yes`** | Inherits four-way separation verbatim: `Send + Freeze + Immutable` pass live (`ZC_DERIVE_IMMUTABLE_OK=1`), `Sync` rejected (`E0277`) |
| `WithUnsafeField { unsafe secret: u32 }` | `no` | (`no`) | `yes` | (`no`) | (`not examined`) | `has_unsafe_fields()` blocks unsafe `Send`/`Sync`/`Freeze` (`E0277` on `Send`), permits safe `Unpin` (`UNSAFE_FIELD_UNPIN_OK=1`) |
| `Rc<u32>` | `no` | (`no`) | (`yes`) | (`yes`) | (`not examined`) | Explicit `!Send` (observed in `async fn` `E0277`) & `!Sync` (`rc.rs:338, 346` / `14210df0e:330, 338`) |

Why does `PhantomData<UnsafeCell<u32>>` sit at this exact intersection?
- `Send` and `Sync` care about whether owning or sharing a wrapper implies thread-safety obligations (and conceptually `PhantomData<T>` signals logical ownership/aliasing properties for `T` — though `#[lang = "phantom_data"]` transmits `[T]` symmetrically to all unoverridden auto traits, which makes `PhantomData<UnsafeCell<u32>>: !Sync` while `*const UnsafeCell<u32>` and `&UnsafeCell<u32>` are governed by manual impls).
- `Freeze` and `zerocopy::Immutable` both answer a *byte-level runtime* question ("do shared references to a value of this type permit interior mutation of its owned memory?"): `UnsafeCell<u32>` owns `4` interior-mutable bytes (or for `UnsafeCell<()>`, an inline interior-mutability node capable of tainting references to sibling/containing bytes or `UnsafePinned`), whereas `PhantomData<UnsafeCell<u32>>` occupies `0` bytes and owns `0` values. Therefore `PhantomData<UnsafeCell<u32>>` *must* be `Freeze` and `zerocopy::Immutable`, even though `Sync` rejects it!

### 3.6 Async Coroutine Witness Layout and Cross-`.await` `Send` Leaks

Basis: source (`compiler/rustc_mir_transform/src/coroutine/layout.rs`, `compiler/rustc_traits/src/coroutine_witnesses.rs`, `select/{mod.rs, candidate_assembly.rs}`) + execution (`probe_results.json` part C) + Lean mechanization (`Part 6`).

When `rustc` lowers an `async fn` into a state machine (`ty::Coroutine(def_id, args)` with `Movability::Static`):

1. **Suspension Liveness (`locals_live_across_suspend_points`, `coroutine/layout.rs:83-184`):**
   - Computes `MaybeStorageLive`, `MaybeBorrowedLocals`, `MaybeRequiresStorage`, and `MaybeLiveLocals`.
   - At every `TerminatorKind::Yield { .. }` (`L113-114`), takes `liveness` (`live_locals`), and crucially when `!movable` (true for every `async fn`!):
     `live_locals.union(borrowed_locals_cursor.get())` (`L121-134`), conservatively keeping any previously borrowed local alive until its `StorageDead` because borrows can span `.await` in immovable coroutines!
   - Intersects with `requires_storage_cursor` (`L144-145`) and removes `SELF_ARG` (`L148`).
   - Unions across all `Yield` terminators into `live_locals_at_any_suspension_point` (`L154, 161`).
2. **Trait-Ignore Filtering (`coroutine/layout.rs:360-392` and `coroutine_witnesses.rs:12-44`):**
   - Each saved local sets `ignore_for_traits` (`L372-382`) to `true` **only** for `LocalInfo::StaticRef { is_thread_local: false, .. }` (non-thread-local `static` references that can be reconstructed cleanly) and `LocalInfo::FakeBorrow` (MIR borrow-checker artifact without runtime storage). Every normal user local (`Rc`, `UnsafeCell`, `&T`, guards) has `ignore_for_traits == false`.
   - `mir_coroutine_witnesses` (`coroutine/layout.rs:462-493`) computes and returns `Some(CoroutineLayout)`.
   - `coroutine_hidden_types` (`coroutine_witnesses.rs:12-44`) reads `tcx.mir_coroutine_witnesses(def_id)`, filters `.filter(|decl| !decl.ignore_for_traits)` (`L22`), replaces erased regions `re_erased` with fresh anonymous higher-ranked bound regions (`L24-33`), and computes region assumptions `compute_assumptions`.
3. **Auto-Trait Evaluation (`candidate_assembly.rs:816-837, 869-871`; `select/mod.rs:2267-2286`):**
   - `Send` / `Sync` / `Freeze` on `ty::Coroutine(def_id, args)` decompose into `[tupled_upvars_ty, CoroutineWitness(def_id, args)]`, and `CoroutineWitness` unfolds to the `coroutine_hidden_types` type list!
   - `Unpin` on `ty::Coroutine` is special-cased in `candidate_assembly.rs:817-828`: `Movability::Static` emits zero candidates -> every `async fn` is strictly `!Unpin`, confirmed live (`async_static_coroutine_not_unpin_e0277`, `E0277: {async fn body of triv()} cannot be unpinned`).
4. **Live Empirically Discriminated Cases (`probe_results.json` Part C):**
   - `Rc<u32>` held across `yield_now().await` -> **Rejected (`compile_returncode = 1`)**: `note: future is not Send as this value is used across an await`.
   - `Rc<u32>` scoped in `{ let rc = Rc::new(1u32); ... }` and dropped *before* `yield_now().await` -> **Accepted (`ASYNC_SEND_OK=1`)**: `rc` is dead (`StorageDead`) at the `Yield` point, so it is excluded from `live_locals_at_any_suspension_point`.
   - `UnsafeCell<u32>` and `PhantomData<UnsafeCell<u32>>` held **by value** across `.await` -> **Accepted (`ASYNC_CELL_VAL_SEND_OK=1`)**: both implement `Send`.
   - `&UnsafeCell<u32>` or `&PhantomData<UnsafeCell<u32>>` held across `.await` -> **Rejected (`compile_returncode = 1`)**: both diagnostics pinpoint `trait Sync is not implemented for UnsafeCell<u32>` (`async_ref_cell_err`, `async_ref_phantom_err`), confirming how `unsafe impl<T: Sync + PointeeSized> Send for &T` makes cross-`.await` shared borrows of `PhantomData<UnsafeCell<u32>>` leak `!Send` even though owning `PhantomData<UnsafeCell<u32>>` by value across `.await` is `Send`!

### 3.7 `zerocopy::Immutable` Architecture, `#[derive(Immutable)]`, and Interior-Mutability Soundness

Basis: source (`zerocopy/src/lib.rs`, `zerocopy/src/impls.rs`, `zerocopy/zerocopy-derive/src/derive/mod.rs`) + execution (`probe_results.json` part B) + Lean mechanization (`Part 5`).

1. **Normative Safety Contract & Sealed Method (`zerocopy/src/lib.rs:1700-1738`):**
   - `pub unsafe trait Immutable` exposes a hidden method `fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized;` (`L1735-1737`) so downstream crates cannot implement it safely without `#[derive(Immutable)]`, while keeping `where Self: Sized` so `dyn` / unsized usage remains object-safe / compatible.
   - Internal safety contract (`L1710-1714`): *"If `T: Immutable`, unsafe code inside of this crate may assume that, given `t: &T`, `t` does not permit interior mutation of its referent. Because `UnsafeCell` is the only type which permits interior mutation, it is sufficient (though not necessary) to guarantee that `T` contains no `UnsafeCell`s."*
   - The phrase `"contains no UnsafeCells"` applies strictly to inline, directly owned bytes of `Self`, not behind heap pointers, references, or zero-sized `PhantomData` markers (`impls.rs`):
     * `impls.rs:839-868`: `UnsafeCell<T>` implements `FromZeros`, `FromBytes`, `IntoBytes`, `Unaligned`, and `TryFromBytes` (`T::is_safe(candidate.transmute::<_, _, BecauseImmutable>())`), and **deliberately omits `Immutable`** (as does `Cell<T>`, which only receives `Unaligned` at `impls.rs:837`). Live probes confirm `UnsafeCell<u32>`, `Cell<u32>`, `ManuallyDrop<UnsafeCell<u32>>`, and `#[derive(Immutable)] struct BadDerivedCell { val: u32, cell: UnsafeCell<u8> }` all fail with `E0277`.
     * `impls.rs:654`: `unsafe_impl!(T: ?Sized => Immutable for PhantomData<T>)` ("`PhantomData` has no fields", `L645`), verified live both directly (`assert_imm::<PhantomData<UnsafeCell<u32>>>()`) and via `#[derive(Immutable)] struct HasPhantomCell` (`ZC_DERIVE_IMMUTABLE_OK=1`).
     * `impls.rs:966-990`: `*const T`, `*mut T`, `NonNull<T>`, `&'_ T`, and `&'_ mut T` unconditionally implement `Immutable` for `T: ?Sized` (verified live for `*const UnsafeCell<u32>` and `&UnsafeCell<u32>`), because a pointer or reference value itself occupies immutable pointer bytes—`&UnsafeCell<u32>` permits mutating through the *pointee*, not mutating the shared reference value behind `&&UnsafeCell<u32>`.
     * **`Box<T>` sizing boundary (`impls.rs:304-308`, test `L2222-2223`):** `T: Sized => Immutable for Box<T>`! Live probes confirm `Box<UnsafeCell<u32>>: Immutable` **succeeds**, whereas `Box<[UnsafeCell<u32>]>: Immutable` **fails `E0277: the size for values of type [UnsafeCell<u32>] cannot be known at compilation time`** (even though neither pointer stores inline `UnsafeCell` bytes, `Box<T>` omits unsized `T` conservatively per `#1358`).
2. **`#[derive(Immutable)]` and Coinductive Cycle Termination (`zerocopy-derive/src/derive/mod.rs:19-31`):**
   - `derive_immutable` calls `ImplBlockBuilder::new(ctx, ..., Trait::Immutable, FieldBounds::ALL_SELF).build()`, emitting field bounds checking that every field type implements `Immutable`.
   - Even though `Immutable` is **not** a coinductive auto trait (`#[rustc_coinductive]` is absent), `#[derive(Immutable)]` on `struct RecImmNode { val: u32, next: Option<Box<RecImmNode>> }` compiles cleanly (`ZC_DERIVE_IMMUTABLE_OK=1`) because:
     1. Field `val: u32` -> `u32: Immutable` (trivial).
     2. Field `next: Option<Box<RecImmNode>>` -> `Option<T>: Immutable` requires `T: Immutable` (`impls.rs:990`), i.e., `Box<RecImmNode>: Immutable`.
     3. **`Box<T>: Immutable` (`impls.rs:306`) requires ONLY `RecImmNode: Sized`, NOT `RecImmNode: Immutable`!** And `Sized` IS coinductive in `rustc` (`select/mod.rs:1179`), discharging the `Box<RecImmNode>` cycle immediately without ever generating a cyclic `RecImmNode: Immutable` sub-obligation!
   - By contrast, any cycle where `Immutable` itself recurs without breaking via a `T: Sized` / `T: ?Sized` indirection (such as direct cyclic `Immutable` obligation without `Box`/`&`/`PhantomData`) hits non-coinductive cycle rejection (`coinductive_match` returns `false`, `LoopImmStruct` in Lean `Theorem 1c`).
3. **Anneal Trusted Verification Boundary (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
   - Anneal's compiler capture binary (`trusted/rustc-capture/src/driver.rs:25, 75-84`) pins `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` and inspects clean post-analysis MIR.
   - Its target MIR type AST (`trusted/lean/Trusted/MirAst.lean:295-321`) encodes `.bool`, `.int`, `.unit`, `.never`, fieldless `.enum`, `.tuple`, `.ref`, `.rawPtr`, and maps **every non-fieldless ADT** (`UnsafeCell`, `PhantomData`, `Box`, `Rc`, `ManuallyDrop`), `Dynamic`, `Opaque`, `Closure`, `CoroutineClosure`, and `Coroutine` to **`MirTy.unsupported`**, causing the operational semantics $M_{\text{anneal}}$ to fail closed with `FaultKind.unsupported`. Consequently, Anneal's MIR formalization does not yet reason about `UnsafeCell` aliasing, `PhantomData` zero-sized invariants, or `async fn` coroutine state machines; proofs in downstream crates (such as `zerocopy`'s `Immutable` markers) rely on the `rustc` + `zerocopy` soundness properties analyzed here when outside Anneal's supported scalar/reference MIR fragment.

### 3.8 Kernel-Checked Lean `v4.34.1` Formalization

Basis: source + kernel verification (`support/AutoTraitsCoinductiveFreezeAndImmutableSoundness.lean`, `2,246` lines, `143` theorems, `[propext]` only, `0` `_unsafe_rec`).

To verify the algebraic structure of these rules independently of prose reasoning, `support/AutoTraitsCoinductiveFreezeAndImmutableSoundness.lean` formalizes:
- **Unified predicate & type graph (`AutoTrait`, `TraitPred`, `NodeKind`, `TypeGraph`):** Models all four auto traits (`send`, `sync`, `unpin`, `freeze`) alongside non-coinductive `immutable` over 12 `NodeKind` constructors (`prim`, `rawPtr`, `refShared`, `refMut`, `boxPtr`, `rcPtr`, `unsafeCell`, `phantomData`, `phantomPinned`, `adtStruct` with `hasUnsafe`, `negAuto`, and `immImpl`, `rpitOpaque`, and `dynObj`).
- **Tarski greatest-fixpoint semantics & DFS/Kleene equivalence (Parts 2–3):**
  - `StepF` and `StepF_mono` (monotone one-step operator), `IsPostFixed`, and impredicative `CoindSat g tr n := ∃ P, IsPostFixed g P ∧ P tr n` (`coindSat_greatest`, `coindSat_iff_step`) requiring zero classical axioms.
  - `coindSat_rejects_reachable_negative_leaf` (**Theorem 1a**): any reachable `IsDirectNegativeAuto` leaf along `AutoReach` refutes `CoindSat g (.auto a₀) root` regardless of coinductive cycles elsewhere.
  - Structural visited-stack solver `checkWithStack` and witness collector `checkAndCollectList` (decomposed structurally via `checkListWithStep` over `Nat` and `List`), with `checkWithStack_sound` (**Theorem 1b**: `checkWithStack = true → CoindSat`) and `checkWithStack_inductive_cycle_fails` (**Theorem 1c**: visited `.immutable` cycles always return `false`), plus finite-graph Kleene fixpoint soundness and completeness `kleeneGfp_iff_coindSat`.
- **Concrete Cycle & Four-Way Separation Witnesses (Part 4):**
  - `node_cycle_coindSat_all` and `mutual_cycle_coindSat_send_sync` establish cyclic acceptance of `Node` (`Option<Box<Node>>`) and `CycleA`/`CycleB`; `bad_node_cycle_rejects_send_and_sync` rejects `BadNode` (`*const u8` sibling); `cell_node_send_yet_not_sync_not_freeze` separates `Send` from `!Sync` + `!Freeze` on `CellNode`; `loop_imm_rejected_by_dfs_stack` verifies non-coinductive cycle rejection for `Immutable`.
  - `phantom_unsafecell_four_way_separation` (**Theorem 2a**) and `has_phantom_cell_four_way_separation` (**Theorem 2b**) prove `(CoindSat ... (.auto .send) ∧ CoindSat ... (.auto .freeze) ∧ CoindSat ... .immutable ∧ ¬ CoindSat ... (.auto .sync))` on both bare `PhantomData<UnsafeCell<u32>>` and struct `HasPhantomCell`.
  - Companion rows (`unsafecell_matrix_row`, `raw_ptr_and_phantom_raw_matrix_rows`, `rc_matrix_row`, `box_sized_vs_unsized_unsafecell`, `unsafe_field_and_negative_impl_discrimination`, `asymmetry_kleene_converges_at_3`) complete the full kernel-checked discrimination matrix.
- **Byte-Level Interior-Mutability Freedom (Part 5):**
  - `ownedFootprint` maps runtime inline storage to lists of `ByteCellKind` (`.immutableByte` vs. `.interiorMutByte`), giving `unsafeCell` `sz` mutable bytes and giving `phantomData` / pointer indirections `[]` or immutable pointer bytes.
  - `coindSat_immutable_implies_no_inline_unsafecell` (**Theorem 3a**) proves that `CoindSat g .immutable n` excludes all inline `ReachableInlineUnsafeCell` paths (even zero-sized `UnsafeCell<()>`!).
  - `coindSat_immutable_implies_all_bytes_immutable` and `coindSat_immutable_implies_zero_unsafecell_bytes` (**Theorem 3b**) prove for every node with `HasFiniteInlineLayout g n depth` that `CoindSat g .immutable n` guarantees every owned byte is `.immutableByte` (`unsafeCellByteCount g depth n = 0`), with concrete separation `zst_unsafecell_fails_immutable_while_phantom_passes`.
- **Async Coroutine Suspend-Live Preservation (Part 6):**
  - `witnessLocals` models `liveAcrossAnyAwait && !ignoreForTraits`; `CoroutineImplementsAuto` models `Movability::Static` `!Unpin` plus upvar and witness `CoindSat`.
  - `async_coroutine_send_iff_live_across_await_send` (**Theorem 4a**), `async_dead_non_send_local_preserves_send` (**Theorem 4b**), `async_live_rc_across_await_breaks_send` (**Theorem 4c**), `async_unsafecell_value_send_vs_ref_not_send` (**Theorem 4d**), and `async_static_not_unpin` (**Theorem 4e**) mechanize the exact cross-`.await` ownership vs. `&`-borrowing asymmetry.

## Boundaries

- **`UnsafePinned<T>` and `UnsafeUnpin` (`marker.rs:927-929`, RFC 3467):** *not examined* in empirical `rustc` probes or modeled as a distinct `NodeKind` in Lean (`support/AutoTraitsCoinductiveFreezeAndImmutableSoundness.lean` models `PhantomPinned` and `UnsafeCell`, not `UnsafePinned` alias/immovability subtleties).
- **Direct `CoindSat` negative proof for non-coinductive cycle `LoopImmStruct`:** *unknown / model-specific* — our Lean `CoindSat` is a greatest fixpoint of `StepF` even on `.immutable`, whereas `rustc` and our executable solver `checkWithStack` distinguish coinductive vs. inductive cycles via `isCoinductivePred` (`checkWithStack_inductive_cycle_fails` proves `checkWithStack` rejects `LoopImmStruct: Immutable`, while greatest-fixpoint `CoindSat` itself models structural coinduction for `StepF`). Notice that for all *finite-inline-layout* ADTs (`RecImmNode` breaks its cycle on `Box` + `Sized`, while non-`Box` inline `struct Loop(Loop)` is already illegal in Rust with `E0072` infinite size), `HasFiniteInlineLayout` guarantees finite inline termination.
- **Unexamined cells in the `3.5` trait matrix:** Combinations marked in parentheses in Table `3.5` (such as `CellNode: Freeze`, `ManuallyDrop<UnsafeCell<u32>>: Freeze`, `Box<UnsafeCell<u32>>: Freeze`, `Rc<u32>: Unpin`/`Freeze`, `WithUnsafeField: Immutable`) were *derived* from inspected `rustc`/`zerocopy` source rules or explicitly *not examined* via standalone `rustc` executions in `probe_results.json`; only unparenthesized `yes`/`no` cells were directly executed in `probe_results.json` or verified in Lean `asymmetryGraph`/`cycleGraph`.
- **`std::pin` & generator `-Zhigher-ranked-assumptions` interactions:** *not examined* empirically (`confirmation.rs:349-364` passes `-Zhigher-ranked-assumptions` from `CoroutineWitness` assumptions to `register_region_assumption`, whereas `structural_traits.rs:92-97` in the next solver does not extract `assumptions`).
- **`zerocopy::Immutable` with `zerocopy` `0.8.64` feature `std` / `simd` / `float-nightly`:** *not examined* beyond `alloc` and `derive` (`libzerocopy.rlib` was built with `--cfg feature="alloc"`, `--cfg feature="derive"`, `--cfg no_zerocopy_allocator_api_1_100_0`).
- **Compiler versions outside `14210df0e` (`1.98.0-nightly`) and `f7da9a423` (`master`):** *unknown / not assumed* without revalidation; however, exact path equality on `zerocopy/src` and `zerocopy/zerocopy-derive` was confirmed across `b4c1107fa2` and `fafea21077`, and primary-source logic in `select/mod.rs`, `candidate_assembly.rs`, and `marker.rs` matches across `14210df0e` and `f7da9a423` except for shifted line offsets, `library/alloc/src/rcs/rc.rs` relocation, and `ty::Alias(..., IsRigid, ...)` factoring.
- **Anneal MIR (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** *unsupported* for `UnsafeCell`, `PhantomData`, `Box`, `Rc`, `Coroutine`, `Closure`, `Opaque`, and `Dynamic` types (`MirTy.unsupported` in `Trusted/MirAst.lean:308-321`), which fail closed rather than attempting auto-trait or interior-mutability proofs.

## Evidence

### 5.1 Primary Source Anchors

| Subject & Revision | File | Symbol / Construct | Line Range | Role |
| --- | --- | --- | --- | --- |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_trait_selection/src/traits/select/mod.rs` | `evaluate_obligation_recursively` stack cycle check & `coinductive_match` | `1106-1116`, `1183-1199` | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_trait_selection/src/traits/select/mod.rs` | `constituent_types_for_auto_trait` (`Coroutine`, `CoroutineWitness`, `PhantomData`, `Adt`, `Opaque`) | `2188-2319` (`2267-2314`) | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_trait_selection/src/traits/select/mod.rs` | `should_stall_coroutine` | `2796-2810` | Source |
| `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) | `compiler/rustc_trait_selection/src/traits/select/mod.rs` | `coinductive_match`, `constituent_types_for_auto_trait` | `1268-1284`, `2393-2442` | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs` | `assemble_candidates_from_auto_impls` (`check_impls`, `Coroutine`/`Unpin`, `has_unsafe_fields`) | `745-910` (`751-766`, `816-837`, `894-898`) | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_trait_selection/src/traits/select/confirmation.rs` | `confirm_auto_impl_candidate` | `325-367` | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs` | `consider_auto_trait_candidate` | `194-260` | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs` | `instantiate_constituent_tys_for_auto_trait` | `24-114` (`87-109`) | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_next_trait_solver/src/solve/eval_ctxt/mod.rs` | `CurrentGoalKind::CoinductiveTrait`, `step_kind_to_nested` | `59-95`, `436-451` | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_middle/src/ty/trait_def.rs` | `TraitDef::is_coinductive` | `44-51` | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_middle/src/ty/util.rs` | `Ty::is_freeze`, `Ty::is_trivially_freeze`, `Ty::has_unsafe_fields` | `1184-1225`, `1281-1287` | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_ty_utils/src/common_traits.rs` | `is_freeze_raw`, `is_trait_raw` | `25-27`, `47-56` | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_mir_transform/src/coroutine/layout.rs` | `locals_live_across_suspend_points`, `ignore_for_traits`, `mir_coroutine_witnesses` | `83-184`, `372-391`, `462-493` | Source |
| `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) | `compiler/rustc_traits/src/coroutine_witnesses.rs` | `coroutine_hidden_types` | `12-44` | Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `library/core/src/marker.rs` | `Send`, `Sync`, `PhantomData`, `Freeze` + `!Freeze`/`unsafe Freeze`, `Unpin`, `PhantomPinned` | `87-106`, `658-675`, `810-812`, `905-919`, `1014-1031` | Normative / Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `library/core/src/cell.rs` | `UnsafeCell` (`!Sync` + `#[rustc_assert_variance(invariant)]`) | `2309-2318` | Normative / Source |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` / `14210df0e`) | `library/alloc/src/rcs/rc.rs` / `library/alloc/src/rc.rs` | `Rc` (`!Send`, `!Sync`) | `325-346` (`14210df0e`: `320-338`) | Source |
| `google/zerocopy` (`b4c1107fa2` / `fafea21077`) | `zerocopy/src/lib.rs` | `pub unsafe trait Immutable` + safety comment | `1700-1738` | Normative / Source |
| `google/zerocopy` (`b4c1107fa2` / `fafea21077`) | `zerocopy/src/impls.rs` | `Box<T: Sized>`, `PhantomData<T: ?Sized>`, `UnsafeCell<T>` impls, `*const T`/`&T`/`Option<T>`, unit assertions | `304-308`, `653-661`, `839-868`, `965-990`, `2222-2238` | Source |
| `google/zerocopy` (`b4c1107fa2` / `fafea21077`) | `zerocopy/zerocopy-derive/src/derive/mod.rs` | `derive_immutable` | `19-31` | Source |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | `trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean` | `COMPILER_VERSION`, `after_analysis`, `MirTy::unsupported` | `driver.rs:25, 75-84`; `MirAst.lean:295-321` | Source |

### 5.2 Empirical Probe Execution (`support/probe_auto_traits_freeze_immutable.py` -> `support/probe_results.json`)

Basis: execution on `2026-11-24` using `rustc 1.98.0-nightly (14210df0e 2026-05-31)` against `google/zerocopy` (`b4c1107fa213ab01d860d6cb24a12fd0834f0df7`, crate `0.8.64`) with temporary scratch artifacts created inside `tempfile.TemporaryDirectory()`.

- **Part A (12 `rustc` probes):**
  - `coinductive_node_has_cell_and_phantom_cell_ok`: `compile_returncode = 0`, `run_returncode = 0`, `run_stdout = "AUTO_OK=1"` (`Node`, `CycleA`, `HasRaw`, `HasCell`, `HasPhantomCell`, `HasPhantomRaw`).
  - `next_solver_coinductive_and_phantom_freeze_ok` (`-Znext-solver`): `compile_returncode = 0`, `run_returncode = 0`, `run_stdout = "AUTO_OK=1"`.
  - `coinductive_node_with_raw_ptr_rejected_send_e0277`, `coinductive_node_with_cell_rejected_sync_e0277`, `has_raw_ptr_not_send_rejected_e0277`, `has_raw_ptr_not_sync_rejected_e0277`, `has_cell_not_sync_rejected_e0277`, `has_cell_not_freeze_rejected_e0277`, `has_phantom_cell_not_sync_rejected_e0277`, `has_phantom_raw_not_send_rejected_e0277`: all returned `compile_returncode = 1` with expected `E0277` diagnostics naming `*const u8` or `UnsafeCell<u32>`.
  - `unsafe_field_blocks_send_allows_unpin`: `compile_returncode = 0`, `run_stdout = "UNSAFE_FIELD_UNPIN_OK=1"`; `unsafe_field_blocks_send_rejected_e0277`: `compile_returncode = 1` (`E0277` on `Send`).
- **Part B (`zerocopy` `0.8.64` + `zerocopy_derive` proc-macro, 8 builds/probes):**
  - `libzerocopy.rlib` (`CARGO_PKG_VERSION=0.8.64 --cfg feature="alloc" --cfg feature="derive" --cfg no_zerocopy_allocator_api_1_100_0` + `libzerocopy_derive.so`): `zerocopy_lib_compile_returncode = 0`, `zerocopy_derive_built = true`.
  - `zerocopy_phantom_unsafecell_implements_immutable_ok`: `compile_returncode = 0`, `run_stdout = "ZC_PHANTOM_CELL_IMMUTABLE_OK=1"` (`PhantomData<UnsafeCell<u32>>: Immutable + Send + Freeze`, `[PhantomData<UnsafeCell<u32>>; 4]`, `Option<PhantomData<UnsafeCell<u32>>>`, `Box<UnsafeCell<u32>>`, `*const UnsafeCell<u32>`, `&UnsafeCell<u32>`, `ManuallyDrop<u32>`, `Wrapping<u32>`, `MaybeUninit<u32>`).
  - `zerocopy_derive_phantom_and_recursive_node_ok`: `compile_returncode = 0`, `run_stdout = "ZC_DERIVE_IMMUTABLE_OK=1"` (`#[derive(Immutable)]` on `HasPhantomCell` and cyclic `RecImmNode { val: u32, next: Option<Box<RecImmNode>> }`).
  - `zerocopy_unsafecell_rejected_immutable_e0277`, `zerocopy_cell_rejected_immutable_e0277`, `zerocopy_manually_drop_unsafecell_rejected_immutable_e0277`, `zerocopy_box_slice_unsafecell_rejected_immutable_e0277` (`doesn't have a size known at compile-time`, pointing to `zerocopy/src/impls.rs:306`), `zerocopy_derive_struct_with_unsafecell_rejected_e0277`, `zerocopy_derive_phantom_cell_rejected_sync_e0277`: all returned `compile_returncode = 1` (`E0277`).
- **Part C (6 `async fn` coroutine probes):**
  - `rc_held_across_await_rejected_not_send`: `compile_returncode = 1` (`future returned by bad is not Send`, `Rc<u32>` used across `.await`).
  - `rc_dropped_before_await_send_ok`: `compile_returncode = 0`, `run_stdout = "ASYNC_SEND_OK=1"`.
  - `unsafecell_by_value_and_phantom_across_await_send_ok`: `compile_returncode = 0`, `run_stdout = "ASYNC_CELL_VAL_SEND_OK=1"`.
  - `ref_unsafecell_across_await_rejected_not_send`, `ref_phantom_unsafecell_across_await_rejected_not_send`: both `compile_returncode = 1` (`future is not Send`, citing `Sync is not implemented for UnsafeCell<u32>`).
  - `async_static_coroutine_not_unpin_e0277`: `compile_returncode = 1` (`E0277`, `{async fn body of triv()} cannot be unpinned`).

### 5.3 Kernel-Checked Lean `v4.34.1` Mechanization (`support/AutoTraitsCoinductiveFreezeAndImmutableSoundness.lean`)

Basis: kernel execution on `2026-11-24` with Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) using `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` plus MetaM environment inspection:

- File size: `2,246` lines (`86` explicit `theorem`s / `143` total kernel `thmInfo` constants across `34` `noncomputable def` definitions, `0` plain `def`s, `0` `partial def`s, `0` `deriving` clauses).
- Exit code: `0` with zero errors and zero warnings (`-DwarningAsError=true`).
- MetaM audit output: `theorem_count=143 unsafe_rec=0 unsafe_const=0 bad_axioms=0 axioms=[propext]` — confirming zero `._unsafe_rec` constants, zero `sorryAx`, zero `Classical.choice`, zero `Quot.sound`, zero `Lean.ofReduceBool` (`native_decide`), zero `omega`, and zero `bv_decide`.
- Key theorem anchors inside `namespace AutoTraitsCoinductiveImmutable`: `StepF_mono`, `coindSat_iff_step`, `coindSat_rejects_reachable_negative_leaf`, `checkWithStack_sound`, `checkWithStack_inductive_cycle_fails`, `kleeneGfp_iff_coindSat`, `node_cycle_coindSat_all`, `mutual_cycle_coindSat_send_sync`, `bad_node_cycle_rejects_send_and_sync`, `cell_node_send_yet_not_sync_not_freeze`, `loop_imm_rejected_by_dfs_stack`, `phantom_unsafecell_four_way_separation`, `has_phantom_cell_four_way_separation`, `unsafecell_matrix_row`, `raw_ptr_and_phantom_raw_matrix_rows`, `rc_matrix_row`, `box_sized_vs_unsized_unsafecell`, `unsafe_field_and_negative_impl_discrimination`, `asymmetry_kleene_converges_at_3`, `coindSat_immutable_implies_no_inline_unsafecell`, `coindSat_immutable_implies_all_bytes_immutable`, `coindSat_immutable_implies_zero_unsafecell_bytes`, `concrete_byte_level_immutable_witnesses`, `zst_unsafecell_fails_immutable_while_phantom_passes`, `async_coroutine_send_iff_live_across_await_send`, `async_dead_non_send_local_preserves_send`, `async_live_rc_across_await_breaks_send`, `async_unsafecell_value_send_vs_ref_not_send`, and `async_static_not_unpin`.

## Revalidation

To revalidate every empirical, source, and mechanized claim cleanly on another toolchain or commit without repeating the broader investigation:

1. **Rerun all live `rustc` + `zerocopy` + `async` probes:**
   ```bash
   python3 reports/rustc-auto-traits-coinductive-send-sync-freeze-phantomdata-and-zerocopy-immutable/support/probe_auto_traits_freeze_immutable.py \
     --zerocopy-src <path/to/google/zerocopy/zerocopy> \
     --out /tmp/reval_probe_results.json
   ```
   Confirm `compile_returncode == 0` with `AUTO_OK=1` (both default solver and `-Znext-solver`), `UNSAFE_FIELD_UNPIN_OK=1`, `ZC_PHANTOM_CELL_IMMUTABLE_OK=1`, `ZC_DERIVE_IMMUTABLE_OK=1`, `ASYNC_SEND_OK=1`, `ASYNC_CELL_VAL_SEND_OK=1`, and `compile_returncode == 1` (`E0277`) on all negative witnesses (`BadNode`, `CellNode`, `HasPhantomCell: Sync`, `Box<[UnsafeCell<u32>]>: Immutable`, `&PhantomData<UnsafeCell<u32>>` across `.await`, `async` `Unpin`).
2. **Re-check the Lean `v4.34.1` kernel proofs:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/rustc-auto-traits-coinductive-send-sync-freeze-phantomdata-and-zerocopy-immutable/support/AutoTraitsCoinductiveFreezeAndImmutableSoundness.lean
   ```
   Confirm exit code `0` with zero warnings and zero errors.
3. **Diff the narrow upstream regions before extending applicability beyond `14210df0e` / `f7da9a423` / `fafea2107`:**
   - `rust-lang/rust`:
     ```bash
     git diff <base>..<new> -- \
       compiler/rustc_trait_selection/src/traits/select/mod.rs \
       compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs \
       compiler/rustc_trait_selection/src/traits/select/confirmation.rs \
       compiler/rustc_next_trait_solver/src/solve/trait_goals.rs \
       compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs \
       compiler/rustc_next_trait_solver/src/solve/eval_ctxt/mod.rs \
       compiler/rustc_middle/src/ty/util.rs \
       compiler/rustc_mir_transform/src/coroutine/layout.rs \
       compiler/rustc_traits/src/coroutine_witnesses.rs \
       library/core/src/marker.rs \
       library/core/src/cell.rs \
       library/alloc/src/rcs/rc.rs
     ```
   - `google/zerocopy`:
     ```bash
     git diff <base>..<new> -- \
       zerocopy/src/lib.rs \
       zerocopy/src/impls.rs \
       zerocopy/zerocopy-derive/src/derive/mod.rs
     ```
   - Notice `PhantomData<T>` explicit `Freeze` impls (`library/core/src/marker.rs:911-919`), `Box<T: Sized>: Immutable` (`zerocopy/src/impls.rs:304-308`), and `locals_live_across_suspend_points` / `ignore_for_traits` (`coroutine/layout.rs:121-145, 372-382`) are the exact policy switches whose edits would alter any separation in Section 3.5–3.7.
4. **Revalidate corpus structural invariants:**
   ```bash
   python3 tools/reference.py catalog
   python3 tools/reference.py check
   ```
