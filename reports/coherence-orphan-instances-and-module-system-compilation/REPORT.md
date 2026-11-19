# Coherence, Orphan Instances, Specialization Soundness, and Module-System Compilation

## Summary

Static ad-hoc polymorphism and modular abstraction are governed by four coupled compiler constraints: **global instance coherence**, **separate compilation**, **specialization soundness under erasure**, and **static phase separation for modules**. No production compiler satisfies all desired properties simultaneously:

1. **The Global Coherence Trilemma**: No language can simultaneously preserve (a) **global uniqueness of instances** (allowing types like `BTreeSet<K>` to omit dictionary identity), (b) **separate compilation without whole-program overlap rejection**, and (c) **modular orphan/local extensibility**.
   - **Rust** keeps (a) and (b) via compile-time orphan rules (RFC 1023/2451) and overlap rejection (`E0119`/`E0210`), sacrificing (c).
   - **Haskell (GHC)** keeps (a) only by convention (`-Worphans`) and transitive orphan interface loading (`VisibleOrphanModules`), while opt-in `OVERLAPPING`/`INCOHERENT` breaks coherence and introduces dictionary-passing vs. monomorphization drift.
   - **Scala 3** and **Lean 4** keep (b) and (c) while dropping global uniqueness: Scala 3 sets `isCoherent` only for `CanEqual`, searching lexical scope before companion scope; Lean 4 uses tabled synthesis with a "morally canonical" cutoff (`backward.synthInstance.canonInstances`) that risks non-defeq instance diamonds.
   - **Modular Type Classes** (Dreyer et al. POPL '07) and **OCaml Modular Implicits** (White, Bour & Yallop 2015) bind overloading to ML modules, placing canonical identity in module paths rather than global tables.
2. **Specialization Soundness vs. Lifetime Erasure**: Overlapping specialization is unsound whenever region/lifetime proofs are erased before monomorphization unless every specializing impl is **always applicable** (invariant under lifetime substitution). In `rust-lang/rust`, full `#![feature(specialization)]` permits safe use-after-free (`tests/ui/specialization/issue-40582.rs`). `min_specialization` restores structural soundness via four checks (`check_has_items`, `check_static_lifetimes`, `check_duplicate_params`, `check_predicates`) plus `#[rustc_specialization_trait]`, but retains a documented unsound marker-trait escape hatch (`#[rustc_allow_lifetime_dependent_specialization]`).
3. **Negative Reasoning & SemVer Monotonicity**: Separate compilation requires monotonicity under upstream impl additions. Rust separates **implicit negative reasoning** (gated by `trait_ref_is_knowable` across `InCrate::Remote`, `#[fundamental]`, and `InCrate::Local`) from **explicit negative impls** (`flip_polarity` + always-applicable auto-trait checks `E0366`/`E0367`). Under RFC 2451, adding any impl with an uncovered type parameter or implementing a `#[fundamental]` trait for an existing type is a **major SemVer-breaking change**.
4. **ML Modules, Phase Separation, 1ML & Recursive "Double Vision"**: Static module compilation rests on the Harper–Mitchell–Moggi **phase distinction**. **1ML** (Rossberg 2018) unifies core and modules via System $F_\omega$ elaboration using **small/large** predicativity and **pure (applicative) / impure (generative)** arrows. **OCaml** strictly separates applicative (`Named`) and generative (`Unit`) functors (`includemod.ml`) and forbids generative abstract-type applications inside applicative functor bodies (`typemod.ml`). For mutually recursive sealed modules, **Dreyer's RTG/RMC** (2007) solves the **double vision** problem via destination-passing abstract types and **MixML** (2013) adds separate compilation, whereas OCaml uses mandatory explicit signatures, finite $N$-step strengthening unrolling (`check_recmodule_inclusion`), and a five-mode initialization-safety checker (`value_rec_check.ml`, POPL 2021).

All four mechanisms are modeled and verified by the self-contained Python 3.10+ probe `support/verify_coherence_and_specialization.py`.

## Applicability

This reference covers formal PL semantics and six production compiler frontends inspected at pinned commits on `2026-11-19`:

- **Foundational literature (`normative` / `derived`)**: Wadler & Blott (POPL '89); Harper, Mitchell & Moggi (POPL '90); Leroy (POPL '95); Dreyer, Crary & Harper (POPL '03); Dreyer, Harper, Chakravarty & Keller (POPL '07); Dreyer (JFP 2007, ICFP 2007); Rossberg & Dreyer (TOPLAS 2013); Rossberg, Russo & Dreyer (JFP 2014); White, Bour & Yallop (EPTCS 2015); Rossberg (JFP 2018); Bottu, Xie, Marntirosian & Schrijvers (ICFP 2019); Schrijvers, Oliveira, Wadler & Marntirosian (JFP 2019); Selsam, Ullrich & de Moura (2020); and Reynaud, Scherer & Yallop (POPL 2021).
- **Pinned compiler & specification repositories (`normative` / `source`)**:
  - `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (RFCs 1023, 1210, 1268, 2451) interpreted against `rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545` (`rustc_next_trait_solver`, `rustc_trait_selection`, `rustc_hir_analysis`, `core`, `alloc`, specialization UI tests).
  - `ocaml/ocaml` @ `d921d1e86c56baa7b30e890ced455c12255793f5` (`typing/includemod.ml`, `typing/typemod.ml`, `typing/value_rec_check.ml`).
  - `ghc/ghc` @ `83038fbee5efea8e3ebd5090b2ff5537462e169d` (`compiler/GHC/Core/InstEnv.hs`).
  - `scala/scala3` @ `90f3daf0a4795308d9c0e1b8f2265aeaecae8aa2` (`compiler/src/dotty/tools/dotc/typer/Implicits.scala`, contextual abstraction reference docs).
  - `leanprover/lean4` @ `8009d0a64d2860606c6a5ac5ff6702622b24921e` (`src/Lean/Meta/SynthInstance.lean`, `src/Lean/ScopedEnvExtension.lean`).
- **Executable probe (`execution`)**: `support/verify_coherence_and_specialization.py` executed under Python `3.13.15` (stdlib only, Python 3.10+ compatible).

### Cross-References to Adjacent Corpus Packages

This package documents cross-language type-system, coherence, specialization, and module semantics without duplicating Rust-specific lowering/linking inventories covered elsewhere:

- `rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning`: post-erasure monomorphization collection, vtable layout, symbol mangling, and CGU partitioning.
- `cross-dso-dynamic-linking-vtable-uniqueness-and-open-world-lto-contracts`: cross-DSO vtable address uniqueness, symbol interposition, and open-world LTO contracts.
- `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering`: `rustc_next_trait_solver` proof structure, Polonius borrow checking, THIR-to-MIR lowering, and why frontend checking before MIR lifetime erasure carries the dominant compiler soundness surface.

## Findings

### 1. The Global Coherence Trilemma and Instance-Scope Design Space

Basis: normative (Wadler & Blott POPL '89; Dreyer et al. POPL '07; White et al. EPTCS 2015; Bottu et al. ICFP 2019; Schrijvers et al. JFP 2019) + source (`ghc/ghc`, `rust-lang/rust`, `scala/scala3`, `leanprover/lean4`) + execution (`support/verify_coherence_and_specialization.py` Part A) + derived.

Wadler & Blott (POPL '89) formalized **type classes** by elaborating overloaded terms into Hindley–Milner/System F functions taking implicit **dictionary records**. **Coherence** requires that all valid elaborations of a source expression yield observationally equivalent runtime behavior regardless of non-determinism in constraint resolution.

#### 1.1 The Trilemma and `BTreeSet` Invariant Corruption

Across separately compiled modules, three properties form an impossibility trilemma:

1. **Global Uniqueness**: At most one dictionary exists for any closed constraint $C(\bar{\tau})$ across the entire program, allowing data structures (`BTreeSet<K>`, `HashMap<K, V>`) and associated types to omit dictionary identity from their static type.
2. **Separate Compilation**: Modules $M_1, M_2$ compiled independently against shared interface $I$ can always be linked without late overlap rejections or silent invariant corruption.
3. **Modular Local / Orphan Extensibility**: Any downstream module can retroactively implement foreign trait $C$ for foreign type $T$, or override $C(T)$ locally, without wrapping $T$ in a distinct nominal `newtype`.

Dropping **(1)** without indexing collections by dictionary identity causes immediate data-structure corruption. In `support/verify_coherence_and_specialization.py` (`probe_a_btreeset_coherence`):
- Module $M_1$ builds an unbranded BST `Set<int>` inserting `(30, 10, 50, 20, 40)` under ascending `Ord` (`a - b`), giving in-order `[10, 20, 30, 40, 50]` with `10` in the left subtree of `30`.
- Module $M_2$ introduces a local descending `Ord` (`b - a`) and receives the same `Set<int>`:
  - `contains(s1, 10)` evaluates `desc_cmp(10, 30) = +1`, descends right, and returns **`False`** even though `10` is physically in the tree (`silent_lookup_miss_for_10: true`).
  - `insert(s1, 25)` routes `25` right of `30` and right of `50`, yielding in-order **`[10, 20, 30, 40, 50, 25]`**, violating **both** ascending and descending BST invariants (`corrupted_valid_under_asc: false`, `corrupted_valid_under_desc: false`).
- Indexing the set by an instance brand (`BrandedSet[K, OrdBrand]`, modeling ML `Set.Make(Ord).t` or dependent `Set K (inst : Ord K)`) statically rejects cross-dictionary `union`/`contains` (`branded_cross_union_rejected: true`).

#### 1.2 Formal Coherence Proofs (Bottu et al. 2019 & COCHIS 2019)

Even without overlapping global instances, elaboration is non-deterministic because **superclasses** and **flexible contexts** yield multiple derivation paths (e.g., obtaining `Eq a` directly from a local given vs. projecting it from a local `Ord a` given). Bottu, Xie, Marntirosian & Schrijvers (ICFP 2019) prove coherence for elaboration with superclasses and flexible contexts by observing that target System F contexts can distinguish equivalent dictionaries if those contexts lack source-language counterparts. Inspired by full abstraction, they split elaboration into two steps: (1) non-deterministic elaboration into an intermediate language proven contextually equivalent via logical relations, followed by (2) deterministic lowering to System F.

When property **(1)** is dropped for scoped implicits, **COCHIS** (Schrijvers, Oliveira, Wadler & Marntirosian JFP 2019) formalizes two weaker invariants: **deterministic resolution** (unique choice per lexical scope) and **stability under type substitution** (instantiating a polymorphic type parameter $\alpha \mapsto \tau$ never retroactively switches an already-resolved dictionary unless resolution was abstracted into a constraint parameter).

#### 1.3 Cross-Language Comparison Matrix

| System | Trilemma Position | Orphan / Scope Policy | Resolution & Precedence | Key Hazard / Tradeoff | Primary Source |
| --- | --- | --- | --- | --- | --- |
| **Rust (`rustc`)** | (1)+(2); drops (3) | Strict compile-time orphan check (RFC 1023/2451); no local impls | Zero overlap (`E0119`), except empty `#[marker]` traits & unstable specialization chain | Newtype boilerplate; cannot author `crate-a-crate-b` glue crates; `OrphanCheckMode::Compat` hole | `rustc_next_trait_solver/src/coherence.rs:20–478` |
| **Haskell (`GHC`)** | (1) by convention; (2) via orphan tracking | Orphans permitted (`-Worphans`); tracked in `VisibleOrphanModules` | Overlap opt-in via `OVERLAPPING`/`OVERLAPPABLE`/`INCOHERENT` (`(IL0)–(IL6)`); Givens block globals | Transitive `.hi` loading cost; link/import collisions; polymorphic vs. monomorphic semantic drift | `compiler/GHC/Core/InstEnv.hs:348–401, 566–680` |
| **Scala 3 (`dotc`)** | (2)+(3); drops (1) | Arbitrary local `given`s + companion implicit scope | Lexical/contextual scope searched strictly before companion `implicitScope`; `compareAlternatives` disambiguates; only `CanEqual` is `isCoherent` | Collections must store `Ordering` at runtime (`TreeSet`) to avoid corruption; `3.4`–`3.7` priority changes | `compiler/src/dotty/tools/dotc/typer/Implicits.scala:1276, 1365–1527, 1696–1825` |
| **Lean 4** | (2)+(3); "morally canonical" (1) | `global`, namespace `scoped`, and block `local` via `ScopedEnvExtension` | Tabled synthesis (`SynthInstance`); locals tried **before** priority-sorted globals; `canonInstances` stops at 1st mvar-free answer | Non-defeq instance diamonds break dependent `isDefEq`; structural table keys may re-solve defeq goals | `src/Lean/Meta/SynthInstance.lean:35–77, 223–280, 618–653`; `ScopedEnvExtension.lean:17–250` |
| **Modular Type Classes** (POPL '07) | (2)+(3); module-indexed (1) | Lexical `using` canonical structures inside ML module system | Harper–Stone type-directed elaboration; ambiguity rejected | Instance identity stays explicit in module signatures (`Set.Make(Ord).t`) | Dreyer et al. POPL '07 (`10.1145/1190216.1190229`) |
| **OCaml Modular Implicits** (2015) | (2)+(3); module-indexed (1) | Lexical `implicit module` bindings; no unimported companion search | Type-directed elaboration into first-class functors; ambiguity fails | Preserves functor path identity; requires explicit module scoping | White, Bour & Yallop EPTCS 198 (`10.4204/EPTCS.198.2`) |

### 2. Orphan Rules, Fundamental Annotations, and Cross-Crate Link Safety

Basis: normative (RFC 1023, RFC 2451) + source (`ghc/ghc`, `rust-lang/rust`) + execution (`support/verify_coherence_and_specialization.py` Part B) + derived.

#### 2.1 Haskell's Orphan Definition and Functional Dependencies

In `compiler/GHC/Core/InstEnv.hs:348–401` (`Note [When exactly is an instance decl an orphan?]`), an instance `instance (...) => C t1 ... tn` is **non-orphan** iff:
- Without functional dependencies: at least one type or class constructor in the instance head is defined in the current module.
- With functional dependencies (`class C a b | a -> b`): for **every** fundep, at least one free name in a **non-determined** part of the head is defined locally. Thus `instance C Int LocalT` in module `X` is an **orphan**, because solving `C Int ?v` in module `Y` cannot locate `X` via `Int` alone.

Because GHC permits orphan instances, it maintains `VisibleOrphanModules` (`ie_visible`, `InstEnv.hs:566–591`) and requires downstream modules to load every transitive orphan `.hi` file—trading compile-time scalability and link-time conflict immunity for retroactive extensibility.

#### 2.2 Rust's RFC 1023 / RFC 2451 Rules and `rustc` Implementation Mechanics

To guarantee compile-time link safety and allow upstream crates to add non-blanket impls without breaking downstream crates, Rust evolved from RFC 1023 (`text/1023-rebalancing-coherence.md:8–16, 192–228`, banning *any* type parameter before a local type) to **RFC 2451** (`text/2451-re-rebalancing-coherence.md:58–84, 181–200`), which distinguishes **covered** vs. **uncovered** type parameters:

- A type parameter `T` is **covered** inside any non-fundamental type constructor (e.g., `Vec<T>`).
- A **`#[fundamental]`** constructor neither covers parameters (`Box<T>`, `&T`, `&mut T`, `Pin<T>` leave `T` uncovered) nor blocks locality (`Box<LocalType>`, `&mut Pin<Box<LocalType>>` are local).
- Given `impl<P1..=Pm> Trait<T1..=Tn> for T0`, the impl passes iff `Trait` is local, **or** scanning `[T0, T1, ..., Tn]` left-to-right:
  1. Some `Ti` contains a local type reached purely through `#[fundamental]` constructors (the *local key parameter*); and
  2. No uncovered type parameter `Pj` is reached purely through `#[fundamental]` constructors in `T0..T_{i-1}`.

Direct inspection of `compiler/rustc_next_trait_solver/src/coherence.rs:14–478` and `compiler/rustc_hir_analysis/src/coherence/orphan.rs:22–382` exposes six critical nuances:

1. **Dual `InCrate` Semantics (`coherence.rs:14–18, 352–389`)**: `InCrate::Local` validates local impls (inference vars representing impl params exit with `UncoveredTyParam`), whereas `InCrate::Remote` tests whether an unknown foreign crate *could* implement a trait ref (inference vars exit with `LocalTy`, since a remote crate could instantiate them with its own local type).
2. **Unsound `OrphanCheckMode::Compat` for Projections (`coherence.rs:20–33, 366–389`; `orphan.rs:29–56`)**: A rigid associated-type projection `<T as Id>::Assoc` may normalize to `T`. `OrphanCheckMode::Proper` rightly treats it as an uncovered parameter, but `orphan_check_impl` falls back to `OrphanCheckMode::Compat`, where `ty::Projection` continues past it and emits only the lint `UNCOVERED_PARAM_IN_PROJECTION`—explicitly annotated `// This is unsound` (`rust-lang/rust#124559`, `#99554`).
3. **Opaque Types Are Always Non-Local (`coherence.rs:390–407`)**: Even in the defining crate, `ty::Opaque` (`impl Trait` / TAIT) is non-local so changing a hidden type from local to foreign is not breaking and coherence does not cycle on typeck.
4. **Const Parameters Are Ignored (`coherence.rs:460–477`)**: `visit_const` returns `Continue(())` because primitive const values exist in the trait-defining crate (flagged as needing revisitation if fn-pointer/dyn const generics arrive).
5. **`Box<T, A>` Special Case (`coherence.rs:417–421`)**: `SolverAdtLangItem::OwnedBox` visits only `args.type_at(0)`, preventing `Box<Foreign, LocalAlloc>` from passing the orphan check.
6. **Live `#[fundamental]` Inventory (`rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545`)**:
   - **Types**: `&T`, `&mut T` (`ty::Ref`, `coherence.rs:413`), `Box<T, A>` (`library/alloc/src/boxed.rs:301–302`), and `Pin<Ptr>` (`library/core/src/pin.rs:1086–1087`). Because `Pin` is fundamental, downstream crates could maliciously write `impl DerefMut for Pin<&LocalType>`; `core::pin` closes this hole by delegating to a non-fundamental `helper::Pin` (`library/core/src/pin.rs:1699–1709`), forcing orphan rules to block downstream `DerefMut` impls.
   - **Traits**: `Fn`, `FnMut`, `FnOnce`, `FnPtr` (`library/core/src/ops/function.rs:73, 160, 239, 350`), `Sized`, `MetaSized`, `PointeeSized`, `Tuple` (`library/core/src/marker.rs:150, 169, 186, 1072`). Fundamental traits promise that adding an impl for an existing type is a breaking change, enabling downstream negative reasoning (e.g., `regex` relying on `&str: !FnMut`, RFC 1023 L172–190).

#### 2.3 Sibling Link-Safety Proof & Exhaustive Model Check

For two mutually unknowing sibling crates `CrateA` and `CrateB`, let `CrateA`'s local key parameter sit at index $i$ and `CrateB`'s at index $j$. Neither crate can name the other's ADTs:
- If $i = j$: position $i$ holds distinct nominal local ADTs reached only through fundamental wrappers, which cannot unify.
- If $i < j$: `CrateB` cannot have an uncovered parameter at $i$, so position $i$ in `CrateB` is either a non-local concrete type or wraps a parameter behind a non-fundamental constructor (e.g., `Vec<B0>`), neither of which unifies with `CrateA`'s local ADT under fundamental wrappers. The case $j < i$ is symmetric.

`support/verify_coherence_and_specialization.py` (`probe_b_rust_orphan_and_knowability`) passes all 14 RFC 2451 cases (including `Proper` vs. `Compat` projection divergence), checks **1,764 sibling impl pairs** ($42 \times 42$ valid proper-orphan impls across `crate_a` and `crate_b`) with **0 unifications**, and demonstrates that bypassing the ordering rule (`impl<B0> ForeignTrait<SiblingTy> for B0`) immediately collides with `impl<A0> ForeignTrait<A0> for MyLocal`.

### 3. Specialization Soundness, Lifetime Erasure, and Parametricity

Basis: normative (RFC 1210, RFC 1268) + source (`rust-lang/rust`, `ghc/ghc`) + execution (`support/verify_coherence_and_specialization.py` Part C) + derived.

Specialization permits overlapping impls ordered by specificity, colliding directly with **lifetime erasure** and **relational parametricity**.

#### 3.1 Lifetime-Erasure Exploits Under Unconstrained Specialization

As detailed in `rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning` and `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering`, `rustc` erases regions (`ReErased`) after borrow checking and before monomorphization/codegen. RFC 1210 (`text/1210-impl-specialization.md:992–1297`) acknowledged that codegen lacks lifetimes, yet proposed an "ask forgiveness" design attempting to ignore lifetimes at dispatch. Whenever polymorphic typechecking selects a **default parent** impl (imposing no lifetime equality/outlives constraint) while post-erasure codegen dispatches to a **specializing child** impl, memory safety collapses in 100% safe Rust. Three exploit classes are verified in `rust-lang/rust` (`b0b600668bb9b4a897e2299b0a44289d42276545`) and reproduced in probe Part C:

1. **Direct `'static` Bound (`impl<T: 'static>` overriding `impl<T>`)**: Polymorphic code typechecks against `impl<T>` without proving `T: 'static`; after erasing `'local` to `ReErased`, post-erasure selection conflates `&'erased str` with `&'static str`, leaking stack references into `'static` storage.
2. **Repeated Lifetime or Type Parameters (`tests/ui/specialization/issue-40582.rs`, still `//@ check-pass` / `//@ known-bug: #40582`)**:
   ```rust
   trait FromRef<'a, T: ?Sized> { fn from_ref(r: &'a T) -> Self; }
   impl<'a, T: ?Sized> FromRef<'a, T> for &'a T { fn from_ref(r: &'a T) -> Self { r } }
   impl<'a, T: ?Sized, R> FromRef<'a, T> for R { default fn from_ref(_: &'a T) -> Self { unimplemented!() } }

   fn make_static<T: ?Sized>(data: &T) -> &'static T {
       fn helper<T: ?Sized, R>(data: &T) -> R { R::from_ref(data) }
       helper(data)
   }
   ```
   Typechecking `helper<T, R>` resolves `<R as FromRef<'b, T>>` to the default impl (no `'b == 'static` bound). At monomorphization with `R = &'static str`, both lifetimes erase to `ReErased`, matching `impl<'a, T> FromRef<'a, T> for &'a T` and returning `&'local str` as `&'static str`. Repeating a *type* parameter (`impl<T> X for (T, T)` specializing `impl<T> X for T`, `tests/ui/specialization/min_specialization/repeating_param.rs`) fails identically on `(&'a u8, &'b u8)` $\xrightarrow{\text{erase}}$ `(&'erased u8, &'erased u8)`.
3. **Indirect Trait Bounds (`tests/ui/specialization/soundness/partial_ord_slice.rs` & `partial_eq_range_inclusive.rs`)**: `struct Evil<'a, 'b>(Cell<(&'a [i32], &'b [i32])>)` implements `PartialOrd` for any `('a, 'b)`, but implements `Ord` **only** for `Evil<'a, 'a>`, swapping the two slices inside `Ord::cmp`. Specializing `<[T] as PartialOrd>` on `T: Ord` would dispatch `Evil<'long, 'short>` into `Ord::cmp` after erasure, swapping a short-lived borrow into a long-lived `Cell` slot (safe UAF).

#### 3.2 `rustc` Specialization Graph and `min_specialization` Always-Applicable Gate

`rustc` enforces specialization in two layers:

- **Chain-Only Specialization Graph (`compiler/rustc_trait_selection/src/traits/specialize/mod.rs:1–6, 234–376`; `specialization_graph.rs:76–335`)**: Unlike RFC 1210's lattice proposal, `rustc` accepts only **strict subset chains** (`le != ge` in `ChildrenExt::insert`, `L158–162`), except for empty `#[marker]` traits (RFC 1268). `specializes(child, parent)` instantiates `child` with identity placeholders, assumes `child`'s `param_env`, unifies `parent` with fresh inference vars, and proves `parent`'s clauses (plus requiring `child` to be at least as `const` as `parent`, `L339–368`; negative impls cannot specialize positive impls, `L268–270`). Overridden items must be marked `default` (`check_specialization_validity`, `check.rs:1227–1286`), and `async fn` / return-position `impl Trait` in traits (RPITIT) are barred from specialization (`check.rs:1445–1472`).
- **Always-Applicable Gate (`compiler/rustc_hir_analysis/src/impl_wf_check/min_specialization.rs:1–476`)**: Ensures that whenever `impl2`'s bounds hold and `impl1`'s bounds hold for *some* lifetimes, `impl1` holds for *all* lifetimes. After equating `impl2`'s args in terms of `impl1`'s generics (`get_impl_args`, `L164–198`) and stripping parent parameters uniquely constrained by associated-type projections (`unconstrained_parent_impl_args`, `L208–247`—which permits `impl<T> SpecExtend<T> for VecIntoIter<T>` over `impl<T, I: Iterator<Item = T>> SpecExtend<T> for I`), `check_always_applicable` (`L114–135`) runs four checks:
  1. `check_has_items` (`L137–150`): rejects empty specializing impls over a parent impl (`EmptySpecialization`).
  2. `check_static_lifetimes` (`L295–304`): rejects any free `'static` region in `parent_args` (`StaticSpecialize`).
  3. `check_duplicate_params` (`L269–285`): rejects any generic parameter of `impl1` appearing more than once in unconstrained `parent_args` (blocking both `issue-40582` and `(T, T)`).
  4. `check_predicates` / `check_specialization_on` (`L317–457`): accepts a clause on `impl1` only if it is already on `impl2` (or a WF obligation of trait args), `clause.is_global()`, a `#[rustc_specialization_trait]` (`TraitSpecializationKind::AlwaysApplicable`, whose own impls are checked always-applicable against *empty* base clauses, `L334–338`), or a `#[rustc_allow_lifetime_dependent_specialization]` marker trait (`TraitSpecializationKind::Marker`).
- **Two Documented Gaps in `min_specialization.rs`**:
  - `TraitSpecializationKind::Marker` (`L58–66`, used for `FusedIterator`) explicitly acknowledges: *"This is unsound, in the sense that the specialized impl may be used when it doesn't apply, but we allow it in the short term since it can't cause use after frees with purely safe code in the same way as specializing on traits with methods can."*
  - `ClauseKind::ConstArgHasType` (`L441–451`) carries an explicit `FIXME(min_specialization), FIXME(const_generics)` warning that allowing it unconditionally will need revision if generic const parameter types (`<T, const N: T>`) are supported.

Probe Part C (`probe_c_specialization_lifetime_erasure`) reproduces the pre- vs. post-erasure dispatch flip (`[false, true]`) for C1 (`'static`), C2 (`issue-40582`), and C3 (`(T, T)`), and confirms `check_min_specialization` rejects C1–C4 and `&'static u8` while accepting the projection-constrained `VecIntoIter<T>` specialization.

#### 3.3 GHC Overlap Rules, Parametricity Drift, and Autoref Workarounds

GHC (`compiler/GHC/Core/InstEnv.hs:592–680`, `Note [Rules for instance lookup]`) resolves constraints via `(IL0)–(IL6)`: local `Given`s block global search unless `-XIncoherentInstances` (`IL0`); `lookupInstEnv` partitions instances into substitution matches `all_matches` and non-matching unifiers `all_unifs` (`IL1`); `pruneOverlappedMatches` eliminates `IX` subsumed by `IY` if *either* `IX` is `OVERLAPPABLE`/`OVERLAPS`/`INCOHERENT` *or* `IY` is `OVERLAPPING`/`OVERLAPS`/`INCOHERENT`, and prunes remaining `INCOHERENT` candidates (`IL3`); a sole non-incoherent match succeeds only if `all_unifs` is empty (`IL6`).

Under **dictionary passing**, overlapping instances break parametricity and create call-site vs. polymorphic-wrapper divergence: calling `f :: Show a => [a] -> String` on `"abc"` passes `Show Char` into `f`, which invokes generic `Show [a]` instead of specialized `Show [Char]`, whereas monomorphizing or inlining at the call site invokes `Show [Char]`. In stable Rust (without `min_specialization`), libraries needing compile-time dispatch distinctions (e.g., `Sized` vs. `KnownLayout` DST transmutation) fall back to macro-based **autoref/autoderef specialization**, which cannot generalize across generic functions.

From a formal-verification standpoint (`derived`), requiring every optimization specialization `impl_fast` to carry a machine-checked refinement proof `impl_fast ⊑ impl_default` against the trait's behavioral specification decouples optimization from coherence: any admissible dispatch choice exhibits identical observable behavior.

### 4. Negative Trait Reasoning, Auto Traits, and Open-World SemVer Monotonicity

Basis: normative (RFC 1023, RFC 2451) + source (`rust-lang/rust`) + execution (`support/verify_coherence_and_specialization.py` Part B) + derived.

Separate compilation in an open-world ecosystem demands **monotonicity**: adding a non-breaking `impl` in an upstream dependency must never invalidate previously checked downstream derivations. Unrestricted negation-as-failure (`T: !Trait`) is non-monotonic.

#### 4.1 `rustc`'s Dual Negative-Reasoning Architecture

In `compiler/rustc_trait_selection/src/traits/coherence.rs:172–452`, `overlap` proves two impls disjoint via two distinct mechanisms:

1. **Explicit Negative Impls (`impl_intersection_has_negative_obligation`, `L180–191, 388–452, 562–593`)**: Equates both impl headers with inference variables in `TypingMode::Coherence`, plugs remaining inference vars with placeholders (`plug_infer_with_placeholders`, `L454–560`), elaborates `impl2`'s clauses, and calls `try_prove_negated_where_clause` (`L562–593`). That function flips polarity (`clause.as_predicate().flip_polarity(tcx)`) and verifies that an explicit negative impl (e.g., `impl !Error for &str`) proves the negated goal with zero ambiguity and empty region errors (`L592`). Contradicting an explicit negative impl triggers `NegativePositiveConflict` (`specialize/mod.rs:470–515`).
2. **Implicit Negative Reasoning (`impl_intersection_has_impossible_obligation`, `L220–228, 323–370`)**: Evaluates the unified obligations in `TypingMode::Coherence` using the next-generation solver (`with_next_trait_solver(true)`). Unproven goals trigger `trait_ref_is_knowable` (`rustc_next_trait_solver/src/coherence.rs:48–94`):
   - If `orphan_check_trait_ref(..., InCrate::Remote)` succeeds $\implies$ `Err(Conflict::Downstream)` (`CandidateSource::CoherenceUnknowable`).
   - Else if `trait_ref.def_id.is_local() || tcx.trait_is_fundamental(def_id)` $\implies$ `Ok(())` (knowable).
   - Else if `orphan_check_trait_ref(..., InCrate::Local { mode: Proper })` succeeds $\implies$ `Ok(())`; otherwise `Err(Conflict::Upstream)`.
   - Only a hard `is_true_error()` proves disjointness; any `Ambiguity` (including `CoherenceUnknowable` or overflow) conservatively reports overlap (`coherence.rs:355–369`).

An open caveat is documented at `coherence.rs:575–576` and `L705–707` (`FIXME(#132279)`): forking `TypingMode::non_body_analysis()` during negative-clause proving or ambiguity diagnostics can reveal opaque types and leak their auto traits.

#### 4.2 Auto-Trait Restrictions (`Send`, `Sync`, `Unpin`)

Because generic code relies structurally on auto traits (`A: Foo, B: Foo |- (A, B): Foo`), `rustc` imposes two additional soundness barriers:
- **Nominal & `dyn` Restrictions (`compiler/rustc_hir_analysis/src/coherence/orphan.rs:60–288`)**: Foreign auto traits may only be implemented (positively or negatively) on local nominal `ty::Adt` or `ty::Foreign` types—blocking `impl !Foo for (A, B)` (`rust-lang/rust#22978`, `L63–91`). Even for local auto traits, `impl AutoTrait for dyn Trait` and `impl<T: ?Sized> AutoTrait for T` are banned (`L109–136, 180–195`) so `dyn Trait` implements `AutoTrait` iff listed in its bounds (`rust-lang/rust#50781`).
- **Always-Applicable Negative Auto-Trait Impls (`compiler/rustc_hir_analysis/src/check/always_applicable.rs:84–179, 253–369`)**: `check_negative_auto_trait_impl` mirrors `check_drop_impl`, enforcing unique unspecialized ADT parameters (`E0366`) and forbidding any extra trait/outlives predicates beyond the ADT's definition (`E0367`).

#### 4.3 SemVer Compatibility Contract (RFC 2451 Amendment to RFC 1105)

| Upstream Crate Addition | SemVer Impact | Justification (`text/2451-re-rebalancing-coherence.md:165–176, 227–258`) |
| --- | --- | --- |
| `impl<T> OldTrait<T> for OldType` or `impl<T> OldTrait<T> for Vec<T>` | **Major breaking** | Contains an uncovered type parameter `T`, colliding with legal downstream `impl OldTrait<Local> for OldType` / `Vec<Local>` |
| `impl<T> OldTrait for Box<T>` / `&T` / `Pin<T>` | **Major breaking** | `#[fundamental]` wrappers leave `T` uncovered, colliding with downstream `impl OldTrait for Box<Local>` |
| `impl FundamentalTrait for OldType` (e.g., `FnMut` for `&str`) | **Major breaking** | Downstream crates legally rely on `OldType: !FundamentalTrait` via `trait_ref_is_knowable` |
| `impl NewTrait<Any> for Any` | **Minor compatible** | Downstream crates could not name `NewTrait` before this release |
| `impl<T> OldTrait<T> for NewType` or `impl<T> OldTrait<NewType, T> for OldType` | **Minor compatible** | `NewType` is a new local key type appearing before any uncovered parameter |
| `impl<T> OldTrait<Vec<T>> for Vec<T>` | **Minor compatible** | Not a blanket impl (`L75–77`): every `T` is covered by non-fundamental `Vec` |

For how open-world assumptions extend across dynamically linked DSOs and vtable deduplication, see `cross-dso-dynamic-linking-vtable-uniqueness-and-open-world-lto-contracts`.

### 5. ML Modules, Phase Separation, 1ML, Functors, and Recursive Module "Double Vision"

Basis: normative (Harper, Mitchell & Moggi POPL '90; Leroy POPL '95; Dreyer, Crary & Harper POPL '03; Dreyer JFP 2007 & ICFP 2007; Rossberg & Dreyer TOPLAS 2013; Rossberg, Russo & Dreyer JFP 2014; Rossberg JFP 2018; Reynaud, Scherer & Yallop POPL 2021) + source (`ocaml/ocaml`) + execution (`support/verify_coherence_and_specialization.py` Part D) + derived.

#### 5.1 Phase Separation and Static Path Dependency

Harper, Mitchell & Moggi (POPL '90) proved the **phase distinction** for higher-order modules: every module of existential signature $\Sigma \alpha : \kappa. \tau(\alpha)$ splits into a static type-constructor part $M_{\text{stat}}$ and a dynamic value part $M_{\text{dyn}}$, ensuring type checking never evaluates dynamic code. Allowing type projections `e.t` from arbitrary dynamic expressions `e` breaks phase separation unless full dependent types are adopted.

In `ocaml/ocaml` (`typing/typemod.ml:2707–2747`), `type_one_application` enforces phase separation directly:
- If a functor argument has a static module path (`arg_path = Some path`), OCaml substitutes `param -> path` into `mty_res` (`L2709–2716`).
- If the argument is anonymous/computed (`arg_path = None`, e.g., `F(struct ... end)` or an unpacked first-class module), OCaml attempts to erase `param` via `Mtype.nondep_supertype env [param] mty_res` (`L2728`), rejecting escaping dependencies with `Cannot_eliminate_dependency` (`L2729–2731`).

#### 5.2 F-ing Modules and 1ML (System $F_\omega$ Elaboration)

**F-ing Modules** (Rossberg, Russo & Dreyer JFP 2014) demonstrated that full ML higher-order modules elaborate directly into plain System $F_\omega$ existentials (`∃α. τ`) without primitive singleton kinds. **1ML** (Rossberg JFP 2018) pushes this further, collapsing ML's stratified core and module languages into a single language that remains elaborable to System $F_\omega$:
- **Unified Syntax & Semantics**: Records are structures, functions are functors, signatures are record types with type fields.
- **Small vs. Large Predicativity**: Types without abstract type fields (**small**) may instantiate polymorphic core type variables; types containing abstract types (**large**) are restricted to predicative contexts unless explicitly boxed, avoiding undecidable impredicative higher-order unification.
- **Pure vs. Impure Arrow Split**: **Pure arrows (`⇒`)** prohibit computational effects and fresh sealing, elaborating to **applicative** functors via Skolemization (`∃f : κ → κ'. ∀α. ...`); **impure arrows (`→`)** permit effects and fresh abstract types, elaborating to **generative** functors (`∀α. τ₁ → ∃β. τ₂`).

#### 5.3 Applicative vs. Generative Functors

Leroy (POPL '95) introduced **applicative functors** so independent invocations `Set.Make(IntOrd)` share the identical abstract type `Set.Make(IntOrd).t`, solving Standard ML's generative diamond-sharing friction. However, Dreyer, Crary & Harper (POPL '03) proved that applicative sealing is unsound with respect to abstraction invariants when a functor allocates per-call mutable state (e.g., fresh symbol tables or secret keys): equating `F(X).t = F(X).t` across two stateful calls lets keys from instance 1 corrupt instance 2.

OCaml (`d921d1e86c56baa7b30e890ced455c12255793f5`) provides both applicative (`Named (name, arg)`) and generative (`Unit`, `functor () -> ...`) functors with two strict guards:
1. **Strict Parameter Incompatibility (`typing/includemod.ml:655–673`)**: `functor_param` matches `(Unit, Unit)` and `(Named _, Named _)` only; mixing generative and applicative parameters fails with `Error.Incompatible_params`.
2. **No Generative Abstract Types Inside Applicative Bodies (`typing/typemod.ml:2657–2679`)**: Applying `Mty_functor (Unit, mty_res)` inside an applicative functor (`funct_body = true`) when `Mtype.contains_type env funct.mod_type` raises `Not_allowed_in_functor_body` (`L2672–2673`), preventing an applicative wrapper from laundering generative stamps into shared paths.

#### 5.4 Recursive Modules, "Double Vision", and Safe Cyclic Initialization

Mutually recursive sealed modules `A` (`type t = int`, sealed behind `sig type t; val f : B.u -> t end`) and `B` (`sig type u; val g : A.t -> u end`) trigger two distinct hazards:
- **Double Vision (Static)**: Inside `A`, `t` is concretely `int`, yet calling `B.g : A.t -> B.u` exposes `A`'s own type as the opaque forward-declared `A.t`. Naive checking rejects `B.g 42` because `int != A.t`.
- **Cyclic Initialization (Dynamic)**: Evaluating module bodies in a cycle can dereference an uninitialized forward binding.

Solutions span three milestones:
- **RTG & RMC (Dreyer JFP 2007, `10.1017/S0956796807006429`; ICFP 2007, `10.1145/1291151.1291196`)**: Replaces continuation-passing existentials with **destination-passing abstract type variables**. A destination $\alpha$ is pre-allocated before typing the cycle; privately inside `A`, $\alpha := \mathsf{int}$ makes forward references to `A.t` transparent, while outside `A`, $\alpha$ remains strictly opaque.
- **MixML (Rossberg & Dreyer TOPLAS 2013, `10.1145/2450136.2450137`)**: Recasts modules as separately compilable mixins (`link` / `new`), separating mutual type/value import-export declarations from final recursive knot-tying.
- **OCaml `module rec` (`typing/typemod.ml:2017–2102, 2192–2300, 3021–3106` & `typing/value_rec_check.ml:19–103`)**:
  - Mandates explicit signatures (`Recursive_module_require_explicit_type`, `typemod.ml:3033`) and performs two-pass approximation (`approx_modtype` $\to$ `dcl1` $\to$ `dcl2`, `L2058–2090`).
  - Checks `ACTUAL <: DECL` via `check_recmodule_inclusion` (`L2192–2300`, `PR#4450`/`PR#4470`): unrolls the recursive environment $N$ times (number of bindings) with `Mtype.strengthen ~aliasable:false` so `Xn.t = ... = X1.t` holds without circular manifest expansion—mitigating common double-vision failures without full destination-passing RTG.
  - Enforces runtime initialization safety in `value_rec_check.ml` via **Reynaud, Scherer & Yallop (POPL 2021, `10.1145/3434326`)**: five access modes (`Ignore`, `Delay`, `Guard`, `Return`, `Dereference`) paired with static-vs.-dynamic allocation size classification.

Probe Part D (`probe_d_modules_and_double_vision`) verifies applicative diamond equality, generative stamp distinctness, `Not_allowed_in_functor_body` and `Cannot_eliminate_dependency` rejections, naive double-vision failure, and RTG destination-passing internal transparency + external opacity.

### 6. Algebraic Diamond Coherence, Tabled Resolution, and Compilation Tradeoffs

Basis: normative (Selsam, Ullrich & de Moura 2020; Bottu et al. ICFP 2019) + source (`leanprover/lean4`, `scala/scala3`, `ghc/ghc`, `rust-lang/rust`) + derived.

#### 6.1 Lean 4 Tabled Typeclass Synthesis and Intensional Diamonds

In deep algebraic DAGs (`Field` $\to$ `CommRing` $\to$ `AddCommMonoid`), SLD backtracking suffers $O(2^d)$ diamond blowup and cyclic divergence. Lean 4 (`src/Lean/Meta/SynthInstance.lean:1–125, 223–280, 618–653`, Selsam et al. 2020) uses a **tabled search forest** keyed by normalized subgoals (`mkTableKey`, replacing assignable metavariables with `_tc.<idx>`, `L95–178`):
- `ScopedEnvExtension` (`src/Lean/ScopedEnvExtension.lean:17–250`) separates `.global` entries, namespace-keyed `.scoped ns` entries, and a lexical `stateStack` for `local` entries (bumping generation on `scopeChanged`).
- `getInstancesLazy` (`SynthInstance.lean:223–262`) sorts globals by ascending priority (`e₁.priority < e₂.priority`, `L237`) and pushes `localInstances` at the end (`L250–259`). Because `generate` (`L618–653`) steps backwards from `currInstanceIdx := instances.size`, **local instances are attempted before globals**, and higher-priority globals before lower-priority ones.
- Under `backward.synthInstance.canonInstances := true` (`L35–38, 69–77, 629–645`), once a metavariable-free goal (`!typeHasMVars`) finds one metavariable-free answer, `generate` pops the generator assuming instances are "morally canonical."
- Because Lean's kernel checks dependent types up to **definitional equality** (`isDefEq`) without global coherence enforcement, synthesizing two non-defeq instances along distinct diamond paths or scoped overrides causes dependent type errors—and structural `MkTableKey` (`L108–110`) can still revisit syntactically distinct but defeq goals.

#### 6.2 Compilation Architecture Synthesis

| Architecture | Systems | Coherence Guarantee | Separate Compilation | Specialization Behavior | Diamond Behavior |
| --- | --- | --- | --- | --- | --- |
| **Monomorphization + Global Orphan Rules** | Rust (`rustc`) | Static global uniqueness (`E0119`/`E0210`) | Full (`orphan_check_trait_ref` + `trait_ref_is_knowable`) | Unsound with lifetime-dependent impls (`issue-40582`); sound under `min_specialization` (minus marker hatch) | Static supertrait resolution; projections must be acyclic |
| **Dictionary Passing + Optional Overlap** | Haskell (`GHC`) | Convention (`-Worphans`); broken by `OVERLAPPING`/`INCOHERENT` | Requires loading transitive `VisibleOrphanModules` | Polymorphic wrapper vs. monomorphized call divergence | Coherent for non-overlapping superclasses (Bottu et al. 2019) |
| **Lexical + Companion Implicits** | Scala 3 (`dotc`) | None globally (`CanEqual` only); deterministic per scope | Full (anchor companions, no global orphan table) | Local override/specificity breaks parametricity; stdlib stores `Ordering` at runtime | `checkDivergence` via `typeSize` + `coveringSet` (`Implicits.scala:1850–1860`) |
| **F-ing / Functor Elaboration (`System` $F_\omega$)** | OCaml, SML, 1ML, MTC | Explicit in module paths (`Set.Make(Ord).t`) or stamps | Full via phase separation (MixML extends to recursive modules) | Explicit functor parameterization | Applicative shares diamonds (`F(X).t = F(X).t`); generative isolates state |
| **Tabled Elaboration + Scoped Extensions** | Lean 4 | None globally ("morally canonical" assumption) | Full per `.olean`; scope pops track `scopeChanged` | Priority + `local`/`scoped` overrides | Tabling eliminates $O(2^d)$ search blowup, but non-defeq diamonds fail `isDefEq` |

## Boundaries

- **Known not to apply**:
  - Rust's RFC 2451 sibling link-safety theorem holds only for `OrphanCheckMode::Proper` (`coherence.rs:21–33`) and does **not** hold for `OrphanCheckMode::Compat` (unsound projection covering, `rust-lang/rust#124559`/`#99554`).
  - `min_specialization`'s lifetime-erasure soundness (`min_specialization.rs:1–42`) does **not** cover traits marked `#[rustc_allow_lifetime_dependent_specialization]` (`TraitSpecializationKind::Marker`, `L58–66`) or full `#![feature(specialization)]` (`issue-40582.rs`).
  - Scala 3's `isCoherent` fast path (`Implicits.scala:1276, 1509`) applies **only** to `scala.CanEqual`, not general typeclasses.
  - OCaml applicative type sharing (`F(X).t = F(X).t`) does **not** apply to anonymous module arguments (`F(struct ... end)`) or generative `()` functors (`typemod.ml:2657–2747`).
- **Unsupported**:
  - `rustc` does **not** support RFC 1210's lattice specialization (chain-only in `specialization_graph.rs:158–162`), does **not** support specializing `async fn` / RPITIT (`check.rs:1445–1472`), and does **not** support user-facing `where T: !Trait` bounds or specialized negative auto-trait impls (`always_applicable.rs:84–179`).
  - OCaml does **not** support unannotated `module rec` (`typemod.ml:3033`) or subtyping between `Unit` and `Named` functors (`includemod.ml:655–673`).
- **Not examined**:
  - Haskell `TypeFamilyDependencies` / unsaturated type families (Kiss et al. 2019), Scala `DOT` calculus "bad bounds" / $D_{<:}$ undecidability (Amin et al. 2016; Hu & Lhoták POPL 2020), Coq/Rocq Canonical Structures & Hierarchy Builder, and Swift protocol witness-table retroactive conformance linking were not inspected at compiler-source level.
- **Unknown**:
  - Whether future generic const-parameter types (`<T, const N: T>`) invalidate `min_specialization`'s `ConstArgHasType` allowance (`min_specialization.rs:441–451`) remains unresolved upstream.
  - Whether `rustc`'s `FIXME(#132279)` (`coherence.rs:575, 705`) enables stable soundness regressions via opaque-type auto-trait leakage during negative coherence checks was not tested by compiling adversarial Rust inputs.
  - Whether a single language can unify 1ML's System $F_\omega$ modules, monomorphized zero-cost specialization, and invisible-by-default instance branding without sacrificing ergonomic type inference remains open.

## Evidence

### Verified Primary Academic Literature (Crossref & arXiv, `2026-11-19`)

| Paper | Identifiers | Role in Report |
| --- | --- | --- |
| P. Wadler & S. Blott, *"How to make ad-hoc polymorphism less ad hoc"*, POPL '89, pp. 60–76 (1989) | DOI `10.1145/75277.75283` | Type-class dictionary elaboration (§1) |
| R. Harper, J. C. Mitchell & E. Moggi, *"Higher-order modules and the phase distinction"*, POPL '90, pp. 341–354 (1990) | DOI `10.1145/96709.96744` | Phase separation & phase-splitting (§5.1) |
| X. Leroy, *"Applicative functors and fully transparent higher-order modules"*, POPL '95, pp. 142–153 (1995) | DOI `10.1145/199448.199476` | Applicative functor path identity (§5.3) |
| D. Dreyer, K. Crary & R. Harper, *"A type system for higher-order modules"*, POPL '03, pp. 236–249 (2003) | DOI `10.1145/604131.604151` | Applicative vs. generative effect soundness (§5.3) |
| D. Dreyer, R. Harper, M. M. T. Chakravarty & G. Keller, *"Modular type classes"*, POPL '07, pp. 63–70 (2007) | DOI `10.1145/1190216.1190229` | Type classes as canonical ML modules (§1.3) |
| D. Dreyer, *"Recursive type generativity"*, JFP 17(4–5), pp. 433–471 (2007) | DOI `10.1017/S0956796807006429` | RTG destination-passing solution to double vision (§5.4) |
| D. Dreyer, *"A type system for recursive modules"*, ICFP '07, pp. 289–302 (2007) | DOI `10.1145/1291151.1291196` | RMC recursive module calculus (§5.4) |
| A. Rossberg & D. Dreyer, *"Mixin' Up the ML Module System"*, ACM TOPLAS 35(1), pp. 1–84 (2013) | DOI `10.1145/2450136.2450137` | MixML separate compilation of recursive modules (§5.4) |
| A. Rossberg, C. V. Russo & D. Dreyer, *"F-ing modules"*, JFP 24(5), pp. 529–607 (2014) | DOI `10.1017/S0956796814000264` | System $F_\omega$ elaboration of ML modules (§5.2) |
| L. White, F. Bour & J. Yallop, *"Modular implicits"*, EPTCS 198, pp. 22–63 (2015) | DOI `10.4204/EPTCS.198.2`, `arXiv:1512.01895` | OCaml implicit module parameters (§1.3) |
| A. Rossberg, *"1ML – Core and modules united"*, JFP 28, e22 (2018) | DOI `10.1017/S0956796818000205` | Core/module unification via small/large & pure/impure $F_\omega$ (§5.2) |
| G.-J. Bottu, N. Xie, K. Marntirosian & T. Schrijvers, *"Coherence of type class resolution"*, PACMPL 3(ICFP), pp. 1–28 (2019) | DOI `10.1145/3341695`, `arXiv:1907.00844` | Two-step coherence proof for superclasses/flexible contexts (§1.2) |
| T. Schrijvers, B. C. d. S. Oliveira, P. Wadler & K. Marntirosian, *"COCHIS: Stable and coherent implicits"*, JFP 29, e3 (2019) | DOI `10.1017/S0956796818000242` | Deterministic & substitution-stable scoped implicits (§1.2) |
| D. Selsam, S. Ullrich & L. de Moura, *"Tabled Typeclass Resolution"* (2020) | `arXiv:2001.04301` | Tabled generator/consumer typeclass synthesis (§6.1) |
| A. Reynaud, G. Scherer & J. Yallop, *"A practical mode system for recursive definitions"*, PACMPL 5(POPL), pp. 1–29 (2021) | DOI `10.1145/3434326` | Five-mode recursive initialization safety (§5.4) |

### Pinned Upstream Repository Coordinates (`2026-11-19`)

- **`rust-lang/rfcs`** @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/1023-rebalancing-coherence.md` (L8–16, L172–258), `text/2451-re-rebalancing-coherence.md` (L58–84, L165–258), `text/1210-impl-specialization.md` (L992–1297), `text/1268-allow-overlapping-impls-on-marker-traits.md`.
- **`rust-lang/rust`** @ `b0b600668bb9b4a897e2299b0a44289d42276545`:
  - `compiler/rustc_next_trait_solver/src/coherence.rs` (L14–98, L129–257, L325–478): `InCrate`, `OrphanCheckMode`, `trait_ref_is_knowable`, `orphan_check_trait_ref`, opaque non-locality, `OwnedBox`, const ignore.
  - `compiler/rustc_hir_analysis/src/coherence/orphan.rs` (L22–288, L302–382) & `coherence/mod.rs` (L27–189): `orphan_check_impl`, auto-trait nominal/`dyn` bans, marker-trait empty check.
  - `compiler/rustc_trait_selection/src/traits/coherence.rs` (L172–265, L323–452, L562–593, L693–731): `overlap`, implicit & explicit negative disjointness, `FIXME(#132279)`.
  - `compiler/rustc_trait_selection/src/traits/specialize/{mod.rs,specialization_graph.rs}`: chain-only graph, `specializes`, `NegativePositiveConflict`.
  - `compiler/rustc_hir_analysis/src/impl_wf_check/min_specialization.rs` (L1–67, L114–150, L208–304, L317–457): `check_always_applicable`, `TraitSpecializationKind::{AlwaysApplicable, Marker}`, `ConstArgHasType` FIXME.
  - `compiler/rustc_hir_analysis/src/check/always_applicable.rs` (L39–179, L253–369) & `check/check.rs` (L1227–1286, L1445–1472): `check_negative_auto_trait_impl`, `check_specialization_validity`, RPITIT/`async fn` ban.
  - `library/core/src/pin.rs` (L1086–1087, L1699–1709), `library/alloc/src/boxed.rs` (L301–302), `library/core/src/ops/function.rs` (L73, L160, L239, L350), `library/core/src/marker.rs` (L150, L169, L186, L1072): `#[fundamental]` items & `helper::Pin`.
  - `tests/ui/specialization/issue-40582.rs`, `tests/ui/specialization/min_specialization/{specialize_on_static,repeating_lifetimes,repeating_param}.rs`, `tests/ui/specialization/soundness/{partial_ord_slice,partial_eq_range_inclusive}.rs`.
- **`ocaml/ocaml`** @ `d921d1e86c56baa7b30e890ced455c12255793f5`: `typing/includemod.ml` (L595–690), `typing/typemod.ml` (L2017–2102, L2192–2300, L2654–2756, L3021–3106), `typing/value_rec_check.ml` (L19–103).
- **`ghc/ghc`** @ `83038fbee5efea8e3ebd5090b2ff5537462e169d`: `compiler/GHC/Core/InstEnv.hs` (L348–401, L566–680).
- **`scala/scala3`** @ `90f3daf0a4795308d9c0e1b8f2265aeaecae8aa2`: `compiler/src/dotty/tools/dotc/typer/Implicits.scala` (L1276, L1365–1527, L1696–1860), `docs/_docs/reference/contextual/relationship-implicits.md`.
- **`leanprover/lean4`** @ `8009d0a64d2860606c6a5ac5ff6702622b24921e`: `src/Lean/Meta/SynthInstance.lean` (L20–125, L223–280, L618–653), `src/Lean/ScopedEnvExtension.lean` (L17–250).

### Execution Evidence (`support/verify_coherence_and_specialization.py`)

Executed `2026-11-19` on `Python 3.13.15` (exit `0`):

```console
python3 -B reports/coherence-orphan-instances-and-module-system-compilation/support/verify_coherence_and_specialization.py
```

Observed results:
- **Part A**: `silent_lookup_miss_for_10: true`; `corrupted_inorder_after_desc_insert_25: [10, 20, 30, 40, 50, 25]` (`corrupted_valid_under_asc: false`, `corrupted_valid_under_desc: false`); `branded_cross_union_rejected: true`; `branded_same_ord_union: [10, 25, 30, 50]`.
- **Part B**: `orphan_matrix_passed: 14`; `projection_compat_vs_proper_diverged: true`; `knowability_str_fnmut: "knowable"`, `knowability_str_foreign: "conflict_upstream"`, `knowability_local_foreign: "knowable"`, `knowability_param_foreign: "conflict_downstream"`; `link_safety_sibling_pairs_verified: 1764` (`42 × 42`, zero unifications); `ordering_bypass_collision_witnessed: true`.
- **Part C**: `witness_c1_static_pre_vs_post: [false, true]`, `witness_c2_issue_40582_pre_vs_post: [false, true]`, `witness_c3_repeated_ty_param_pre_vs_post: [false, true]`; `min_specialization` rejects C1, C2, C3, C4 (`Ord`), and `&'static u8`, and accepts `VecIntoIter<T>` (`min_spec_accepts_vec_into_iter_projection: true`).
- **Part D**: `applicative_diamond_equal: true`, `generative_calls_distinct: true`, `generative_inside_applicative_rejected: true`, `anonymous_arg_dependency_rejected: true`, `naive_recmodule_double_vision_conflict: true`, `rtg_destination_passing_internal_transparent: true`, `rtg_destination_passing_external_opaque: true`.

## Revalidation

1. **Re-run the standalone model probe** (`<1s`, Python 3.10+ stdlib only):
   ```console
   python3 -B reports/coherence-orphan-instances-and-module-system-compilation/support/verify_coherence_and_specialization.py
   ```
   This verifies the internal consistency of the abstract models only; it does not invoke the upstream compilers.
2. **Targeted `rust-lang/rust` diffs from `b0b600668bb9b4a897e2299b0a44289d42276545`**:
   - Inspect `tests/ui/specialization/issue-40582.rs` for removal of `//@ known-bug: #40582`.
   - Diff `compiler/rustc_hir_analysis/src/impl_wf_check/min_specialization.rs` (`TraitSpecializationKind::Marker`, `check_always_applicable`, `ConstArgHasType`).
   - Diff `compiler/rustc_next_trait_solver/src/coherence.rs` (`OrphanCheckMode::Compat`, `trait_ref_is_knowable`, `#[fundamental]` items) and `compiler/rustc_trait_selection/src/traits/coherence.rs` (`FIXME(#132279)`).
3. **Targeted OCaml / GHC / Scala 3 / Lean 4 diffs**:
   - **OCaml** (`d921d1e86c56baa7b30e890ced455c12255793f5`): diff `typing/includemod.ml` (`functor_param`) and `typing/typemod.ml` (`type_one_application`, `check_recmodule_inclusion`); check upstream status of modular implicits.
   - **GHC** (`83038fbee5efea8e3ebd5090b2ff5537462e169d`): diff `compiler/GHC/Core/InstEnv.hs` (`Note [Rules for instance lookup]` and `Note [When exactly is an instance decl an orphan?]`).
   - **Scala 3** (`90f3daf0a4795308d9c0e1b8f2265aeaecae8aa2`): grep `Implicits.scala` for `isCoherent` and `preferGeneral` migration flags.
   - **Lean 4** (`8009d0a64d2860606c6a5ac5ff6702622b24921e`): diff `src/Lean/Meta/SynthInstance.lean` around `backward.synthInstance.canonInstances` and `getInstancesLazy`.
