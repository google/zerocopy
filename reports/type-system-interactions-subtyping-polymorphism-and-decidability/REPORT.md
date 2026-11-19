# Type-System Feature Interactions: Subtyping, Polymorphism, Dependent Types, and Decidability Cliffs

## Summary

Individually tractable type-system features—Damas–Milner polymorphism, structural or nominal subtyping, local equality constraints (GADTs), dependent indices, linearity, impredicative propositions, and SMT-backed refinements—cross sharp mathematical barriers when combined. These cliffs stem from fundamental theorems (undecidability, non-existence of principal types, logical inconsistency, or subtyping lattice collapse) rather than implementation accidents, and every production compiler or proof assistant inspected here embeds explicit guardrails, fuel limits, or syntactic restrictions around them:

| Feature Combination | Fundamental Mathematical Barrier | Decidable / Practical Frontier | Production Implementation Anchor |
| :--- | :--- | :--- | :--- |
| **HM Polymorphism + Subtyping** | Equality unification fails on width/variance asymmetry; regular-tree canonicalization incurs product-automaton ($\text{lcm}$) blowup. | Algebraic subtyping / biunification over distributive polar lattices (`MLsub`, `Simple-sub`). | `LPTK/simple-sub` (`Typer.scala`, `TypeSimplifier.scala`): polar cache, level extrusion, NFA-to-DFA alignment. |
| **Bounded Quantification ($F_{<:}$)** | Full $F_{<:}$ subtyping is **undecidable** (Pierce 1994, two-counter machines) via contravariant quantifier bounds (`S-All`). | Kernel $F_{<:}$ (identical upper bounds on compared quantifiers). | Avoided in global inference; Scala 3 bounds checking uses cycle-set + depth cutoffs. |
| **Nominal Generics + Variance + Wildcards** | Contravariance + expansive inheritance + use-site wildcards make Java generic subtyping **Turing complete** (Grigore 2017; Kennedy & Pierce 2007); uninhabited wildcard bounds + `null` break soundness (Amin & Tate 2016). | Ban expansive contravariant inheritance or enforce Material/Shape separation (Greenman et al. 2014); remove `null` as universal bottom. | Scala 3 `TypeComparer.scala` switches to `monitoredIsSubType` at `LogPendingSubTypesThreshold = 50` (`DerefLimit = 10` for `LazyRef`). |
| **Path-Dependent Type Members (`DOT`)** | Core $D_{<:}$ subtyping is **undecidable** (Hu & Lhoták 2020); contradictory ("bad") bounds `{ type L >: Int <: String }` derive `Int <: String` via `S-Trans`, unsound under `null`/uninitialized inhabitants. | Strict CBV value-realizability invariant: concrete non-null objects fix equal bounds (`lo = hi`), making bad-bounds contexts unreachable (Amin et al. 2016; Rompf & Amin 2016). | Scala 3 `CheckRealizable.scala` (`boundsRealizability`, `memberRealizability`) and `Checking.scala` (`checkGoodBounds`), noting unchecked non-null gap. |
| **Higher-Rank & Impredicative Polymorphism** | Curry-style System F typability and checking are **equivalent and undecidable** (Wells 1999); undecidability starts at **rank 3** (Kfoury & Wells 1994); impredicative instantiation breaks principal types. | Bidirectional typing (Dunfield & Krishnaswami 2021); `Quick Look` local application-chain impredicativity (Serrano et al. 2020); explicit freezing (`FreezeML`). | GHC `GHC/Tc/Gen/App.hs` (`QLInstVar` infinite `TcLevel`, `qlUnify`, `qlZonkTcType`) monomorphizing unfilled vars before `tcValArgs`. |
| **GADTs + Local Equalities + Coverage** | Local equalities destroy principal types (`∀a. T a -> Bool` vs. `∀a. T a -> a` are incomparable); exhaustiveness reduces to **undecidable** type inhabitance. | `OutsideIn(X)` blocks outer meta-var unification under local Givens (Vytiniotis et al. 2011); `Lower Your Guards` guard DAGs with fuel-bounded oracles (Graf et al. 2020). | GHC `TcType.hs` (`isTouchableMetaTyVar`: `tv_tclvl == ctxt_tclvl`); `Pmc/Solver.hs` (`initFuel = 4`, depth cap `1` for branching factor `> 1`). |
| **Dependent DefEq + Unification + Erasure** | Extensional equality reflection makes typechecking **undecidable** (Hofmann 1995); 2nd-order unification is **undecidable** and lacks MGUs (Goldfarb 1981); counting linear uses in types breaks linearity. | Intensional conversion + Miller's decidable **pattern** fragment (Miller 1991); QTT `{0, 1, ω}` semiring places type formation at quantity `0` (Atkey 2018; Brady 2021). | Idris 2 `Core/Unify.idr` (`getVars`/`patternEnv`, postponing non-patterns) and `ZeroOneOmega.idr` + `LinearCheck.idr` (`0 * c = 0`). |
| **Universes + Impredicative `Prop` / `SProp`** | `Type : Type` is inconsistent (Girard/Hurkens 1995); unrestricted large elimination from proof-irrelevant `Prop`/`SProp` breaks soundness or forces definitional UIP (Gilbert et al. 2019). | Stratified universes (non-cumulative levels vs. cumulative graphs) + strict subsingleton or squashed elimination guards. | Lean 4 (`inductive.cpp:510-565`, `type_checker.cpp:267-285,371-377,906-913`): non-cumulative levels, `normalizes_to_zero`, subsingleton `Prop` elim. Rocq (`uGraph.ml`, `indTyping.ml:186-218`): cumulative graph, `SProp` gated by `allow_uip`. |
| **Liquid Refinements + Mutation / Aliasing** | Quantifier-free SMT Horn solving (Rondon et al. 2008) breaks under aliased mutation because heap framing requires undecidable quantified arrays. | Ownership-gated refinements (`Flux`, Lehmann et al. 2023): exclusive `&mut` enables strong updates; shared/weak refs stay invariant. | `flux-rs/flux` (`type_env.rs:132-149,250-266`): `result.is_strg` strong update (`PtrKind::Mut`) vs. weak `infcx.subtyping` vs. raw-pointer skip. |

**Key Architectural Invariant:** Because expressive surface inference and subtyping inevitably hit undecidability or non-principality, sound verification toolchains must decouple **incomplete/fuel-bounded surface elaborators** from **decidable, witness-checking core kernels** carrying explicit coercions, type applications, equality evidence, or proof certificates.

## Applicability

This report covers **27 primary subjects** recorded in `REPORT.json`—**20 peer-reviewed papers** (1981–2023) paired directly with **7 pinned upstream repository revisions** (`ghc/ghc@83038fbee5ef`, `scala/scala3@90f3daf0a479`, `idris-lang/Idris2@cf66cb4ccb8f`, `LPTK/simple-sub@ace6a33abb35`, `flux-rs/flux@7d9886b36347`, `leanprover/lean4@8009d0a64d28`, `rocq-prover/rocq@25f5b18a320e`)—plus the executable five-witness suite at `support/verify_type_interaction_witnesses.py`.

### Subject Pairing, Generalization, and Cross-References

- **Theory-to-Source Mapping:** `Dolan & Mycroft (2017)` + `Parreaux (2020)` $\leftrightarrow$ `LPTK/simple-sub`; `Pierce (1994)` + `Grigore (2017)` + `Amin & Tate (2016)` + `Amin et al. (2016)` + `Rompf & Amin (2016)` + `Hu & Lhoták (2020)` $\leftrightarrow$ `scala/scala3`; `Wells (1999)` + `Dunfield & Krishnaswami (2021)` + `Serrano et al. (2020)` + `Vytiniotis et al. (2011)` + `Graf et al. (2020)` $\leftrightarrow$ `ghc/ghc`; `Goldfarb (1981)` + `Miller (1991)` + `Atkey (2018)` + `Brady (2021)` $\leftrightarrow$ `idris-lang/Idris2`; `Gilbert et al. (2019)` $\leftrightarrow$ `leanprover/lean4` vs. `rocq-prover/rocq`; `Rondon et al. (2008)` + `Lehmann et al. (2023)` $\leftrightarrow$ `flux-rs/flux`.
- **Exact Observation vs. Broader Applicability:** Undecidability, non-principality, and inconsistency theorems apply to any language or IR embedding the corresponding syntactic fragment (contravariant bounded quantifiers, unannotated rank-3 polymorphism, unconstrained local equalities, second-order unification, or proof-irrelevant large elimination). Concrete heuristic parameters (`initFuel = 4`, `LogPendingSubTypesThreshold = 50`) and implementation gaps (`CheckRealizable` null-safety, `QLInstVar` solver leaks, Flux raw-pointer skips) are exact observations of the pinned commits and require revalidation on newer revisions.
- **Cross-References to Adjacent Corpus Packages:**
  - Rust-specific frontend crate metrics, `rustc_next_trait_solver` proof trees, Polonius borrow-check certificates, and THIR-to-MIR lowering are documented in `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering` (not duplicated here).
  - Lean 4 kernel RSS/memory ceilings (`-M768`), WHNF conversion-cost profiles, per-`inductive` eliminator heap costs, and external validator architectures are documented in `lean-kernel-memory-ceilings-whnf-scaling-and-validator-architectures` (not duplicated here).

## Findings

### 1. Subtyping × Parametric Polymorphism × Global Inference

#### 1.1 Why Damas–Milner Principal Types Break Under Subtyping

Basis: normative + derived + execution

Hindley–Milner global inference guarantees decidable **principal types** because equality constraints ($\tau_1 = \tau_2$) admit unique, finite, syntactic **most general unifiers (MGUs)** via Robinson unification with an occurs check. Introducing an asymmetric subtyping preorder ($\tau_1 <: \tau_2$) breaks this mechanism in three orthogonal ways:

1. **Asymmetric Width/Variance Flow Breaks Equality Unification:** Unifying `{a: α, b: int}` with `{a: β, c: bool}` across conditional branches fails on mismatched field sets (`{a, b} ≠ {a, c}`), even though both support `.a` via width subtyping; forcing equality destroys width polymorphism.
2. **Inequality Constraint Sets Lack Canonical Normal Forms:** Constrained polymorphic schemes $\forall \vec{\alpha}.\ C \Rightarrow \tau$ (where $C$ is a graph of $\alpha_i <: \beta_j$ inequalities) cannot eliminate constraints by simple substitution. Minimizing or deciding equivalence of subtype constraint graphs with recursive types and distributive lattices is PSPACE/EXPTIME-hard and degrades into huge, non-canonical inferred signatures.
3. **Invariant Mutable Constructors Reintroduce Equality Cliffs:** Invariant type constructors (`Ref<S> <: Ref<T>` iff `S <: T` and `T <: S`) collapse subtyping back to equality inside mutable cells or arrays. Mainstream OOP/subtyping languages (Java, Scala 3, C#, Swift, TypeScript) therefore abandon global HM inference for local bidirectional inference, incurring order-dependent failures on unannotated lambdas and invariant containers.

#### 1.2 Algebraic Subtyping: MLsub and Simple-sub Biunification, Polarity, and Canonicalization Blowup

Basis: normative + source + execution

**MLsub** (Dolan & Mycroft, POPL 2017, DOI `10.1145/3009837.3009882`) and **Simple-sub** (Parreaux, ICFP 2020, DOI `10.1145/3409006`) restore **decidable, principal global type inference with structural subtyping** for rank-1 functional calculi without qualified constraint sets. Types live in a **distributive lattice** of positive unions ($\sqcup, \bot$) and negative intersections ($\sqcap, \top$) restricted to **polar normal forms**: unions appear only in positive (covariant/producer) positions and intersections only in negative (contravariant/consumer) positions.

Direct inspection of `LPTK/simple-sub@ace6a33abb35` (`shared/src/main/scala/simplesub/Typer.scala` and `TypeSimplifier.scala`) pins the exact algorithm:

- **Biunification (`Typer.scala:88-129`):** `constrain(lhs, rhs)` maintains mutable `lowerBounds` and `upperBounds` on each `Variable(level, lowerBounds, upperBounds)`. When `lhs: Variable` has `rhs.level <= lhs.level`, `rhs` is pushed to `lhs.upperBounds` and transitively propagated via `lhs.lowerBounds.foreach(constrain(_, rhs))` (and dually for `rhs: Variable`). Memoizing `(lhs, rhs)` pairs whenever either side is a `Variable` (`Typer.scala:100-104`) guarantees termination on regular cycles.
- **Polar Extrusion (`Typer.scala:134-159`):** Crossing polymorphism levels uses `extrude(ty, pol)` with a polar cache `MutMap[(Variable, Boolean), Variable]`, copying inner variables down to outer level `lvl` as conservative upper-bound (positive) or lower-bound (negative) proxies so each `let` instantiation stays independent.
- **Polar Coalescing and Exact Condition for Equi-Recursive (`μ`) Emergence (`Typer.scala:239-258`):** `coalesceType` folds `tv.lowerBounds` with `Union` positively (`pol = true`) and `tv.upperBounds` with `Inter` negatively (`pol = false`), tracking `(Variable, Boolean)` in `inProcess`. **Recursive `μ`-types arise strictly on same-polarity cycles.** Verified by `support/verify_type_interaction_witnesses.py` (`witness_1_biunification_vs_hm`):
  1. *Heterogeneous record branches:* `if cond then {a = 1, b = true} else {a = false, c = 2}` fails HM unification, while `Simple-sub` infers `(a1 | int | bool)` for `.a` and rejects accessing non-common field `.b`.
  2. *Self-application (`λx. x x`) is non-recursive:* HM rejects `λx. x x` via the occurs check, yet `Simple-sub` infers the **non-recursive** polar intersection `((a0 & (a0 -> a1)) -> a1)` (`needs_mu = false`) because `a0` appears once negatively (outer parameter) and once positively (argument of `a0 -> a1` under negative polarity). Likewise, the untyped Y combinator types without `let rec`, so pure MLsub/Simple-sub is **not strongly normalizing**.
  3. *Same-polarity cycles induce positive/negative `μ`:* `let rec stream = λx. {head = x, tail = stream x}` produces positive recursive `(a0 | (a1 -> {head: a1, tail: (mu mu0. (a2 | {head: a1, tail: mu0}))}))`, while `let rec peel_a = λx. peel_a (x.a)` produces negative recursive `(a0 | ((mu mu0. (a1 & {a: (a2 & mu0)})) -> a3))`.
- **Canonicalization `lcm` Blowup (`TypeSimplifier.scala:86-158`):** While `compactType` (`L49-84`) merges single-variable bounds linearly, `canonicalizeType` (`L102-158`) merges co-occurring recursive types by unrolling them until cycle lengths align. Parreaux notes verbatim (`TypeSimplifier.scala:89-101`): *"if they have different cycle lengths, we create a new recursive type whose cycle length is the LCD [least common multiple] of the respective original cycle lengths... akin to the powerset construction for turning NFAs into DFAs, and can in principle result in an exponentially larger type."* Our probe confirms five coprime cycle periods `[2, 3, 5, 7, 11]` (28 input nodes) expand to an aligned product cycle of `2310`. Furthermore, extending algebraic subtyping cleanly to higher-rank polymorphism, GADTs, or invariant mutable cells remains hard, and polar error localization degrades when constraints propagate transitively across many binders.

#### 1.3 Bounded Quantification Undecidability (Full vs. Kernel System $F_{<:}$)

Basis: normative + derived

System $F_{<:}$ extends System F with upper-bounded quantifiers $\forall \alpha <: \tau_1.\ \tau_2$. Two subtyping rules for universal types divide decidability:

```text
Kernel F_<: (Decidable):                 Full F_<: (Undecidable):
  Γ, α <: U ⊢ T₁ <: T₂                    Γ ⊢ U₂ <: U₁    Γ, α <: U₂ ⊢ T₁ <: T₂
  ──────────────────────────── (S-All-K)  ──────────────────────────────────────── (S-All-F)
  Γ ⊢ (∀α<:U. T₁) <: (∀α<:U. T₂)          Γ ⊢ (∀α<:U₁. T₁) <: (∀α<:U₂. T₂)
```

**Pierce (POPL 1992; *Information and Computation* 112(1), 1994, DOI `10.1006/inco.1994.1055`)** proved subtyping (and hence typechecking) in **full $F_{<:}$** is **undecidable** via reduction from **two-counter Turing machines**. Undecidability arises from the interaction of three mechanisms inside `S-All-F`: (1) contravariant bound flipping ($U_2 <: U_1$), (2) extending $\Gamma$ with fresh upper bounds $\alpha <: U_2$ referencing earlier variables, and (3) left-hand variable promotion (`S-Trans-TVar`) substituting $\alpha$ by $U_2$ to re-expose nested quantifiers. Restricting to `S-All-K` ($U_1 = U_2$) makes subtyping decidable because the right-hand type shrinks strictly whenever $\Gamma$ grows, but rejects contravariant bound refinement common in OOP/generic interfaces.

#### 1.4 Nominal Variance, Wildcards, and Turing-Complete Subtyping

Basis: normative + source + execution

Mainstream OOP generics (Java, Scala, C#, Kotlin) replace structural $F_{<:}$ with **nominal inheritance**, declaration-site variance (`in`/`out`) or use-site existential wildcards (`? extends T`, `? super T`), and F-bounded recursion (`Comparable<T extends Comparable<T>>`).

- **Undecidability & Turing Completeness:** **Kennedy & Pierce (2007)** proved nominal subtyping with declaration-site contravariance and **expansive inheritance** (inheriting a supertype that nests constructors around type parameters along a cycle) is undecidable. **Grigore (POPL 2017, DOI `10.1145/3009837.3009871`)** resolved the Java conjecture by proving **Java generic subtyping is Turing complete**, using contravariant wildcards (`? super ...`) and wildcard capture conversion to simulate arbitrary Turing machines inside `javac`.
- **Executable Non-Termination Witness (`support/verify_type_interaction_witnesses.py`, `witness_4_contravariant_expansive_divergence`):** Under the minimal contravariant expansive hierarchy (realizable via `in` variance or Java `? super` wildcards):
  ```text
  interface N<in X> {}
  interface C<in X> extends N<N<C<C<X>>>> {}
  ```
  evaluating $C^1(T) <: N(C^1(T))$ generates a strictly growing infinite chain incrementing $k \to k+1$ every four steps:
  $$C^k(T) <: N(C^k(T)) \xrightarrow{\text{super}} N(N(C^{k+1}(T))) <: N(C^k(T)) \xrightarrow{\text{contra}} C^k(T) <: N(C^{k+1}(T)) \xrightarrow{\text{super, contra}} C^{k+1}(T) <: N(C^{k+1}(T)).$$
  Because every pair has strictly larger syntactic depth than all ancestors, **cycle-set memoization never triggers**. In our probe, the expansive check exhausts 24 steps (`unique_pairs_visited = 24`, depth climbing `2 -> 9`), whereas non-expansive `C<in X> extends N<N<X>>` terminates (`refuted`) in 5 steps at max depth `2`.
- **Decidable Fragments:** Banning expansive or contravariant inheritance cycles restores decidability (Kennedy & Pierce 2007). **Greenman, Muehlboeck & Tate (PLDI 2014, DOI `10.1145/2594291.2594308`)** achieve practical decidability via **Material/Shape separation**, forbidding recursive F-bound *Shapes* (like `Comparable<T>`) from appearing as type arguments to other generics or in contravariant cycles.

#### 1.5 Path-Dependent Type Members, DOT "Bad Bounds," and the Realizability Dilemma

Basis: normative + source + execution

Scala 3 grounds generics, modules, and OO inheritance in **Dependent Object Types (DOT)** (Amin, Grütter, Odersky, Rompf & Stucki, WadlerFest 2016, DOI `10.1007/978-3-319-30936-1_14`; soundness proof by Rompf & Amin, OOPSLA 2016, DOI `10.1145/2983990.2984008`). Objects expose abstract type members `{ type L >: S <: U }` with selection rules:

$$\frac{\Gamma \vdash x : \{ L : S..U \}}{\Gamma \vdash S <: x.L}\text{ (S-Sel1)} \qquad \frac{\Gamma \vdash x : \{ L : S..U \}}{\Gamma \vdash x.L <: U}\text{ (S-Sel2)}$$

Two deep cliffs follow directly:

1. **Undecidability of Core $D_{<:}$ (Hu & Lhoták, POPL 2020, DOI `10.1145/3371077`):** Even without recursive self-types or intersections, subtyping in $D_{<:}$ is **undecidable** (encoding full $F_{<:}$ via $\forall (x : \{ L : \bot..U \}).\ [x.L/\alpha]T$); decidable fragments (*strong kernel* $D_{<:}$) must ban contravariant bound narrowing. In **`scala/scala3@90f3daf0a479`**, `TypeComparer.scala:1672-1675` counts recursion depth in `recCount`, switching to cycle-monitored `monitoredIsSubType` (`TypeComparer.scala:292-331`, normalizing `LazyRef` up to `DerefLimit = 10` at `L306,314`) once `recCount >= Config.LogPendingSubTypesThreshold` (`50`, `config/Config.scala:198`; alongside `LogPendingUnderlyingThreshold = 50` and `LogPendingAppliedTypeParamRefsThreshold = 30`, `Config.scala:195,201`), falling back to `ctx.handleRecursive` against strictly growing derivations.
2. **"Bad Bounds" Transitivity Collapse & Null Soundness Failure:** In a context containing `x : { type L >: Int <: String }` (or `{ type L >: Top <: Bot }`), `S-Sel1`, `S-Trans`, and `S-Sel2` derive **`Int <: x.L <: String`** (or **`Top <: x.L <: Bot`**), breaking transitivity elimination and subtyping inversion in arbitrary environments $\Gamma$.
   - **Soundness Restoration (Rompf & Amin 2016):** In call-by-value DOT *without `null`*, every concrete runtime object `v = ν(x) { type L = T; ... }` fixes equal bounds `T <: T` (*good bounds*), so bad-bounds functions are vacuously sound because no runtime value can ever invoke them.
   - **Real-World Exploit Under `null` (Amin & Tate, OOPSLA 2016, DOI `10.1145/2983990.2984004`):** Because Java (wildcards + `null`) and Scala 2 (type projections + `null`) allowed `null` to inhabit an uninhabited bounded type, callers could invoke a bad-bounds coercion function with `null` and cast any type `A` to `B` without casts, crashing at runtime with `ClassCastException`. Probe Witness 3 (`witness_3_dot_bad_bounds_vs_realizability`) reproduces both the 5-step `Int <: x.L <: String` / `Top <: x.L <: Bot` derivations and the runtime `AttributeError` when `None` inhabits `x`, contrasted against `dot_check_realizable` rejecting `{L >: Int <: String}` as `HasProblemBounds`.
   - **Scala 3 Realizability Guard & Explicit Null Gap (`scala/scala3@90f3daf0a479`):** Scala 3 bans unconstrained abstract type projections `T#L` and checks realizability in `core/CheckRealizable.scala:55-204` (`boundsRealizability` at `L140-177` checking `!(mbr.info.loBound <:< mbr.info.hiBound)` on type members, refinements, and base types; `typer/Checking.scala:89-101` `checkGoodBounds`/`findBadBounds`). Crucially, `CheckRealizable.scala:78-81` admits: *"We don't check yet the 'not null' clause: that will require null-safety checking,"* and `memberRealizability` (`L196-204`) gates deep field checks behind `sourceVersion.isAtLeast(future)` until nullability tracking is standard.

---

### 2. Higher-Rank Polymorphism, Impredicativity, and GADTs

#### 2.1 System F Inference Undecidability and the Rank-2 / Rank-3 Cliff

Basis: normative + derived

While Church-style System F (explicit $\Lambda\alpha.\ e$ and $e\ [\tau]$) has decidable type checking, **Wells (LICS 1994; *Annals of Pure and Applied Logic* 98, 1999, DOI `10.1016/S0168-0072(98)00047-5`)** proved that for **Curry-style System F** (untyped $\lambda$-terms with implicit quantifier introduction/instantiation), **typability and type checking are computationally equivalent and undecidable** (by reduction from semi-unification, in both $\lambda K$ and $\lambda I$). By **Kfoury & Wells (1994)**, rank-2 typability remains decidable (via acyclic semi-unification) while **rank $\ge 3$ typability is already undecidable**—meaning no annotation-free global inference algorithm can handle higher-rank signatures like Haskell's `runST :: (forall s. ST s a) -> a` or Rust's `for<'a> Fn(&'a T) -> &'a U`.

#### 2.2 Bidirectional Typing vs. GHC Quick Look Impredicativity

Basis: normative + documentation + source

Practical higher-rank languages navigate Wells's barrier via **bidirectional typing** (**Dunfield & Krishnaswami**, ICFP 2013; *ACM Computing Surveys* 54(5), 2021, DOI `10.1145/3450952`), splitting judgments into **synthesis** ($\Gamma \vdash e \Rightarrow A$, inferring variables, annotated terms, and applications) and **checking** ($\Gamma \vdash e \Leftarrow A$, propagating known types into lambdas and skolemizing outer $\forall$ binders). This is sound, complete, and decidable for **predicative** higher-rank polymorphism relative to an annotation discipline, though syntactically fragile under transformations that reverse information flow (e.g., `f x` vs. `x |> f`).

Allowing **impredicative instantiation** (instantiating a type variable $\alpha$ with a polytype $\forall\beta.\ \sigma$, e.g., `[forall a. a -> a]`) destroys principal types even with lambda annotations: applying `id :: forall a. a -> a` to `id` admits incomparable System F elaborations (`id @(forall b. b -> b) id` vs. `Λb. id @(b -> b) (id @b)`), and `single id` admits both `[forall a. a -> a]` and `forall a. [a -> a]`. Three designs span the trade-off:
- **MLF (Le Botlan & Rémy 2003):** Complete principal inference via instance-bounded quantifiers, at high type-syntax and typeclass complexity.
- **FreezeML (Emrich et al., PLDI 2020, DOI `10.1145/3385412.3386003`):** Complete System F inference via an explicit syntactic freeze operator suppressing automatic instantiation.
- **Quick Look (Serrano, Hage, Peyton Jones & Vytiniotis, ICFP 2020, DOI `10.1145/3408971`):** Deployed in GHC (`-XImpredicativeTypes`), trading completeness (argument-order and $\eta$-sensitivity) for zero syntactic freeze markers and compatibility with `OutsideIn(X)`.

Direct inspection of **`ghc/ghc@83038fbee5ef`** pins GHC's exact Quick Look implementation:
- `compiler/GHC/Tc/Utils/TcType.hs:738-739,790-807,861,898` encodes instantiation variables directly as an infinite `TcLevel` constructor:
  ```haskell
  data TcLevel = TcLevel {-# UNPACK #-} !Int | QLInstVar
  ```
  Because `strictlyDeeperThan QLInstVar (TcLevel {}) = True`, standard skolem-escape level checks prevent ordinary finite-level unification variables from unifying with a `QLInstVar`.
- `compiler/GHC/Tc/Gen/App.hs:79-167,306-355` (`Note [Quick Look overview]`, `Note [Instantiation variables are short lived]`) runs a three-phase n-ary application pipeline in `tcApp` / `tcInstFun`: (1) instantiate head $\forall$ binders with fresh `QLInstVar`s (the only variables `qlUnify` may fill with polytypes); (2) run `quickLookArg` on **all** value arguments *before* `quickLookResultType` (`App.hs:337-355`); and (3) monomorphize any unfilled `QLInstVar` into an ordinary finite-level meta-variable via `qlZonkTcType` (`App.hs:101-122`) prior to `tcValArgs`.
- `App.hs:132-166` explicitly documents two boundaries where Quick Look leaks into the constraint solver: (i) emitted class constraints `Dict kappa` later rewritten to `Dict (forall b. b -> b)` (`#18987`, benign only because the constraint solver performs no implicit instantiation), and (ii) visible type-application wildcards `@_` with polymorphic kinds (`VisFlag1_ql`) leaving deferred `QLInstVar`s in kind constraints. Quick Look is also enabled unconditionally for select `Id`s like `($)` (`App.hs:306-310`).

#### 2.3 GADTs, Local Equality Constraints, Principal-Type Loss, and OutsideIn(X)

Basis: normative + source + execution

Pattern matching on a GADT introduces **local `Given` type equalities** scoped to a single branch, destroying principal types in Damas–Milner/System F (**Vytiniotis, Peyton Jones, Schrijvers & Sulzmann, JFP 2011, DOI `10.1017/S0956796811000098`**):

```haskell
data T a where T1 :: T Bool
f x = case x of { T1 -> True }
```

Inside `T1`, Given is `a ~ Bool` and RHS is `Bool`. Probe Witness 2 (`witness_2_gadt_non_principality_outsidein`) mechanically verifies: (1) both `∀a. T a -> Bool` and `∀a. T a -> a` are valid typings; (2) neither is an instance of the other; and (3) their HM anti-unifier `∀a b. T a -> b` is unsound (`a ~ Bool ⊬ Bool ~ b`).

**`OutsideIn(X)` in `ghc/ghc@83038fbee5ef`** enforces modularity by collecting a tree of implication constraints $\forall \vec{a}.\ Q_{\text{given}} \supset Q_{\text{wanted}}$ governed by four `TcLevel` invariants (`GHC/Tc/Utils/TcType.hs:745-855`): `ImplicInv` (strictly increasing child implication levels), `SkolInv` (skolems at implication level), `GivenInv` (meta-vars in `ic_given` strictly shallower than `ic_tclvl`, preventing same-level Wanted unifications from mutating Givens), and `WantedInv` (meta-vars in `ic_wanted` $\le$ `ic_tclvl`, preventing skolem escape). The critical untouchability gate is `isTouchableMetaTyVar` (`TcType.hs:1220-1229`):

```haskell
isTouchableMetaTyVar ctxt_tclvl tv
  | isTyVar tv
  , MetaTv { mtv_tclvl = tv_tclvl, mtv_info = info } <- tcTyVarDetails tv
  , isTouchableInfo info
  = assertPpr (checkTcLevelInvariant ctxt_tclvl tv_tclvl) ... $
    tv_tclvl `sameDepthAs` ctxt_tclvl
  | otherwise = False
```

Entering a GADT match pushes `TcLevel` (`pushTcLevel`, `TcType.hs:891`), so any outer return meta-variable `beta[1]` fails `sameDepthAs` at level `2` and becomes **untouchable** (`GHC/Tc/Solver/Equality.hs:2072-2075`; `GHC/Tc/Solver.hs:1199-1201,1665-1667`). As verified in Witness 2, unannotated `f` is rejected (`blocked_untouchable(beta[lvl=1] at implic_lvl=2)`), while supplying *either* explicit user signature (`T a -> Bool` or `T a -> a`) propagates expected types **outside-in** so `a ~ Bool` cleanly discharges the implication (`discharged_by_givens`).

#### 2.4 GADT Pattern-Match Exhaustiveness, Guardedness, and Non-Termination (`Lower Your Guards`)

Basis: normative + source

With GADTs, type families, laziness, and strict fields, pattern-match coverage reduces to **residual type/value inhabitance**, which is **NP-hard** for finite propositional constraints and **undecidable** in general (Karachalias, Schrijvers, Vytiniotis & Peyton Jones, ICFP 2015, DOI `10.1145/2784731.2784748`). **Lower Your Guards (LYG)** (**Graf, Peyton Jones & Scott, ICFP 2020, DOI `10.1145/3408989`**) desugars patterns, guards, `COMPLETE` pragmas, and `EmptyCase` into compositional guard DAGs (`GdOne`/`GdEnd`/`GdSeq`/`GdAlt`, `ghc/ghc@83038fbee5ef`, `compiler/GHC/HsToCore/Pmc/Check.hs:165-185`) checked against refinement states `Nabla` combining: (1) `tyOracle` (`Pmc/Solver.hs:622-639`) calling `tcCheckGivens` to refute contradictory GADT equalities; (2) `ResidualCompleteMatches` (`Pmc/Solver.hs:131-262`) tracking negative `x /~ K` constraints; and (3) `addBotCt` (`Pmc/Solver.hs:683-686`) modeling non-strict $\bot$ vs. strict (`!`) fields.

Direct inspection of **`GHC/HsToCore/Pmc/Solver.hs:593-609,1725-1780`** (`Note [Fuel for the inhabitation test]`) documents two concrete coverage cliffs:
1. **Inductive Uninhabitability / Non-Termination:** Strict recursive types with no base case (`data Abyss = MkAbyss !Abyss`, `newtype Chasm = MkChasm Chasm`) admit no terminating values, so `case x of {}` is semantically exhaustive, yet finite constructor instantiation cannot prove emptiness without induction (`Pmc/Solver.hs:1734-1751`, noting false non-exhaustive warnings).
2. **Exponential Branching & Fuel Caps:** Strict branching types (`data T = MkT !T !T !T`, `Pmc/Solver.hs:1758-1777`) explode exponentially in inhabitation depth. GHC therefore hard-caps `initFuel = 4` (`Pmc/Solver.hs:596`, reduced from `defaultRecTcMaxBound = 100` after `#17977`) and drops maximum recursion depth to `1` whenever constructor branching factor exceeds `1` (`Pmc/Solver.hs:1766-1771`).

---

### 3. Dependent Types, Erasure, Universes, and Mutable Refinements

#### 3.1 Definitional Equality, Higher-Order Unification, and Miller's Pattern Fragment

Basis: normative + source + execution

Dependently typed systems face two independent undecidability boundaries in conversion checking and implicit elaboration:

1. **Extensional vs. Intensional Conversion:** Promoting propositional proofs $p : t =_A u$ into definitional equality $t \equiv u$ (**Extensional Type Theory**) makes **type checking undecidable** (Hofmann 1995). Lean 4, Rocq, Agda, and Idris 2 therefore adopt **Intensional Type Theory**, restricting kernel conversion to $\beta\delta\iota\zeta\eta$-reduction (plus proof irrelevance where configured) and requiring explicit `transport`/`cast` for non-definitional equalities like `n + 0 = n`. For Lean 4 kernel WHNF scaling and memory ceilings, see `lean-kernel-memory-ceilings-whnf-scaling-and-validator-architectures`.
2. **Higher-Order Unification vs. Miller's Pattern Fragment:** **Goldfarb (*TCS* 13(2), 1981, DOI `10.1016/0304-3975(81)90040-2`)** proved even **second-order unification** is **undecidable** and lacks MGUs. **Miller (*JLC* 1(4), 1991, DOI `10.1093/logcom/1.4.497`)** isolated the decidable **higher-order pattern fragment**—metavariables applied solely to **distinct bound local variables** $?M\ x_1 \dots x_n$—which admits unique MGUs.
   - **Direct Source Audit of `idris-lang/Idris2@cf66cb4ccb8f` (`src/Core/Unify.idr:211-359`):** `getVars` (`L278-290`) and `patternEnv` (`L304-359`) enforce Miller's exact three conditions (distinct local variable arguments, occurs check, and RHS free variables contained in the spine via `Thin newvars vars`). Every non-pattern constraint (repeated variable, constructor argument, stuck function) is suspended via `postpone` (`L211-260`) rather than guessed eagerly.
   - **Executable Witness (`witness_5_qtt_semiring_and_miller_hou`):** Verifies over binary $\lambda u\, v.\ f(a, b)$ that Miller pattern `?M(x, y) =?= f(y, x)` has **1 unique MGU** (`lambda u v. f(v, u)`), whereas repeated-variable non-pattern `?M(x, x) =?= f(x, x)` admits **4 incomparable solutions** (`f(u,u)`, `f(u,v)`, `f(v,u)`, `f(v,v)`).

#### 3.2 Quantitative Type Theory: Uniting Compile-Time Erasure and Runtime Linearity

Basis: normative + source + execution

In a linear dependent type $\Pi (x : A).\ B(x)$, $x$ appears in both the type $B(x)$ and the runtime body: counting type-level occurrences breaks linearity, while ignoring them naively risks types depending on consumed resources. **Quantitative Type Theory (QTT)** (McBride 2016; **Atkey, LICS 2018, DOI `10.1145/3209108.3209189`**; **Idris 2**, **Brady, ECOOP 2021, DOI `10.4230/LIPIcs.ECOOP.2021.9`**) resolves this by annotating every context binder with a multiplicity from the semiring $\{0, 1, \omega\}$ and **placing all type formation at quantity `0`**.

Direct inspection of **`idris-lang/Idris2@cf66cb4ccb8f`**:
- **Mechanized `{0, 1, ω}` Semiring (`src/Algebra/ZeroOneOmega.idr:9-135`):** Defines `data ZeroOneOmega = Rig0 | Rig1 | RigW`, preorder `Rig0 <= _`, `Rig1 <= Rig1`, `_ <= RigW` (`L14-30`), additive splitting `rigPlus` (`0 + a = a`, `1 + 1 = ω`, `L46-49`), and multiplicative scaling `rigMult` (`0 * _ = 0`, `_ * 0 = 0`, `1 * a = a`, `L52-57`), with mechanized associativity/commutativity proofs (`L77-135`; all 27 triples re-verified in Probe Witness 5).
- **Type-Level Annihilation & Linear Enforcement (`src/Core/LinearCheck.idr:156-255,365-391`):** `lcheck` (`L161-176`) rejects usage violations via `rigSafe l r` (`l < r => throw LinearMisuse`) and zeros outer linear variables inside unrestricted `RigW` lambdas via `eraseLinear env` (`L236-240`). `lcheckBinder` (`L371-390`) checks every binder's type annotation (`Lam`, `Let`, `PVar`, `PLet`, `PVTy`) strictly at `erased` (`Rig0`) and scales `Pi fc c x ty` by `rig |*| c` (`L378-380`), so at `rig = Rig0`, `0 * 1 = 0` annihilates type-level usage of linear variables.
- **Inherent QTT Limitations:** (1) Because type formation lives strictly at `0`, types cannot inspect or enforce quantity-`1` resource invariants inside type formers (blocking strong linear $\Sigma$-types without graded modal extensions; Atkey 2018); (2) runtime code cannot pattern-match directly on a `0`-erased index (it must match a runtime-relevant indexed constructor like `Nil`/`Cons`); and (3) absence of **quantity polymorphism** forces duplicating higher-order combinators across `0`, `1`, and `ω` arrow multiplicities.

#### 3.3 Universe Hierarchies, Cumulativity, and Impredicative `Prop` / `SProp` Consistency Limits

Basis: normative + source

Because `Type : Type` is inconsistent (**Girard's paradox**, simplified by **Hurkens, TLCA 1995, DOI `10.1007/BFb0014058`**), dependent kernels stratify types into predicative universes $\text{Type}_0 : \text{Type}_1 : \dots$ plus optional impredicative propositional sorts. Direct side-by-side audit of `leanprover/lean4@8009d0a64d28` and `rocq-prover/rocq@25f5b18a320e` exposes three sharp kernel trade-offs:

| Kernel Axis | Lean 4 (`leanprover/lean4@8009d0a64d28`) | Rocq (`rocq-prover/rocq@25f5b18a320e`) | Metatheoretic Trade-Off |
| :--- | :--- | :--- | :--- |
| **Cumulativity** | **Non-cumulative** algebraic `Level` (`0`, `u+1`, `max`, `imax` in `src/kernel/level.cpp`). | **Cumulative** universe constraint graph (`kernel/uGraph.ml:49-102`, `check_leq`, `UniverseInconsistency`; Sozeau & Tabareau ITP 2014, DOI `10.1007/978-3-319-08970-6_32`). | Lean 4 keeps conversion subtyping-free (requiring `ULift`/`PLift`); Rocq avoids lifting boilerplate at the cost of subtyping in conversion + non-local universe cycles. |
| **Impredicative Proof Irrelevance** | Single impredicative `Prop` ($\text{Sort } 0$), **definitionally proof-irrelevant** (`src/kernel/type_checker.cpp:906-913`, `is_def_eq_proof_irrel`). | Split into proof-**relevant** `Prop` and strictly proof-**irrelevant** `SProp` (`kernel/sorts.ml:166-290`; Gilbert et al. POPL 2019, DOI `10.1145/3290316`). | Definitional proof irrelevance + large elimination of inductive equality yields definitional UIP / Axiom K. |
| **Large Elimination (`Prop`/`SProp` $\to$ `Type`)** | **Subsingleton elimination** (`src/kernel/inductive.cpp:510-565`, `elim_only_at_universe_zero`): permitted iff 0 ctors (`False`), or 1 non-mutual ctor whose non-param args live in `Prop` or occur in indices (allowing `Eq.rec`, `Acc.rec`). | `Prop`: singleton elimination allowed (enabling `eq_rect` without UIP). `SProp` (`kernel/indTyping.ml:190-212`): 1-ctor inductives with args always squash; **0-arg 1-ctor inductives (`sEq`) squash UNLESS `typing_flags.allow_uip` is set**. | Unrestricted large elimination from proof-irrelevant `Prop` derives `true = false`. Squashing `sEq` in Rocq's `SProp` preserves univalent/HoTT compatibility without UIP (Gilbert et al. 2019). |
| **Structure Projection Guard** | `type_checker.cpp:267-285,371-377`: `infer_proj` rejects projecting non-`Prop` fields from `Prop` structures; `is_prop` tests `normalizes_to_zero(sort_level(s))` (catching `imax 1 0`). | `indTyping.ml:239-241,531-545`: primitive records require `not (Option.has_some info.ind_squashed)` so projections cannot extract data from squashed `Prop`/`SProp`. | Lean 4 `type_checker.cpp:373-376` explicitly notes that syntactic `s == Prop` misses `imax 1 0` and would let `infer_proj` extract non-proof data from a proof, contradicting proof irrelevance. |

#### 3.4 Liquid / Refinement Types Under Mutation, Aliasing, and Higher-Order State

Basis: normative + source + derived

**Liquid Types** (**Rondon, Kawaguchi & Jhala, PLDI 2008, DOI `10.1145/1375581.1375602`**) infer refinements automatically by generating Constrained Horn Clauses (CHCs) over decidable quantifier-free SMT theories (`QF_LIA`, `QF_UFLIA`) and solving them via predicate abstraction over finite qualifiers. Adding **aliased mutable state** breaks this immediately: if `p` and `q` alias and `p : Ref<{v: Int | v > 0}>`, writing `*q = 0` invalidates `p`'s refinement unless references are restricted to weak *invariant* refinements or writes encode quantified heap framing ($\forall a.\ a \neq q \implies H'[a] = H[a]$), exiting decidable QF-SMT into heuristic E-matching divergence.

**Flux** (**Lehmann, Geller, Vazou & Jhala, PLDI 2023, DOI `10.1145/3591283`**) recovers quantifier-free **strong updates** for Rust by leveraging Rust's exclusive `&mut` ownership guarantee. Direct inspection of **`flux-rs/flux@7d9886b36347`** (`crates/flux-refineck/src/type_env.rs`) pins the exact three-way boundary:

```rust
// type_env.rs:140-148 (borrow)
let result = self.bindings.lookup_unfolding(infcx, place, span)?;
if result.is_strg && mutbl == Mutability::Mut {
    Ok(Ty::ptr(PtrKind::Mut(re), result.path()))
} else {
    Ok(Ty::mk_ref(re, result.ty, mutbl))
}

// type_env.rs:259-265 (assign)
let result = self.bindings.lookup_unfolding(infcx, place, span)?;
if result.is_strg {
    result.update(new_ty);
} else if !place.behind_raw_ptr(infcx.genv, self.local_decls)? {
    infcx.subtyping(&new_ty, &result.ty, ConstrReason::Assign)?;
}
```

1. **Strong place (`result.is_strg`):** Uniquely owned places and strong borrows (`PtrKind::Mut`) perform flow-sensitive **strong updates** (`result.update(new_ty)`) inside `PlacesTree` (`type_env.rs:46-49`).
2. **Weak/invariant reference (`!result.is_strg`, safe Rust):** Assignment checks `new_ty <: result.ty` via `infcx.subtyping`, preserving an invariant refinement without heap quantifiers.
3. **Raw pointers (`behind_raw_ptr`):** Flux skips refinement checking on assignment (`type_env.rs:262`), because raw pointers relinquish aliasing exclusion.

**Remaining Hard Walls:** Shared interior mutability (`RefCell`, `Mutex`, atomics), cyclic aliased graphs outside tree-shaped `PlacesTree` paths, higher-order stateful closures (`FnMut`) whose captured refinements mutate across calls, non-linear/inductive properties beyond QF-SMT, and trusting the SMT solver unless verdicts are reconstructed into kernel-checked proof certificates.

---

### 4. Architectural Synthesis: Decoupling Surface Elaboration from Core Checkers

Basis: derived + source + execution

Across all nine cliffs above, sound and predictable verification toolchains obey one structural boundary: **keep undecidable, heuristic, or fuel-bounded inference strictly in the untrusted surface elaborator, and emit explicit witnesses into a decidable core checker**:

- *Subtyping & DOT bounds* $\longrightarrow$ explicit **coercion functions / realizability witnesses** (removing `S-Trans` bad-bounds collapse and cycle heuristics from the core).
- *Higher-rank & impredicative polymorphism* $\longrightarrow$ **Church-style explicit $\Lambda$ and type applications** (bypassing Wells 1999).
- *GADTs & exhaustiveness* $\longrightarrow$ **explicit equality coercions** (`Core` casts / `Eq.rec`) and explicit absurdity proofs (`False.elim`) rather than trusting a fuel-4 coverage oracle.
- *Dependent equality, erasure & SMT refinements* $\longrightarrow$ explicit conversion/proof certificates checked by a small intensional kernel with strict `Prop`/`SProp` elimination guards (`normalizes_to_zero`, subsingleton/squash rules) and `0`-quantity erasure cleanly separating ghost proofs from runtime ABIs. This directly parallels the trait-solver proof-tree and Polonius fixed-point certificate architecture detailed for Rust in `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering`.

## Boundaries

- **not examined:**
  - `MLstruct` (Parreaux & Chau, OOPSLA 2022) Boolean-algebraic subtyping (`MLscript` source not inspected).
  - `microsoft/TypeScript` conditional/mapped-type instantiation depth heuristics.
  - `agda/agda` `--without-K`, `--cubical`, and `--cumulativity` internals (Cockx, Devriese & Piessens, ICFP 2014, DOI `10.1145/2628136.2628139` cited for non-K pattern matching, source not inspected).
  - Global typeclass coherence, orphan rules, 1ML unified modules, and recursive-module double vision (distinct modularity scope).
  - Rust `rustc` frontend LOC/Polonius internals and Lean 4 kernel RSS/WHNF benchmarks (covered in `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering` and `lean-kernel-memory-ceilings-whnf-scaling-and-validator-architectures`).
- **unknown:**
  - Weakest restriction on distributive polar lattices guaranteeing polynomial-time canonical normal forms without `lcm` NFA-to-DFA alignment blowup (`Simple-sub/TypeSimplifier.scala:89-101`).
  - Whether algebraic subtyping (`Simple-sub`/`MLstruct`) admits a complete, principal, ergonomic unification with both higher-rank impredicativity and GADT local equalities.
  - Ergonomic quantity polymorphism (`0`/`1`/`ω`) in QTT (`Idris 2`) without duplicating erased vs. runtime library ABIs.
  - Composing Flux-style ownership-gated liquid refinements cleanly across `unsafe`/`Mutex` interior mutability with kernel-checked SMT proof reconstruction.
- **known not to apply:**
  - *Claim that `λx. x x` requires recursive (`μ`) types in algebraic subtyping:* **Falsified by execution** (`witness_1_biunification_vs_hm`): `Simple-sub` types `λx. x x` non-recursively via polar intersection `((a0 & (a0 -> a1)) -> a1)`; `μ`-types arise only on same-polarity cycles (`stream`, `peel_a`).
  - *Claim that cycle-set memoization (`pendingSubTypes`) guarantees nominal variance subtyping termination:* **Falsified by execution** (`witness_4_contravariant_expansive_divergence`): `C<in X> extends N<N<C<C<X>>>>` strictly grows depth ($C^k(T) \to C^{k+1}(T)$) so no `(lhs, rhs)` pair repeats.
  - *Claim that Scala 3 `CheckRealizable` already enforces full non-null DOT realizability:* **Falsified by source** (`scala/scala3@90f3daf0a479`, `CheckRealizable.scala:78-81,196-204`: `"not null"` unchecked by default; `memberRealizability` gated on `3.future`).
  - *Claim that Lean 4 and Rocq share identical `Prop`/`SProp` elimination rules:* **Falsified by source**: Lean 4 combines definitional proof irrelevance with subsingleton `Prop` elimination (`inductive.cpp:510-565`), whereas Rocq keeps `Prop` proof-relevant and squashes 0-arg 1-ctor `SProp` inductives (`sEq`) unless `typing_flags.allow_uip` is enabled (`indTyping.ml:196-208`).
- **unsupported:**
  - Decidable Curry-style System F inference/checking and Rank $\ge 3$ inference (Wells 1999; Kfoury & Wells 1994).
  - Decidable subtyping for full $F_{<:}$, full Java generics with wildcards, and unrestricted $D_{<:}$ (Pierce 1994; Grigore 2017; Hu & Lhoták 2020).
  - Unannotated principal GADT inference without equality-qualified types (Vytiniotis et al. 2011).
  - Decidable Extensional Type Theory checking and general second-order unification (Hofmann 1995; Goldfarb 1981).
  - Unrestricted large elimination or non-`Prop` structure projection from proof-irrelevant `Prop` (inconsistent; blocked in `lean4/src/kernel/inductive.cpp:510-565`, `type_checker.cpp:267-285,371-377`).
  - Flux strong refinement checking behind raw pointers (`flux-rs/flux/crates/flux-refineck/src/type_env.rs:262`).

## Evidence

All primary-source evidence and probe outputs were collected and verified on **2026-11-19**.

### 1. Pinned Upstream Source Audit

| Repository & Commit SHA | Inspected Paths, Symbols & Lines |
| :--- | :--- |
| `LPTK/simple-sub` @ `ace6a33abb3563f56938c4987cd52145d5b99ba1` | `shared/src/main/scala/simplesub/Typer.scala` (`constrain` L88–129, `extrude` L134–159, `coalesceType` L239–258); `TypeSimplifier.scala` (`compactType` L49–84, `canonicalizeType` L86–158, `simplifyType` L185–282) |
| `scala/scala3` @ `90f3daf0a4795308d9c0e1b8f2265aeaecae8aa2` | `compiler/src/dotty/tools/dotc/core/TypeComparer.scala` (`monitoredIsSubType` L292–331, `DerefLimit = 10` L306, `recCount` L1672–1675); `config/Config.scala` (`LogPending*Threshold` L195–201); `core/CheckRealizable.scala` (L55–204); `typer/Checking.scala` (`checkGoodBounds`/`findBadBounds` L89–101) |
| `ghc/ghc` @ `83038fbee5efea8e3ebd5090b2ff5537462e169d` | `compiler/GHC/Tc/Gen/App.hs` (`Note [Quick Look overview]` L79–167, L306–355); `GHC/Tc/Utils/TcType.hs` (`TcLevel`/`QLInstVar` L738–899, `isTouchableMetaTyVar` L1220–1229); `GHC/Tc/Solver/Equality.hs` (L2072–2075); `GHC/Tc/Solver.hs` (L1199–1201, L1665–1667); `GHC/HsToCore/Pmc/Check.hs` (`checkGrdDag` L165–185); `GHC/HsToCore/Pmc/Solver.hs` (`initFuel = 4` L593–609, `tyOracle` L622–639, `addBotCt` L683–686, `Note [Fuel for the inhabitation test]` L1725–1780) |
| `idris-lang/Idris2` @ `cf66cb4ccb8f0df7876fd07842f056f6222b9dce` | `src/Algebra/ZeroOneOmega.idr` (L9–135); `src/Core/LinearCheck.idr` (`lcheck` L156–255, `lcheckBinder` L365–391); `src/Core/Unify.idr` (`postpone` L211–260, `getVars` L278–290, `patternEnv` L304–359) |
| `leanprover/lean4` @ `8009d0a64d2860606c6a5ac5ff6702622b24921e` | `src/kernel/inductive.cpp` (`elim_only_at_universe_zero` L510–565, `init_elim_level` L568–580); `src/kernel/type_checker.cpp` (`infer_proj` L267–285, `is_prop` L371–377, `is_def_eq_proof_irrel` L906–913); `src/kernel/level.cpp` |
| `rocq-prover/rocq` @ `25f5b18a320e4796f181f938d3b74bebe7db4dc4` | `kernel/sorts.ml` (`Quality` L166–290); `kernel/uGraph.ml` (`UniverseInconsistency`, `check_leq`, `enforce_constraint` L49–102); `kernel/indTyping.ml` (`compute_elim_squash` L100–135, `check_constructors` L186–218); `kernel/indtypes.ml` (L506–579) |
| `flux-rs/flux` @ `7d9886b36347e9e245fa8b354da7fb9662a2087c` | `crates/flux-refineck/src/type_env.rs` (`TypeEnv`/`PlacesTree` L46–49, `borrow` L132–149, `assign` L250–266, `move_place` L268–279); `crates/flux-refineck/src/checker.rs` (L548–572) |

### 2. Verified Literature & Execution Probe

- **Literature:** All 20 primary papers in `REPORT.json` verified for authors, venues, years, and DOIs (`10.1006/inco.1994.1055`, `10.1016/S0168-0072(98)00047-5`, `10.1145/3009837.3009882`, `10.1145/3409006`, `10.1145/3009837.3009871`, `10.1145/2983990.2984004`, `10.1007/978-3-319-30936-1_14`, `10.1145/2983990.2984008`, `10.1145/3371077`, `10.1017/S0956796811000098`, `10.1145/3408971`, `10.1145/3408989`, `10.1145/3450952`, `10.1016/0304-3975(81)90040-2`, `10.1093/logcom/1.4.497`, `10.1145/3209108.3209189`, `10.4230/LIPIcs.ECOOP.2021.9`, `10.1145/3290316`, `10.1145/1375581.1375602`, `10.1145/3591283`), plus supporting citations Kfoury & Wells (1994), Hurkens (1995, `10.1007/BFb0014058`), Kennedy & Pierce (2007), Greenman et al. (2014, `10.1145/2594291.2594308`), Cockx et al. (2014, `10.1145/2628136.2628139`), Sozeau & Tabareau (2014, `10.1007/978-3-319-08970-6_32`), Karachalias et al. (2015, `10.1145/2784731.2784748`), and Emrich et al. (2020, `10.1145/3385412.3386003`).
- **Execution (`support/verify_type_interaction_witnesses.py`):** Executed via `python3 -B reports/type-system-interactions-subtyping-polymorphism-and-decidability/support/verify_type_interaction_witnesses.py` (Python 3 stdlib only, exit `0`), outputting verified JSON receipts for all five witnesses:
  1. `witness_1_biunification_vs_hm`: HM rejects width mismatch, `λx. x x`, and recursive stream; `Simple-sub` infers `(a1 | int | bool)` on `.a`, non-recursive `((a0 & (a0 -> a1)) -> a1)` on `λx. x x`, `mu0` on `stream`/`peel_a`, and `lcm(2,3,5,7,11) = 2310` vs. 28 input nodes.
  2. `witness_2_gadt_non_principality_outsidein`: `∀a. T a -> Bool` and `∀a. T a -> a` both validate under `a ~ Bool`, are mutually incomparable, have unsound HM anti-unifier `∀a b. T a -> b`, trigger `blocked_untouchable(beta[lvl=1] at implic_lvl=2)` unannotated, and discharge under either explicit signature.
  3. `witness_3_dot_bad_bounds_vs_realizability`: Empty env rejects `Int <: String`; bad bounds derive `Int <: x.L <: String` and `Top <: x.L <: Bot` in 5 steps; `None` inhabitant triggers runtime `AttributeError`; `dot_check_realizable` returns `HasProblemBounds`.
  4. `witness_4_contravariant_expansive_divergence`: Expansive `C<in X> extends N<N<C<C<X>>>>` exhausts 24 steps (`unique_pairs_visited = 24`, max depth `9`), while non-expansive `C<in X> extends N<N<X>>` refutes in 5 steps (max depth `2`).
  5. `witness_5_qtt_semiring_and_miller_hou`: All 27 triples satisfy `{Rig0, Rig1, RigW}` semiring/preorder laws (`0 * 1 = 0`, `1 + 1 = ω </= 1`); Miller pattern `?M(x, y) =?= f(y, x)` has 1 unique MGU while non-pattern `?M(x, x) =?= f(x, x)` has 4 incomparable solutions.

## Revalidation

The mathematical impossibility theorems (Pierce 1994, Wells 1999, Goldfarb 1981, Hurkens 1995, Vytiniotis et al. 2011, Grigore 2017, Hu & Lhoták 2020, Gilbert et al. 2019) are permanent properties of their formal calculi. Revalidation targets the executable witnesses and pinned compiler guardrails:

1. **Re-run the Standalone Probe (~100 ms):**
   ```console
   python3 -B reports/type-system-interactions-subtyping-polymorphism-and-decidability/support/verify_type_interaction_witnesses.py
   ```
   Exit code `0` re-confirms all five encoded mathematical witnesses (not upstream compiler changes).
2. **Narrow Upstream Diffs for Implementation Guardrails:**
   - **GHC (`ghc/ghc`):** Diff `compiler/GHC/Tc/Gen/App.hs` (`QLInstVar` / `Note [Quick Look overview]`), `GHC/Tc/Utils/TcType.hs` (`isTouchableMetaTyVar`), and `GHC/HsToCore/Pmc/Solver.hs` (`initFuel`, `Note [Fuel for the inhabitation test]`).
   - **Scala 3 (`scala/scala3`):** Diff `compiler/src/dotty/tools/dotc/core/CheckRealizable.scala` (L78–81, L196–204) and `config/Config.scala` (`LogPendingSubTypesThreshold`) to check if default null-safety closes the realizability gap.
   - **Idris 2 (`idris-lang/Idris2`):** Diff `src/Algebra/ZeroOneOmega.idr`, `src/Core/LinearCheck.idr`, and `src/Core/Unify.idr` (`patternEnv`) for quantity polymorphism or non-Miller unification changes.
   - **Lean 4 (`leanprover/lean4`) & Rocq (`rocq-prover/rocq`):** Diff `src/kernel/inductive.cpp` (`elim_only_at_universe_zero`), `src/kernel/type_checker.cpp` (`is_prop`/`infer_proj`), `kernel/indTyping.ml` (`check_constructors`/`allow_uip`), and `kernel/uGraph.ml`.
   - **Flux (`flux-rs/flux`):** Diff `crates/flux-refineck/src/type_env.rs` (`borrow`/`assign`, `is_strg`, `behind_raw_ptr`) for interior-mutability, aliasing, or proof-certificate support.
