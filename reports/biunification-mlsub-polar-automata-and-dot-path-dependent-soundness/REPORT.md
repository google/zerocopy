# Biunification, Polar Regular-Tree Automata, and Path-Dependent Soundness in MLsub, MLscript, gDOT, and Scala 3

## Summary

Combining ML-style principal type inference with subtyping requires replacing unconstrained constraint bags with **polar algebraic subtyping**, whereas combining object-oriented path-dependent type projections (`p.T`) with unrestricted subtyping transitivity destroys soundness whenever unrealized or uninitialized type bounds collapse the subtyping lattice. Across the two lineages analyzed here:

1. **Distributive-lattice and Boolean-algebraic type inference (`MLsub`, `Simple-sub`, `MLscript`):** `MLsub` (Dolan & Mycroft, POPL 2017) and `Simple-sub` (`LPTK/simple-sub`) preserve decidable, principal Hindley–Milner polymorphism alongside structural subtyping and equirecursive types by separating types into **positive output joins** ($\sqcup$, `Bot` identity) and **negative input meets** ($\sqcap$, `Top` identity), solved via directional **biunification** (`lhs <: rhs`) and polar level extrusion (`extrude`). Presentation and subsumption require converting cyclic constraint graphs (`CompactType` / NFA states) into simplified polar regular-tree automata via powerset determinization (`canonicalizeType` / `determinise`), which incurs worst-case $\mathrm{lcm}(\ell_1, \dots, \ell_k) \le 2^n$ state expansion across co-occurring recursive cycles. Extending distributive lattices to full **Boolean algebras with negation** (`¬τ`) in `hkust-taco/mlscript` (`invalml/NormalForm.scala`, `ConstraintSolver.scala`) enables first-class union/intersection/negation refinements by normalizing $\tau_1 \sqcap \neg\tau_2 \le \bot$ into Disjunctive Normal Form (`Disj` of `Conj`), trading linear-polarity cleanliness for worst-case $2^d$ DNF clause multiplication under nested intersections and negations.
2. **Path-dependent type projections, bad-bounds transitivity, and initialization safety (`DOT`, `gDOT`, `Scala 3`):** In Dependent Object Types (`DOT`), unrestricted transitivity (`Sub-Trans`) across an unrealized path binding $x : \{ T >: \mathrm{Int} <: (\mathrm{Bool} \to \mathrm{Int}) \}$ proves $\mathrm{Int} <: x.T <: (\mathrm{Bool} \to \mathrm{Int})$ in two steps, collapsing soundness. Guarded `gDOT` (`Blaisorblade/dot-iris`, ICFP 2020) restores full transitivity (`iStp_Trans`) by wrapping abstract type bounds in step-indexed Iris later modalities (`TTMemL` $= \triangleright L .. \triangleright U$), preventing step-$0$ value coercion until concrete stamped object construction (`iD_Typ_Abs`, Löb induction) inhabits the path. Production `scala/scala3` (`TypeComparer.scala`) instead disables unguarded transitivity via **dual-bound checks** whenever `!trustBounds`: `tp1 <:< p.T` requires checking both `tp1 <: lo` and `tp1 <: hi`, and `p.T <:< tp2` requires both `hi <: tp2` and `lo <: tp2`, paired with `-Wsafe-init` (`Semantic.scala`, `Objects.scala`, `checkTermUsage`) to block `this` escape or uninitialized path reads (`Warm`/`Cold` vs. `Hot`) from undermining concrete bounds at runtime.

## Applicability

This report synthesizes and compares two primary families of subtyping type systems examined at exact pinned upstream revisions and peer-reviewed specifications:

- **Algebraic & Boolean Type Inference Family:** `stedolan/mlsub` (`b425c8da91f45ea59780756950871b80a18ddfc2`, POPL 2017 `DOI: 10.1145/3009837.3009882`), `LPTK/simple-sub` (`ace6a33abb3563f56938c4987cd52145d5b99ba1`, ICFP 2020 `DOI: 10.1145/3409006`), and `hkust-taco/mlscript` (`a44346127da2c608bfe4503d630e99c4ba9aa31c`, OOPSLA 2022 `DOI: 10.1145/3563304`). In `MLscript`, structural Boolean normal forms are observed specifically in `hkmc2/shared/src/main/scala/hkmc2/invalml/{NormalForm,ConstraintSolver,TypeSimplifier}.scala` alongside the main `hkmc2` elaborator.
- **Path-Dependent & Initialization-Safe Family:** `DOT` OOPSLA 2016 specification (`DOI: 10.1145/3022671.2984008`), `Blaisorblade/dot-iris` (`203d45ea4be590e9dfca84ed83374494af0a3db4`, ICFP 2020 `DOI: 10.1145/3408996`), and `scala/scala3` (`90f3daf0a4795308d9c0e1b8f2265aeaecae8aa2`, OOPSLA 2020 `DOI: 10.1145/3428243` and Scala 2021 `DOI: 10.1145/3486610.3486895`).
- **Relationship among subjects:** `Simple-sub` distills `MLsub` from bipartite finite-automaton state graphs (`types.ml`) into direct mutable-bound syntax variables (`Typer.scala`) plus explicit determinization/co-occurrence passes (`TypeSimplifier.scala`); `MLscript` generalizes `Simple-sub`'s distributive lattice to full Boolean normal forms (`Disj`/`Conj`); `gDOT` mechanizes a sound core of `Scala 3`'s dependent object calculus in Coq/Iris; and `Scala 3` implements production `TypeComparer` approximations alongside the `transform/init` abstract interpreter guarding path initialization. All empirical timings and state-count figures labeled `Basis: execution` were measured on Python 3.13.15 running the self-contained probe preserved in **Evidence**.

## Findings

### 1. Distributive-Lattice Algebraic Subtyping and Directional Biunification (`MLsub` & `Simple-sub`)

`Basis: normative + source`

Classical Hindley–Milner inference combined naively with subtyping generates arbitrary multi-variable inequality systems whose principal types require large, non-canonical constraint qualifiers. Both `MLsub` and `Simple-sub` eliminate qualified constraint sets by restricting the type grammar to a **bounded distributive lattice** partitioned by syntactic **polarity**:

- **Polar Lattice Restriction (`MLsub` `types.ml:16-97, 139-141`):** Type constructors live in `TypeLat.t` (`LZero | LUnexpanded | LExpanded`), where `LZero` interprets as bottom $\bot$ in `Pos` (output/covariant) positions and top $\top$ in `Neg` (input/contravariant) positions, and `LExpanded` merges distinct heads as unions ($\sqcup$) in `Pos` vs. intersections ($\sqcap$) in `Neg` (`TypeLat.join_comps`, `TypeLat.to_typeterm`). `State.check_polarity` (`types.ml:139-141`) asserts two structural invariants on every automaton node `s`: every dataflow edge `s -> s'` crosses opposite polarities (`s'.pol <> s.pol`), and every child component `p` preserves the structural polarity rule (`p = s.pol`, flipped at contravariant arrow domains via `polneg` / `!polarity`).
- **Directional Biunification (`Simple-sub` `Typer.scala:88-129` vs. `MLsub` `types.ml:405-429`):** Instead of solving symmetric equations $A = B$, `Typer.constrain(lhs, rhs)` decomposes only directed subtype goals `lhs <: rhs`:
  1. Structural decomposition flips polarity on function domains (`Function(l0, r0) <: Function(l1, r1)` emits `l1 <: l0` and `r0 <: r1`, `Typer.scala:106-108`) and verifies record width/depth subtyping (`Record(fs0) <: Record(fs1)` checks every field in `fs1` exists in `fs0`, `Typer.scala:109-114`).
  2. Variable bounds propagate transitively on the fly: adding `lhs <: rhs` when `rhs.level <= lhs.level` pushes `rhs` onto `lhs.upperBounds` and immediately constrains every existing `lb <- lhs.lowerBounds` against `rhs` (`Typer.scala:115-120`).
  3. **Cycle Termination (`Typer.scala:95-104`, `mlsub/types.ml:408-412`):** Because inferred types are regular (rational) trees, cyclic recursive constraints are guaranteed to revisit the same `(Variable, SimpleType)` or `(st_pos.id, st_neg.id)` pair; caching only pairs containing at least one type variable guarantees termination without slowing non-variable structural checks (`cache: MutSet[(SimpleType, SimpleType)]`).
- **Let-Polymorphism via Polar Level Extrusion (`Typer.scala:134-159`):** Traditional level-based HM raises or mutates an inner `Variable` level when unified with an outer variable, which is unsound under subtyping because lower and upper bounds have opposite variance. `Simple-sub`'s `extrude(ty, pol)(lvl, cache)` leaves variables at `ty.level <= lvl` shared in place, and clones any escaping higher-level variable (`tv.level > lvl`) into a fresh level-`lvl` variable keyed by **(variable, polarity)** `PolarVariable = (Variable, Boolean)` (`Typer.scala:131, 146-157`). If `pol == true` (positive extrusion into an outer lower bound), the original variable gains upper bound `nvs` (`tv <: nvs`) and `tv.lowerBounds` are extruded recursively into `nvs.lowerBounds`; if `pol == false`, `nvs <: tv` and `tv.upperBounds` extrude downward. This preserves principal polymorphic let-generalization (`PolymorphicType(level, body)`, `Typer.scala:201-203`) without copying entire constraint graphs eagerly.

### 2. Polar Regular-Tree Automata Determinization, Co-Occurrence Simplification, and Boolean Negation (`MLsub`, `Simple-sub`, `MLscript`)

`Basis: source + execution`

Raw biunification graphs accumulate redundant flow edges, spurious `α <: β <: α` variable cycles, and mis-aligned recursive cycle lengths that make inferred types unreadable and block canonical subsumption checks. Both `MLsub` and `Simple-sub` interpret constraint graphs as **nondeterministic polar regular-tree automata** and simplify them in three stages:

1. **Compaction and Spurious-Cycle Stripping (`Simple-sub` `TypeSimplifier.scala:15-84`):** `CompactType(vars, prims, rec, fun)` merges co-occurring bounds at each polarity (`CompactType.merge(pol)` at lines 29–36 intersects record field maps positively and unions them negatively). During traversal, `compactType` tracks `parents: Set[Variable]` (`lines 55-70`) to discard direct variable-only cycles (`?a <: ?b <: ?a`), emitting recursive `μ`-bindings only when a variable re-enters after passing through a type constructor (`Function` or `Record`).
2. **Powerset Determinization (`MLsub` `types.ml:496-528`; `Simple-sub` `TypeSimplifier.scala:102-158`):** `MLsub`'s `determinise` constructs DFA states indexed by `StateSet.t` sets of NFA states (`states_follow`), followed by Hopcroft-style partition refinement (`minimise`, `types.ml:531-631`) and greedy bipartite biclique decomposition (`decompile_automaton`, `types.ml:321-402`) to re-synthesize human-readable type variables and check semantic subsumption (`subsumed`, `types.ml:666-713`). `Simple-sub`'s `canonicalizeType` performs the same two-phase powerset construction over `(CompactType, Boolean)` pairs (`go0` closes variable-to-variable bounds via `closeOver`, `go1` merges constructor bounds across the active variable set before recursing). As documented at `TypeSimplifier.scala:88-100` and verified by Probe Part 1A, merging co-occurring recursive cycles of lengths $\ell_1, \dots, \ell_k$ unrolls the resulting DFA to cycle period $\mathrm{lcm}(\ell_1, \dots, \ell_k)$, producing exponential $2^{\Omega(n)}$ state blowup in pathological NFA inputs.
3. **Polar Co-Occurrence Unification (`Simple-sub` `TypeSimplifier.scala:185-282`):** `simplifyType` tracks `coOccurrences: MutMap[(Boolean, Variable), MutSet[SimpleType]]`—the intersection of variables and primitives co-occurring in every occurrence of `(pol, v)`:
   - Non-recursive variables occurring at only one polarity (`(Some(_), None) | (None, Some(_))`, lines 233–236) collapse to `Bot` (`pos`) or `Top` (`neg`) and drop out.
   - Two variables `v, w` with matching recursiveness (`recVars.contains(v) === recVars.contains(w)`, line 246—preventing unsound merging of strictly polar recursive variables with non-recursive ones) are unified (`w := v`) whenever every occurrence of `w` at polarity `pol` is accompanied by `v` and vice versa (`coOccurrences.get(pol -> w).forall(_(v))`, line 250).
   - Any variable `v` co-occurring at `!pol` with a primitive `atom` already paired with `v` at `pol` collapses to that primitive (`lines 273-274`).
4. **Full Boolean Normal Forms with Negation (`MLscript` `hkmc2/invalml/NormalForm.scala:12-191`, `ConstraintSolver.scala:35-148`):** While `MLsub` and `Simple-sub` forbid negation and positive intersection, `MLscript`/`MLstruct` supports arbitrary `A & B`, `A | B`, and `~A` (`NegType`) needed for OO class hierarchies and pattern-matching exhaustiveness. `ConstraintSolver.constrainImpl` (`ConstraintSolver.scala:139-145`) tests `lhs <: rhs` by inlining Skolem bounds and normalizing `lhs & rhs.!` (`lhs ⊓ ¬rhs`) into a `Disj(conjs: Ls[Conj])` (`NormalForm.dnf`, lines 176–190), where every `Conj(i: Inter, u: Union, vars: Ls[(InfVar, Bool)])` represents a conjunction of one positive class/function intersection `Inter`, negated disallowed constructors `Union` (`¬{...}`), and signed inference variables `(tv, pol)`. During `Conj.merge` (`NormalForm.scala:30-49`), contradicting variable polarities (`p1 =/= p2` for the same `uid`, line 43) or disjoint classes (`cls1.uid =/= cls2.uid`, line 95) prune the branch to `None` ($\bot$), while solving `Conj(i, u, (v, pol) :: tail)` moves the remaining literals onto `v`'s upper/lower bound by negating or preserving `rest` (`ConstraintSolver.scala:82-99`). Because `NormalForm.neg` converts unions into intersections (`inter(neg(lhs), neg(rhs))`, line 173), nested unions/intersections across contravariant arrow types trigger exponential $2^d$ DNF clause growth (Probe Part 1B).

### 3. Path-Dependent Types (`DOT`), the Bad-Bounds Paradox, Guarded `gDOT`, and `Scala 3` `TypeComparer`

`Basis: normative + source + execution`

Dependent Object Types (`DOT`, Rompf & Amin OOPSLA 2016) model objects containing both value/method members (`TVMem l T`), dependent functions (`TAll T1 T2`), intersection/union lattice connectives (`TAnd`, `TOr`), recursive self-types (`TMu T`, $\mu(x: T)$), and **type members with lower and upper bounds** (`TTMem l L U`, `{ type A >: L <: U }`) projected via stable paths (`TSel p l`, `p.A`).

- **The Bad-Bounds Transitivity Paradox:** The two natural projection rules for `p : { A >: L <: U }` are:
  $$\frac{\Gamma \vdash p : \{ A >: L <: U \}}{\Gamma \vdash L <: p.A}\text{ (<:-Sel)} \qquad \frac{\Gamma \vdash p : \{ A >: L <: U \}}{\Gamma \vdash p.A <: U}\text{ (Sel-<:)}$$
  In an environment containing an unrealized assumption $x : \{ A >: \mathrm{Int} <: (\mathrm{Bool} \to \mathrm{Int}) \}$ (for example, inside an uncalled function body $\lambda(x: \{A : \mathrm{Int}..\mathrm{Bool} \to \mathrm{Int}\}).\; e$, or via a `null` / uninitialized path), unrestricted subtyping transitivity (`Sub-Trans`) derives $\mathrm{Int} <: x.A <: (\mathrm{Bool} \to \mathrm{Int})$, coercing an integer `42` into a function and violating progress/preservation upon application (`42 true`).

The examined systems prevent this collapse via three distinct mechanisms:

| Mechanism | Subject (`Revision` / `DOI`) | Core Invariant Keeping Soundness | Preserves General `Sub-Trans`? | Runtime Witness Requirement |
| :--- | :--- | :--- | :--- | :--- |
| **Pushback / Inertness Proof** | `DOT` (`10.1145/3022671.2984008`) | Eliminates `Sub-Trans` from derivation normal forms; concrete store values cannot inhabit contradictory bounds. | In typing only via inversion lemmas; eliminated from canonical subtyping normal forms. | Soundness holds only for runtime stores of **inert** concrete objects (`dtysyn` / tight bounds $S..S$). |
| **Step-Indexed Later Guard (`▷`)** | `gDOT` (`Blaisorblade/dot-iris` @ `203d45ea`) | Encodes `{ A >: L <: U }` as `TTMemL "A" L U = TTMem "A" (TLater L) (TLater U)` (`correspondence.md:196-205`) under indexed subtyping `Γ t⊢ₜ T1 <:[i] T2` (`subtyping.v:64-189`). | **Yes** (`iStp_Trans` at every step index `i`, `subtyping.v:67-70`). | Coercion `Int <:[0] Bool -> Int` is blocked (`i=0`); `iIdx_Later_Stp` shifts step index `0 -> 1`, requiring concrete object creation (`iD_Typ_Abs`, `typing.v:86-90`) + runtime `tskip` (`typing.v:52-55`) to strip `▷`. |
| **Untrusted Dual-Bound Check** | `Scala 3` (`scala/scala3` @ `90f3daf0`) | Disables single-sided bound projection whenever `!trustBounds` (`TypeComparer.scala:634, 1019`): checking `tp1 <:< p.A` checks both `lo` and `hi`; checking `p.A <:< tp2` checks both `hi` and `lo`. | **No**—`TypeComparer` sacrifices blind transitivity through abstract bounds when `!trustBounds` unless concrete/GADT/singleton evidence exists. | Also requires `-Yexplicit-nulls` (`TypeComparer.scala:1023-1036`, `isNullable`) and `-Wsafe-init` (`Semantic.scala:1676-1685`) so `null` or uninitialized paths cannot spoof valid bounds. |

Inspecting the primary sources confirms exact implementation differences:

1. **Guarded `gDOT` (`Blaisorblade/dot-iris`):** In `theories/Dot/typing/subtyping.v:71-145`, `iStp_Add_Later` allows `T <:[i] ▷T` at index `0`, while `iSel_Stp` (`TSel p l <:[i] U` given `p : TTMem l L U, i`) and `iStp_Sel` (`L <:[i] TSel p l`) wrap bounds via `TTMemL "A" L U := TTMem "A" (TLater L) (TLater U)` (`correspondence.md:200-202`). Consequently, a bad-bounds assumption `x : { A >: ▷Int <: ▷(Bool -> Int) }` yields `Int <:[0] ▷Int <:[0] x.A <:[0] ▷(Bool -> Int)`, which by `iIdx_Later_Stp` (`subtyping.v:74-76`) is `Int <:[1] Bool -> Int`—never `Int <:[0] Bool -> Int`! Meanwhile, concrete object construction `iD_Typ_Abs` (`typing.v:86-90`) proves `L <:[0] ▷T` and `▷T <:[0] U` for an actual closed witness `T`, guarded by Iris's Löb induction (`sT_Obj_I`) in `theories/Dot/fundamental.v:141-148` (`Theorem type_soundness`) and using only two Coq axioms (`functional_extensionality` and `proof_irrelevance`, verified in `tests/test_used_axioms.v`). Notice also `subtyping.v:148-174` establishes that `gDOT` proves intersection distributivity $F[A] \land F[B] <: F[A \land B]$ for concrete constructors (`iAnd_All_1_Stp_Distr`, `iAnd_Fld_Stp_Distr`, `iAnd_Typ_Stp_Distr`), whereas union distributivity holds only for fields (`iOr_Fld_Stp_Distr`), not arbitrary type constructors as Scala 3 assumes for covariant higher-kinded type projections.
2. **Production `Scala 3` (`scala/scala3` @ `90f3daf0`):** In `TypeComparer.scala:634` (`thirdTryNamed`, comparing `tp1 <: tp2` where `tp2` has `info2: TypeBounds`), `TypeComparer` executes:
   `isSubApproxHi(tp1, info2.lo) && (trustBounds || isSubApproxHi(tp1, info2.hi))`
   Symmetrically, in `fourthTry` (`TypeComparer.scala:1019`, comparing `tp1 <: tp2` where `tp1` has `info1 @ TypeBounds(lo1, hi1)`), it checks:
   `isSubType(hi1, tp2, approx.addLow) && (trustBounds || isSubType(lo1, tp2, approx.addLow))`
   Thus, against an abstract path with contradictory bounds `type A >: Int <: (Bool => Int)`, neither `Int <:< x.A` nor `x.A <:< (Bool => Int)` succeeds when `trustBounds == false`—the compiler refuses to project across inconsistent bounds without failing overall soundness, while still allowing `Int <:< y.A` and `y.A <:< Any` when `type A >: Int <: Any` has consistent bounds (`Int <: Any`). Furthermore, lines `1023-1043` (`isNullable`) demonstrate how `Scala 3` must distinguish `!ctx.explicitNulls` for `TermRef`/`ThisType`: without `-Yexplicit-nulls`, `null` inhabits every non-value class type including `{ type A >: Int <: String }`, enabling runtime null dereferences or cast failures along `p.A` unless `-Yexplicit-nulls` removes `Null` from reference types.

### 4. Initialization Escape and Abstract Domain Soundness (`Scala 3` `transform/init`)

`Basis: normative + source`

Even when every concrete class specifies consistent type members (`type T = Int`), DOT soundness still fails if a path `p` referencing an object under construction is observed before `p`'s enclosing object fields or `outer` pointers are initialized, or if `this` escapes through a super-constructor virtual call (`AbstractFile.scala`, `Trees.scala` in `safe-initialization.md:18-63`). Crucially, `Semantic.scala:1672-1685` explicitly ties initialization checking back to DOT soundness: `checkTermUsage` traverses every `TermRef(_: SingletonType, _)` inside type expressions (`tpt.tpe`) to verify that paths appearing inside path-dependent types are initialized at the point of use.

`scala/scala3` implements two complementary static abstract interpreters under `-Wsafe-init` (`Checker.scala:31-62`):

- **Per-Class Initialization Lattice (`Semantic.scala:35-160`, Liu et al. OOPSLA 2020 / Scala 2021):** The abstract domain orders object initialization states as a finite-height lattice:
  - `Hot` (bottom element $\sqsubseteq$ all others): transitively initialized; field reads and method calls produce `Hot`.
  - `ThisRef(klass)` (`Semantic.scala:96-97`): the current object under construction (`outer = Hot`), whose fields mutate flow-sensitively inside `Objekt` (`Heap`) as `ValDef` initializers execute (`Semantic.scala:1640-1666`), attempting promotion via `tryPromoteCurrentObject()`.
  - `Warm(klass, outer, ctor, args)` (`Semantic.scala:103-140`): an object whose own fields are initialized (populated lazily via `populateParams()`), but whose `outer` or constructor arguments reach `Cold` or `ThisRef` values. To guarantee fixed-point termination over arbitrary inner-class nesting, `new p.C(args)` widens nested `Warm` `outer` pointers to `Cold` (`safe-initialization.md:291-299`).
  - `Fun(expr, thisV, klass)` and `RefSet(refs)` (`Semantic.scala:143-149`): abstract closure and branch-join values.
  - `Cold` (top element): uninitialized / unknown initialization state; any field access `e.f`, method call `e.m()`, pattern-match scrutinee, assignment RHS (`o.x = e`), return, or exception throw on non-effectively-hot values is rejected (`safe-initialization.md:246-301`), while passing `Warm`/`ThisRef` to constructor arguments is permitted to allow cyclic immutable graphs provided the callee never reads fields on the escaped reference.
- **Static Global Object Irrelevance (`Objects.scala:35-103`):** Because global `object` singletons form cross-module initialization dependencies, `Objects` enforces **initialization-time irrelevance** ("the initialization of a static object should not directly or indirectly read or write mutable state of another static object", `Objects.scala:49-55`), bounded by a per-object method-call budget `checkCost`: **`500`** calls in default `BestEffort = true` mode (`Objects.scala:85-102`) and **`2000`** calls in aggressive mode (throwing `OutOfQuotaException`). Cross-project superclass/supertrait analysis relies on serialized TASTy trees (`safe-initialization.md:306-308`), while Java/Scala 2 superclasses and `@unchecked` annotations remain unverified escape hatches (`lines 329-336`).

### 5. Cross-System Technical Matrix & Reproducible Execution Probe

`Basis: execution + source + derived`

| Property / System | `MLsub` (`b425c8da`) | `Simple-sub` (`ace6a33a`) | `MLscript` / `MLstruct` (`a4434612`) | `gDOT` (`203d45ea`) | `Scala 3` (`90f3daf0`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Algebraic Structure** | Polar distributive lattice ($\sqcup^+, \sqcap^-, \bot, \top$) | Polar distributive lattice ($\sqcup^+, \sqcap^-, \bot, \top$) | Full Boolean algebra ($\sqcup, \sqcap, \neg, \bot, \top$) | Intersection/union lattice + $\mu$ + `▷` + `{A: L..U}` | Path-dependent lattice + unions/intersections + GADT + match types |
| **Inference Engine** | Bipartite NFA flow closure (`constrain`, `types.ml`) | Directed biunification + polar extrusion (`Typer.scala`) | Constraint DNF normalization (`lhs ⊓ ¬rhs ⊑ ⊥`) | None (explicitly typed kernel calculus) | Bidirectional local type inference + constraint bounds + `TypeComparer` |
| **Principal Types** | Yes (for core MLsub) | Yes (modulo syntactic vs. semantic equivalence) | Yes for `MLstruct` core without dependent types | No (higher-rank / path-dependent) | No (requires annotations on polymorphic / recursive defs) |
| **Equirecursive Types** | Built-in (`TRec` / cyclic NFA states) | Built-in (cyclic variable bounds + `coalesceType`) | Supported in core structural layer | Explicit iso-recursive $\mu(x: T)$ (`TMu`) + `iP_Mu_{I,E}` | Class recursion + F-bounds + match types (bounded recursion depth) |
| **Transitivity Guard** | Sound by polarity invariant (`State.check_polarity`) | Sound by level extrusion (`extrude`) | Sound by DNF contradiction pruning | Unrestricted `iStp_Trans` guarded by `▷` (`TTMemL`) | `!trustBounds` dual-bound checks + `-Yexplicit-nulls` + `-Wsafe-init` |
| **Path-Init Check** | N/A (immutable ML terms) | N/A (immutable ML terms) | N/A (effect/inval checked separately) | Value-only path roots + termination (`path_normalization`) | Flow-sensitive `Cold/Warm/ThisRef/Hot` + `Objects` (`500`/`2000` quota) |

Executing the standalone Python 3.13.15 probe (`## Evidence`) yielded the following exact measurements:

1. **Cycle Alignment & NFA-to-DFA Blowup (`Simple-sub` `canonicalizeType` simulation):** Merging two positive recursive arrow cycles of coprime periods $(\ell_1, \ell_2)$ forced DFA state unrolling proportional to $2 \cdot \mathrm{lcm}(\ell_1, \ell_2) + 2$:
   - `(2, 3)` (`lcm=6`, 9 constraints) $\to$ **14** DFA states (`0.178 ms`)
   - `(3, 4)` (`lcm=12`, 11 constraints) $\to$ **26** DFA states (`0.238 ms`)
   - `(3, 5)` (`lcm=15`, 12 constraints) $\to$ **32** DFA states (`0.233 ms`)
   - `(4, 5)` (`lcm=20`, 13 constraints) $\to$ **42** DFA states (`0.276 ms`)
   - `(5, 7)` (`lcm=35`, 16 constraints) $\to$ **72** DFA states (`0.742 ms`)
   Merging $k$ parallel tagged prime-period cycles `[2, 3, 5, 7, 11]` raised `canonicalizeType` DFA states exponentially in $k$ from **6** ($k=1$, `lcm=2`, 4 constraints, `0.074 ms`) to **7** ($k=2$, `lcm=6`, 9 constraints, `0.125 ms`), **31** ($k=3$, `lcm=30`, 16 constraints, `0.615 ms`), **211** ($k=4$, `lcm=210`, 25 constraints, `6.876 ms`), and **2311** ($k=5$, `lcm=2310`, 38 constraints, `238.438 ms`, requiring Python recursion-limit expansion past 1,000 frames).
2. **Boolean DNF Clause Multiplication (`MLscript` `NormalForm.neg` / `inter` simulation):** Intersecting $d$ negated two-conjunct expressions $\bigsqcap_{i=1}^d \neg(a_i \sqcap b_i)$ expanded strictly as $2^d$ DNF clauses: `4` clauses at $d=2$ (`0.033 ms`), `16` at $d=4$ (`0.042 ms`), `64` at $d=6$ (`0.156 ms`), `256` at $d=8$ (`0.678 ms`), `1024` at $d=10$ (`4.394 ms`), and `4096` clauses at $d=12$ (`23.452 ms`).
3. **DOT Bad-Bounds Paradox Discrimination (`probe` Part 2):** Given `x : { T >: Int <: (Bool -> Int) }`:
   - `naive_dot(Int <: Bool->Int via x.T)` $\to$ **`True`** (unsound collapse);
   - `scala3_untrusted(Int <: x.T, bad)` $\to$ **`False`**, `scala3_untrusted(Int <: Bool->Int, bad)` $\to$ **`False`**, while valid bounds `y : { T >: Int <: Top }` retain `Int <: y.T == True` and `y.T <: Top == True`;
   - `gdot idx=0 (Int <:[0] Bool->Int via TTMemL)` $\to$ **`False`** (step-0 soundness holds), while `Int <:[0] ▷(Bool->Int)` (`True`), `▷Int <:[0] ▷(Bool->Int)` (`True`), and `Int <:[1] Bool->Int` (`True`) demonstrate exact step-delay isolation until an object witness strips `▷`.

### 6. Six-Level Performance & Resource Footprint Analysis (L1–L6)

`Basis: source + execution + derived`

| Level | `MLsub` / `Simple-sub` | `MLscript` (`MLstruct`) | `gDOT` (`dot-iris`) | `Scala 3` (`TypeComparer` + `init`) |
| :--- | :--- | :--- | :--- | :--- |
| **(L1) Human & Agent Authoring Velocity** | Minimal implementation footprint: `LPTK/simple-sub` core `Typer.scala` (`261` lines) + `TypeSimplifier.scala` (`322` lines); `stedolan/mlsub` `types.ml` (`748` lines) + `typecheck.ml` (`796` lines). Zero type annotations needed on polymorphic programs. | Moderate specification burden for union/intersection/negation signatures and class declarations; avoids HM annotation boilerplate while supporting match refinement typing. | High mechanized proof ratio (`dot-iris` `codesize.md`): `15,080` Coq LoC total (`2,761` Iris preliminaries, `2,562` syntax, `3,299` logical relation, `848` syntactic typing + fundamental theorem, `5,610` examples for 3–50 line target Scala snippets—a ~100:1 proof-to-program ratio). | Low user annotation overhead for classes/traits, rising on higher-kinded/GADT/path-dependent variance; `-Wsafe-init` uses zero mandatory annotations (`@unchecked` rare escape). |
| **(L2) Framework & Toolchain Build Time** | OCaml `mlsub` compiles in sub-second `ocamlbuild`/Make runs; `Simple-sub` `sbt` Scala.js compilation (`build.sbt`, Scala `2.13.18`) takes tens of seconds cold, `<2s` incremental. | Scala `sbt` multi-project build (`hkmc2`); heavier than `Simple-sub` due to elaborator/UCS/codegen passes. | Coq + `stdpp` + `iris` full build of `dot-iris` (`dune` / `Makefile.coq`) takes minutes on clean builds due to Iris higher-order separation logic and `Autosubst` de Bruijn rewrites. | Full `scala/scala3` bootstrap builds (`sbt`) require multi-minute multi-stage compilation (bootstrapping compiler with itself). |
| **(L3) Compilation, Elaboration & Synthesis Latency** | Biunification closure is fast ($O(n^2)$ edges in typical HM programs), but `canonicalizeType` / `determinise` hits $\mathrm{lcm}(\ell_i)$ / $2^n$ cliffs on nested co-occurring cycles (verified: `0.074 ms` at $k=1 \to 238.438\text{ ms}$ at $k=5$ in Python). `minimise` uses $O(n^2)$ initial partitioning (`types.ml:547`). | `NormalForm.dnf` hits $2^d$ clause blowup on chained `¬(a_i ∧ b_i)` / `(A \| B) -> C` constraints (`0.033 ms` at $d=2 \to 23.452\text{ ms}$ at $d=12$ in probe), mitigated in `MLscript` via hash-consing (`CanonicalTypeTest.scala`) and trace-budget caches. | No automated solver; interactive Coq proof script replay (`eauto` restricted by `Remove Hints iStp_Trans`, `typing.v:123`, `subtyping.v:198` to avoid divergence). | `TypeComparer` memoizes and caps recursion depth (`recCount`/`appliedRecCount`, `TypeComparer.scala:51-53`) avoiding undecidable loops; `Semantic` finitizes `Warm` outers; `Objects` hard-caps calls at `500` (`BestEffort`) or `2000` (`Objects.scala:101`). |
| **(L4) Generated Code Execution Performance** | Compiles directly to untagged OCaml/JS (`camlgen.ml`, `Simple-sub` Scala.js); zero runtime subtyping checks or type-dictionary passing needed, though structural records without monomorphization rely on uniform boxed/tagged field lookup. | `hkmc2` emits JS/Wasm (`DeadConstructorElim`, `ErasedType`); runtime tag tests align directly with union/negation type cases (`ClassLikeType`). | Pure operational calculus (`head_step` / `prim_step`); `tskip` steps reduce syntactically in 1 reduction step solely for soundness proofs, with zero production runtime analogue. | JVM/Scala.js erasure removes type members completely; path projections compile to ordinary JVM field reads (`0` tag overhead), while `-Wsafe-init` emits **zero** runtime check instructions (purely compile-time). |
| **(L5) Proof / Certificate Verification Speed** | Uncertified OCaml/Scala implementations (no kernel checker); `MLsub`'s `subsumed` checks bipartite automaton inclusion on determinized `dstate`s (`types.ml:666-713`). | Uncertified Scala compiler implementation tested via diff-test suites (`hkmc2DiffTests`). | Highest assurance: Coq kernel checks compiled `.vo` proofs (`Theorem type_soundness` in `fundamental.v:141`) in seconds with minimal TCB (`functional_extensionality` + `proof_irrelevance`, `test_used_axioms.v`). | Uncertified compiler (`TypeComparer.scala` is 4,160 lines of subtle mutable state); `-Wsafe-init` is not kernel-verified against JVM bytecode verifier invariants beyond `scalac`. |
| **(L6) RAM, Disk & Binary Footprints** | `mlsub` uses compact `Intmap` bitsets for `StateSet` / `DStateSet` (`types.ml:124-125, 453-454`); `Simple-sub`'s precompiled JS artifact (`simple-algebraic-subtyping-opt.js`) is `378,433` bytes. | `CanonicalTypeTest.scala` enforces `<= 4096` bytes thread allocation over `10,000` interned leaf type comparisons (`CanonicalTypeTest.scala:49`). | `dot-iris` Coq `.vo` artifacts + Iris opam dependencies require hundreds of MB–low GB RAM/disk during `coqc` proof checking; `0` runtime binary footprint. | `scala3` compiler JVM heap commonly runs `1–4+ GB` on large builds (`Cache.Data` retains immutable `ExprValueCache` snapshots in `Semantic.scala:260-372`, plus TASTy classpath indexing). |

### 7. Human Comprehensibility (C1) & Conceptual Simplicity / Model Refinement (C2)

`Basis: source + derived`

- **(C1) Human Comprehensibility & Mental-Model Ergonomics:**
  - *Working-memory burden:* Biunification succeeds ergonomically when inferred types are aggressively simplified (`Simple-sub` `simplifyType` + `coalesceCompactType`), turning opaque multi-variable constraint graphs (`'a <: 'b, 'b <: 'c -> 'd`) into familiar polymorphic signatures. Without simplification—or when `canonicalizeType` unrolls coprime recursive loops into $\mathrm{lcm}(\ell_1, \dots, \ell_k)$ states—inferred signatures explode past human working memory (`>100` `μ`-bound clauses), making type errors illegible unless the solver preserves constraint provenance (`CCtx.parents`, `ConstraintSolver.scala:15-30`).
  - *Transitivity betrayal in DOT/Scala 3:* Programmers intuitively expect subtyping `<:` to be transitive and type aliases `{ type A >: L <: U }` to satisfy $L <: p.A <: U$. Scala 3's `!trustBounds` fix silently breaks local transitivity when bounds are contradictory (`Int <: x.A` fails even though `x.A` declares `>: Int`)—preventing unsoundness while producing non-obvious rejections where `T1 <: p.A` fails because `p.A`'s upper bound is incompatible with `T1`. Conversely, `Semantic.scala`'s `Warm`/`ThisRef`/`Cold` diagnostic traces (`safe-initialization.md:33-90`) align directly with human operational intuition by printing the exact initialization call stack (`val extension -> def name -> val localFile`).
- **(C2) Conceptual Simplicity, Orthogonality & Universal Model Refinement:**
  - *Polar Lattice vs. Boolean DNF:* `MLsub`/`Simple-sub` achieve Ousterhout "deep module" simplicity by unifying polymorphism, structural records, variants, and equirecursion under **one algebraic invariant**—polarity-segregated bounded distributive lattices—eliminating ad-hoc subtype-variable solvers. However, under Felleisen's macro-expressibility criterion, omitting intersection/union symmetry (`¬`) prevents expressing disjoint class-tag pattern complements locally without encoding Church-style eliminators. `MLscript` recovers symmetric Boolean expressiveness via one canonical normal form (`Disj`/`Conj`), at the cost of collapsing the neat polarity wall (`v` and `¬v` mix inside `Conj`).
  - *Unifying Witness-Guarded Path Soundness:* Across `DOT`, `gDOT`, and `Scala 3`, bad-bounds paradoxes, null inhabitation, and initialization escapes are three surface manifestations of **one missing universal invariant**: *an abstract type projection `p.A` is only sound as a witness-transport channel when the path expression `p` is backed by a constructive, fully initialized runtime value witnessing `L <: S <: U`*. `gDOT` internalizes that witness temporally via the `▷` modality (`TTMemL` + `tskip`), while `Scala 3` patches the static surface piecemeal across three disconnected mechanisms (`TypeComparer`'s `!trustBounds`, `-Yexplicit-nulls`, and `transform/init`'s `Warm`/`Hot` abstract interpreter). Unifying path-dependent types with explicit **initialized-value / linear witness capabilities** would make `null`, uninitialized `this`, and bad-bounds paths syntactically un-projectable without special-case compiler flags.

## Boundaries

- **Full `DOT` / `Scala 3` subtyping decidability (`known not to apply`):** Unlike `MLsub` and `Simple-sub`, full `DOT` and `Scala 3` subtyping with recursive bounds and contravariant path selections is undecidable in general; `TypeComparer.scala` guarantees termination only via conservative recursion counters (`recCount`), not completeness.
- **Higher-kinded `hkDOT` and capture checking (`not examined`):** Although `Blaisorblade/dot-iris` contains an experimental `theories/Dot/hkdot` extension (`1,635` Coq LoC) and `scala/scala3`'s `TypeComparer.scala:630-632` invokes capture-set subtyping (`CCState`, `subCaptures`), full higher-kinded DOT soundness and Scala 3 capture-checking soundness were not examined in detail.
- **Scala 3 without `-Yexplicit-nulls` or `-Wsafe-init` (`known not to apply`):** Soundness protections against `null`-inhabited bad bounds (`val p: HasBadBounds = null`) and early constructor `this`-escape do not hold under default Scala 3 flags when explicit nulls and initialization checks are disabled, nor across Java/Scala 2 inheritance boundaries (`safe-initialization.md:336`).
- **`MLscript` `hkmc2` full-language DNF termination (`unknown`):** While `NormalForm.scala` (`191` lines) and `ConstraintSolver.scala` (`148` lines) implement terminating DNF solving for non-cyclic structural constraints via `CCtx.cache`, full-language termination and principality across recursive user-defined classes with cyclic variance in `hkust-taco/mlscript` remain unverified (`unknown` from static inspection alone without executing the full Scala test suite).
- **`Simple-sub` JS bundle execution (`not examined`):** `LPTK/simple-sub` includes a precompiled `bin/simple-algebraic-subtyping-opt.js` (`378,433` bytes), which was inspected on disk for footprint size only and not executed under `node`.

## Evidence

- **Primary Source Repositories & Exact Citations:**
  - `stedolan/mlsub` @ `b425c8da91f45ea59780756950871b80a18ddfc2`: `types.ml` (`TypeLat` lines 16–97; `State` & `check_polarity` 111–142; `decompile_automaton` 321–402; `constrain` 405–429; `determinise` 496–528; `minimise` 531–631; `subsumed` 666–713), `typecheck.ml` (`to_dscheme` 19–24; `typecheck` 501–715; `infer_module` 758–785).
  - `LPTK/simple-sub` @ `ace6a33abb3563f56938c4987cd52145d5b99ba1`: `shared/src/main/scala/simplesub/Typer.scala` (`constrain` lines 88–129; `extrude` 134–159; `PolymorphicType` 201–203; `Variable` 223–233; `coalesceType` 239–258), `shared/src/main/scala/simplesub/TypeSimplifier.scala` (`CompactType` 15–37; `compactType` 49–84; `canonicalizeType` 102–158; `simplifyType` 185–282), `bin/simple-algebraic-subtyping-opt.js` (`378,433` bytes).
  - `hkust-taco/mlscript` @ `a44346127da2c608bfe4503d630e99c4ba9aa31c`: `hkmc2/shared/src/main/scala/hkmc2/invalml/NormalForm.scala` (`Disj`, `Conj`, `Inter`, `Union` lines 12–138; `NormalForm.inter`/`neg`/`dnf` 151–191), `ConstraintSolver.scala` (`extrude` 43–79; `constrainConj` 81–123; `constrainImpl` 139–147), `TypeSimplifier.scala` (`simplifyBounds` 46–160), `hkmc2/jvm/src/test/scala/hkmc2/CanonicalTypeTest.scala` (allocation assertions lines 40–60).
  - `Blaisorblade/dot-iris` @ `203d45ea4be590e9dfca84ed83374494af0a3db4`: `correspondence.md` (`TTMemL` encoding lines 196–205), `codesize.md` (lines 6–45), `theories/Dot/typing/subtyping.v` (`path_typed` / `subtype` lines 15–189; `iAnd_*_Distr` 163–176; `iStp_Add_Later` 79–80), `theories/Dot/typing/typing.v` (`iT_Skip` 52–55; `iD_Typ_Abs` 86–90), `theories/Dot/fundamental.v` (`Theorem type_soundness` lines 141–148; `Theorem path_normalization` 151–158), `tests/test_used_axioms.v` (lines 1–14).
  - `scala/scala3` @ `90f3daf0a4795308d9c0e1b8f2265aeaecae8aa2`: `compiler/src/dotty/tools/dotc/core/TypeComparer.scala` (`thirdTryNamed` lines 613–638; `fourthTry` 1008–1022; `isNullable` 1023–1043), `compiler/src/dotty/tools/dotc/transform/init/Checker.scala` (lines 23–91), `Semantic.scala` (`Value` lattice lines 35–160; `Cache.Data` 260–372; `init` 1542–1670; `checkTermUsage` 1676–1685), `Objects.scala` (`BestEffort` / `checkCost` lines 85–102), `docs/_docs/reference/other-new-features/safe-initialization.md` (lines 1–343).
- **Peer-Reviewed Specifications:** Dolan & Mycroft, POPL 2017 (`DOI: 10.1145/3009837.3009882`); Parreaux, ICFP 2020 (`DOI: 10.1145/3409006`); Parreaux & Chau, OOPSLA 2022 (`DOI: 10.1145/3563304`); Rompf & Amin, OOPSLA 2016 (`DOI: 10.1145/3022671.2984008`); Giarrusso et al., ICFP 2020 (`DOI: 10.1145/3408996`); Liu et al., OOPSLA 2020 (`DOI: 10.1145/3428243`) and Scala 2021 (`DOI: 10.1145/3486610.3486895`).
- **Self-Contained Reproducible Probe (Python 3.13.15, exited `0`):**

```bash
python3 - <<'EOF'
from __future__ import annotations
from dataclasses import dataclass
import math, sys, time

sys.setrecursionlimit(6000)

@dataclass
class SType: pass
@dataclass
class Prim(SType):
    name: str
    @property
    def level(self) -> int: return 0
@dataclass
class Fun(SType):
    lhs: SType; rhs: SType
    @property
    def level(self) -> int: return max(self.lhs.level, self.rhs.level)
@dataclass
class Rcd(SType):
    fields: tuple[tuple[str, SType], ...]
    @property
    def level(self) -> int: return max((t.level for _, t in self.fields), default=0)

class Var(SType):
    def __init__(self, uid: int, level: int):
        self.uid, self.level = uid, level
        self.lower: list[SType] = []; self.upper: list[SType] = []

class Biunifier:
    def __init__(self) -> None:
        self.uid = 0; self.constraints = 0
    def fresh(self, level: int) -> Var:
        v = Var(self.uid, level); self.uid += 1; return v
    def constrain(self, lhs: SType, rhs: SType, cache=None) -> None:
        if cache is None: cache = set()
        if lhs is rhs: return
        self.constraints += 1
        if isinstance(lhs, Var) or isinstance(rhs, Var):
            k = (id(lhs), id(rhs))
            if k in cache: return
            cache.add(k)
        if isinstance(lhs, Fun) and isinstance(rhs, Fun):
            self.constrain(rhs.lhs, lhs.lhs, cache); self.constrain(lhs.rhs, rhs.rhs, cache)
        elif isinstance(lhs, Rcd) and isinstance(rhs, Rcd):
            fm = dict(lhs.fields)
            for k, t1 in rhs.fields: self.constrain(fm[k], t1, cache)
        elif isinstance(lhs, Var) and rhs.level <= lhs.level:
            lhs.upper.append(rhs)
            for lb in list(lhs.lower): self.constrain(lb, rhs, cache)
        elif isinstance(rhs, Var) and lhs.level <= rhs.level:
            rhs.lower.append(lhs)
            for ub in list(rhs.upper): self.constrain(lhs, ub, cache)

@dataclass(frozen=True)
class Compact:
    vars: frozenset[int] = frozenset(); prims: frozenset[str] = frozenset()
    rec: tuple[tuple[str, Compact], ...] | None = None
    fun: tuple[Compact, Compact] | None = None
    @property
    def is_empty(self) -> bool:
        return not (self.vars or self.prims or self.rec is not None or self.fun is not None)

def merge_compact(pol: bool, a: Compact, b: Compact) -> Compact:
    vs, ps = a.vars | b.vars, a.prims | b.prims
    if a.rec is not None and b.rec is not None:
        da, db = dict(a.rec), dict(b.rec)
        keys = sorted((set(da) & set(db)) if pol else (set(da) | set(db)))
        rec = tuple((k, merge_compact(pol, da[k], db[k]) if (k in da and k in db) else da.get(k, db.get(k))) for k in keys)
    else:
        rec = a.rec if a.rec is not None else b.rec
    fun = (merge_compact(not pol, a.fun[0], b.fun[0]), merge_compact(pol, a.fun[1], b.fun[1])) if (a.fun and b.fun) else (a.fun or b.fun)
    return Compact(vs, ps, rec, fun)

def canonicalize_dfa_states(ty: SType, pol: bool = True) -> tuple[int, int]:
    var_reg: dict[int, Var] = {}
    def collect(t: SType, seen: set[int]) -> None:
        if id(t) in seen: return
        seen.add(id(t))
        if isinstance(t, Var):
            var_reg[t.uid] = t
            for b in t.lower + t.upper: collect(b, seen)
        elif isinstance(t, Fun): collect(t.lhs, seen); collect(t.rhs, seen)
        elif isinstance(t, Rcd):
            for _, ft in t.fields: collect(ft, seen)
    collect(ty, set())
    def close_vars(seed: Var, p: bool) -> frozenset[int]:
        seen, st = set(), [seed]
        while st:
            v = st.pop()
            if v.uid in seen: continue
            seen.add(v.uid)
            for b in (v.lower if p else v.upper):
                if isinstance(b, Var) and b.uid not in seen: st.append(b)
        return frozenset(seen)
    def go0(t: SType, p: bool) -> Compact:
        if isinstance(t, Prim): return Compact(prims=frozenset([t.name]))
        if isinstance(t, Fun): return Compact(fun=(go0(t.lhs, not p), go0(t.rhs, p)))
        if isinstance(t, Rcd): return Compact(rec=tuple(sorted((k, go0(v, p)) for k, v in t.fields)))
        return Compact(vars=close_vars(t, p))
    vis = knots = 0
    def go1(ct: Compact, p: bool, in_proc: frozenset) -> None:
        nonlocal vis, knots
        if ct.is_empty: return
        k = (ct, p)
        if k in in_proc: knots += 1; return
        vis += 1; acc = ct
        for vid in ct.vars:
            for b in (var_reg[vid].lower if p else var_reg[vid].upper):
                if not isinstance(b, Var): acc = merge_compact(p, acc, go0(b, p))
        nxt = in_proc | {k}
        if acc.rec:
            for _, ft in acc.rec: go1(ft, p, nxt)
        if acc.fun: go1(acc.fun[0], not p, nxt); go1(acc.fun[1], p, nxt)
    go1(go0(ty, pol), pol, frozenset())
    return vis, knots

for l1, l2 in [(2, 3), (3, 4), (3, 5), (4, 5), (5, 7)]:
    b = Biunifier()
    def mk_cyc(per, tag):
        vs = [b.fresh(0) for _ in range(per)]
        for i in range(per): b.constrain(Fun(Prim(f"P{tag}_{i}"), vs[(i + 1) % per]), vs[i])
        return vs[0]
    out = b.fresh(0); b.constrain(mk_cyc(l1, 1), out); b.constrain(mk_cyc(l2, 2), out)
    t0 = time.perf_counter(); vis, kn = canonicalize_dfa_states(out)
    print(f"CyclePair({l1},{l2}) lcm={math.lcm(l1,l2)}: constraints={b.constraints}, dfa_states={vis}, knots={kn}, time_ms={(time.perf_counter()-t0)*1e3:.3f}")

for k in [1, 2, 3, 4, 5]:
    b, primes = Biunifier(), [2, 3, 5, 7, 11][:k]
    out = b.fresh(0)
    for idx, p in enumerate(primes):
        vs = [b.fresh(0) for _ in range(p)]
        for j in range(p): b.constrain(Rcd(((f"k{idx}_{j}", Prim("Int")), ("next", vs[(j + 1) % p]))), vs[j])
        b.constrain(vs[0], out)
    t0 = time.perf_counter(); vis, kn = canonicalize_dfa_states(out)
    print(f"PrimeCycles(k={k}, primes={primes}, lcm={math.prod(primes)}): constraints={b.constraints}, dfa_states={vis}, knots={kn}, time_ms={(time.perf_counter()-t0)*1e3:.3f}")

def dnf_clauses(depth: int) -> int:
    clauses = [frozenset([("a0", True)])]
    for i in range(1, depth + 1):
        neg_t = [frozenset([(f"a{i}", False)]), frozenset([(f"b{i}", False)])]
        nxt = []
        for c1 in clauses:
            for c2 in neg_t:
                m = dict(c1)
                if all(k not in m or m[k] == p for k, p in c2):
                    m.update(c2); nxt.append(frozenset(m.items()))
        clauses = nxt
    return len(clauses)
for d in [2, 4, 6, 8, 10, 12]:
    t0 = time.perf_counter(); cnt = dnf_clauses(d)
    print(f"DNF depth={d}: clauses={cnt}, time_ms={(time.perf_counter()-t0)*1e3:.3f}")

@dataclass(frozen=True)
class DT: pass
@dataclass(frozen=True)
class DTop(DT): pass
@dataclass(frozen=True)
class DBot(DT): pass
@dataclass(frozen=True)
class DPrim(DT): name: str
@dataclass(frozen=True)
class DFun(DT): arg: DT; ret: DT
@dataclass(frozen=True)
class DLater(DT): inner: DT
@dataclass(frozen=True)
class DMem(DT): lo: DT; hi: DT
@dataclass(frozen=True)
class DSel(DT): path: str

def sub_dot(env: dict[str, DMem], t1: DT, t2: DT, mode: str, idx: int = 0, depth: int = 0) -> bool:
    if depth > 12: return False
    if t1 == t2 or isinstance(t2, DTop) or isinstance(t1, DBot): return True
    if mode == "gdot":
        if isinstance(t2, DLater) and sub_dot(env, t1, t2.inner, mode, idx, depth + 1): return True
        if idx > 0 and not (isinstance(t1, DLater) and isinstance(t2, DLater)):
            if sub_dot(env, DLater(t1), DLater(t2), mode, idx - 1, depth + 1): return True
        if isinstance(t1, DLater) and isinstance(t2, DLater):
            if sub_dot(env, t1.inner, t2.inner, mode, idx + 1, depth + 1): return True
    if isinstance(t1, DFun) and isinstance(t2, DFun):
        return sub_dot(env, t2.arg, t1.arg, mode, idx, depth + 1) and sub_dot(env, t1.ret, t2.ret, mode, idx, depth + 1)
    if isinstance(t1, DSel) and t1.path in env:
        b = env[t1.path]
        if mode == "scala3_untrusted":
            return sub_dot(env, b.hi, t2, mode, idx, depth + 1) and sub_dot(env, b.lo, t2, mode, idx, depth + 1)
        return sub_dot(env, b.hi, t2, mode, idx, depth + 1)
    if isinstance(t2, DSel) and t2.path in env:
        b = env[t2.path]
        if mode == "scala3_untrusted":
            return sub_dot(env, t1, b.lo, mode, idx, depth + 1) and sub_dot(env, t1, b.hi, mode, idx, depth + 1)
        return sub_dot(env, t1, b.lo, mode, idx, depth + 1)
    if mode in ("naive_dot", "gdot"):
        for p in env:
            pv = DSel(p)
            if pv != t1 and pv != t2 and sub_dot(env, t1, pv, mode, idx, depth + 1) and sub_dot(env, pv, t2, mode, idx, depth + 1):
                return True
    return False

bad = {"x": DMem(DPrim("Int"), DFun(DPrim("Bool"), DPrim("Int")))}
gbad = {"x": DMem(DLater(DPrim("Int")), DLater(DFun(DPrim("Bool"), DPrim("Int"))))}
good = {"y": DMem(DPrim("Int"), DTop())}
print("naive_dot(Int <: Bool->Int via x.T):", sub_dot(bad, DPrim("Int"), DFun(DPrim("Bool"), DPrim("Int")), "naive_dot"))
print("scala3_untrusted(Int <: x.T, bad):", sub_dot(bad, DPrim("Int"), DSel("x"), "scala3_untrusted"))
print("scala3_untrusted(Int <: Bool->Int, bad):", sub_dot(bad, DPrim("Int"), DFun(DPrim("Bool"), DPrim("Int")), "scala3_untrusted"))
print("scala3_untrusted(Int <: y.T, good):", sub_dot(good, DPrim("Int"), DSel("y"), "scala3_untrusted"))
print("scala3_untrusted(y.T <: Top, good):", sub_dot(good, DSel("y"), DTop(), "scala3_untrusted"))
print("gdot idx=0 (Int <:[0] Bool->Int via TTMemL):", sub_dot(gbad, DPrim("Int"), DFun(DPrim("Bool"), DPrim("Int")), "gdot", 0))
print("gdot idx=0 (Int <:[0] ▷(Bool->Int) via TTMemL):", sub_dot(gbad, DPrim("Int"), DLater(DFun(DPrim("Bool"), DPrim("Int"))), "gdot", 0))
print("gdot idx=0 (▷Int <:[0] ▷(Bool->Int) via TTMemL):", sub_dot(gbad, DLater(DPrim("Int")), DLater(DFun(DPrim("Bool"), DPrim("Int"))), "gdot", 0))
print("gdot idx=1 (Int <:[1] Bool->Int via TTMemL):", sub_dot(gbad, DPrim("Int"), DFun(DPrim("Bool"), DPrim("Int")), "gdot", 1))
EOF
```

## Revalidation

- **Re-run the self-contained Python 3 probe above:** Verify clean exit `0`, $\mathrm{lcm}$-scaled `canonicalizeType` DFA growth, $2^d$ DNF clause scaling, and exact separation between `naive_dot`, `scala3_untrusted`, and step-indexed `gdot` under `TTMemL`.
- **Inspect upstream `Scala 3` dual-bound and initialization guards on newer commits:** Fetch `compiler/src/dotty/tools/dotc/core/TypeComparer.scala` and verify `trustBounds` predicates in `thirdTryNamed` / `fourthTry` (`TypeComparer.scala:634, 1019`) alongside `Semantic.checkTermUsage` (`Semantic.scala:1676-1685`) and `Objects.checkCost` (`Objects.scala:101`).
- **Inspect upstream `MLscript` normal forms:** Diff `hkmc2/shared/src/main/scala/hkmc2/invalml/{NormalForm,ConstraintSolver}.scala` to verify whether recursive type normalization or Boolean clause caching thresholds have changed relative to revision `a44346127da2c608bfe4503d630e99c4ba9aa31c`.
- **Inspect `gDOT` axiom footprint:** Re-run `coqc` on `tests/test_used_axioms.v` in `Blaisorblade/dot-iris` (`203d45ea4be590e9dfca84ed83374494af0a3db4`) to confirm `type_soundness` depends exclusively on `functional_extensionality` and `proof_irrelevance`.
