# Graded Dependent Erasure, Uniqueness-versus-Linearity Polarity, and Duoidal High-Water-Mark Resource Algebras

## Summary

Core intermediate calculi that combine dependent type indices, pure duplicable values, linear consumption obligations, exclusive mutation guarantees, and physical resource budgets face four structural constraints established across Quantitative Type Theory (`QTT`, `Idris 2`), `GraD`, `pi-forall`, `Granule`, `linear-base`, Automatic Amortized Resource Analysis (`AARA`), and duoidal dependence categories:

1. **Runtime `0`-erasure and compile-time definitional irrelevance are distinct judgements.** In `QTT` (`Atkey 2018`) and `GraD` (`Choudhury et al. 2021`), grade `0` denotes *runtime* irrelevance enforced by usage-aware heap semantics and stripped without runtime tags (`Idris 2` `Compiler.CompileExpr`), yet `0`-graded type arguments remain *relevant* during compile-time conversion (`Idris 2` `Core.Normalise.Convert`). Ignoring arguments during conversion—as `pi-forall` (`Equal.hs`) does for `Arg Irr`—implements proof irrelevance and is unsound for type-distinguishing indices such as vector length `n` in `Vect n A`.
2. **Pure values are type-isomorphic to unrestricted capabilities (`!A -> B` vs. `A -> B`) only up to heap boxing, strictness forcing, and deep-copy overhead.** In `linear-base`, `Ur a` (`Data.Unrestricted.Linear.Internal.Ur`) is a boxed `data` GADT rather than an unboxed `newtype` so pattern-matching forces thunk evaluation and prevents unconsumed linear resources from escaping inside lazy closures; converting a linear recursive structure of size $N$ into `Ur` via `Movable.move` incurs an $O(N)$ deep copy. Under Call-by-Value (`CBV`), `Granule` (`Checker.hs`) explicitly blocks promoting expressions that allocate mutable or channel resources (`resourceAllocator e`) into graded boxes `[e] : []_r A` to prevent single-evaluation pointer aliasing.
3. **Linearity restrictions and uniqueness guarantees induce opposite subtyping/coercion polarities.** Linearity restricts *future* consumption, validating dereliction `!A -> A` while rejecting `A -> !A`. Uniqueness certifies absence of *past* aliasing, validating forgetting uniqueness `*A -> !A` (`uniqueReturn` / `share`) while rejecting `!A -> *A`. Together they form the directed chain `*A -> !A -> A`; recovering `*A` from `!A` requires an explicit `Cloneable` deep copy with existential region renaming (`uniqueBind`), whereas zero-copy temporary mutation requires fractional borrowing (`& f A` with `withBorrow`, `split`, and `join`).
4. **Multi-resource tuples combining cumulative latency (`WCET`) with peak memory (`SRAM` high-water marks) do not form a semiring and exhibit opposite duoidal interchange polarities.** Sequential peak composition fails to distribute over parallel additive memory (`max(5, 1 + 1) = 5 != max(5, 1) + max(5, 1) = 10`), and scalar `max(p1, p2)` under-counts sequential heap watermarks whenever net retained allocation `n1 > 0` (`(4, 4) ; (0, 3) = (4, 7)`, not `4`). Sound compositional high-water-mark tracking requires `AARA`-equivalent `(net, peak)` pairs $\mathcal{M} = \{(n, p) \in \mathbb{Z} \times \mathbb{N} \mid p \ge \max(0, n)\}$ with $(n_1, p_1) \fatsemi (n_2, p_2) = (n_1 + n_2, \max(p_1, n_1 + p_2))$ and $(n_1, p_1) \parallel (n_2, p_2) = (n_1 + n_2, p_1 + p_2)$. Refining asynchronous parallel pipelines $(a \fatsemi b) \parallel (c \fatsemi d)$ into barrier-synchronized stages $(a \parallel c) \fatsemi (b \parallel d)$ increases `WCET` (**lax** interchange: $(a \fatsemi b) \parallel (c \fatsemi d) \le (a \parallel c) \fatsemi (b \parallel d)$) while decreasing `peak` memory across all signed $(n, p) \in \mathcal{M}$ (**colax** interchange: $((a \parallel c) \fatsemi (b \parallel d)).\text{peak} \le ((a \fatsemi b) \parallel (c \fatsemi d)).\text{peak}$). Subtracting reconvergence or slack credits via $\text{eff}(t, d) = \max(0, t - d)$ under additive composition is non-monotone unless $0 \le d_i \le t_i$ holds at every leaf.

## Applicability

This report characterizes the static typing, operational erasure, representation layout, subtyping variance, resource-algebra composition, and validation requirements of intermediate and surface languages that combine dependent types, linear/unique ownership, and static resource bounds.

### Subject Relationships and Scope

- **`idris-lang/Idris2`** (`cf66cb4ccb8f0df7876fd07842f056f6222b9dce`) and **`Atkey (LICS 2018)`** (`DOI: 10.1145/3209108.3209189`): Examined as a concrete full-spectrum `QTT` compiler over the `{0, 1, omega}` (`ZeroOneOmega`) semiring, establishing how `0`-multiplicity binders behave in elaboration (`TTImp.ProcessType`), linearity checking (`Core.LinearCheck`), conversion (`Core.Normalise.Convert`), and tag-free runtime argument dropping (`Core.CompileExpr` and `Compiler.CompileExpr`; note that `src/Compiler/Erase.idr` does not exist at this revision because erasure was folded into `CompileExpr`).
- **`Choudhury et al. (POPL 2021, GraD)`** (`DOI: 10.1145/3434331`) and **`sweirich/pi-forall`** (`75feff0f86f10d02c9e69999f0a112d0d289c948`): Examined in comparison to separate `GraD`'s usage-aware heap semantics (runtime non-interference for `0`-graded bindings with conversion-relevant type indices) from `pi-forall`'s stage-annotated bidirectional checker (`full/src/TypeCheck.hs`, `full/src/Equal.hs`), which implements compile-time definitional irrelevance (`Arg Irr`).
- **`tweag/linear-base`** (`bb5182a76c84eedcf78536c9ce24cb900882b2f3`) and **`granule-project/granule`** (`85a463f18914353669ff291677c47190fff43b23`) alongside **`Marshall, Vollmer, and Orchard (ESOP 2022)`** (`DOI: 10.1007/978-3-030-99336-8_13`): Examined to test macro-expressibility of duplicable values via comonadic wrappers (`Ur a`, `Box c t`) under lazy (`GHC` Linear Haskell) versus strict (`Granule` CBV) evaluation, and to extract the exact subtyping, cloning, and fractional-borrowing rules connecting linearity (`[]_r A`) and uniqueness (`*A`, `& f A`).
- **`Hofmann and Jost (POPL 2003)`** (`DOI: 10.1145/604131.604148`), **`Hoffmann, Das, and Weng (POPL 2017, RaML)`** (`DOI: 10.1145/3009837.3009842`), and **`Shapiro and Spivak (arXiv:2210.01962v2)`** (`DOI: 10.48550/arXiv.2210.01962`): Synthesized with finite-domain algebraic verification to establish exact composition laws for net-plus-peak memory watermarks, duoidal poset variance, and pessimism-credit side conditions.

Findings derived from direct repository source inspection apply specifically to the pinned commits above. Algebraic counterexamples and universal poset inequalities over $(\mathbb{N}, +, \max)$ and $\mathcal{M}$ hold mathematically for any resource type system instantiating those operators.

## Findings

### 1. Usage-Aware Operational Semantics and the Split Between `0`-Erasure and Proof Irrelevance

`Basis: normative + source`

Standard substitution-based small-step semantics $(\lambda x.\, e)\, v \mapsto e[v/x]$ duplicates or discards $v$ syntactically before $x$ is demanded, making runtime multiplicity violations invisible to type preservation. `Choudhury et al. (POPL 2021, GraD)` (`DOI: 10.1145/3434331`) resolve this by evaluating open terms against an explicit usage-annotated heap $H$ mapping each heap variable $x$ to a grade-annotated binding $x \mapsto^q e$ over a partially ordered semiring $(Q, +, \cdot, 0, 1, \le)$:

$$\frac{H = H_1,\, x \mapsto^{q' + 1} v,\, H_2 \quad v\text{ value}}{(H;\, x) \;\longmapsto\; (H_1,\, x \mapsto^{q'} v,\, H_2;\; v)}$$

Looking up $x$ consumes $1$ unit of grade ($q = q' + 1$); if $x$ carries grade $0$ and $0 \not\ge 1$ (e.g., in $\{0, 1, \omega\}$ or $\mathbb{N}$), evaluation of $(H; x)$ gets stuck. Type soundness (`Heap Preservation` and `Progress`) proves that well-typed closed programs at grade $1$ never demand a `0`-graded heap cell, and bisimulation over the heap stripping operator $|\cdot|$ proves **Erasure Non-Interference**: replacing every `0`-graded argument with a dummy token $\Box$ produces identical terminal values.

Across implemented dependent typecheckers, however, two distinct notions of "irrelevant / erased argument" exist and cannot be conflated:

| Property | Quantitative `0`-Erasure (`Atkey 2018`, `GraD`, `Idris 2`) | Compile-Time Proof Irrelevance (`pi-forall` `Irr`) |
| :--- | :--- | :--- |
| **Semiring / stage carrier** | `ZeroOneOmega = Rig0 \| Rig1 \| RigW` (`Idris 2` `src/Algebra/ZeroOneOmega.idr:9`) | Binary stage `Epsilon = Rel \| Irr` (`pi-forall` `full/src/Syntax.hs`) |
| **Type formation grade** | `QTT`: $0\Gamma \vdash A\text{ type}$ (`InType` uses `PI erased` at `ProcessType.idr:164–165`); `GraD`: graded contexts in types | `tcType tm = Env.withStage Irr $ checkType tm TyType` (`full/src/TypeCheck.hs:155`) |
| **Resurrection when checking `0`/`Irr` arg** | `LinearCheck.idr:166`: `when (not erase) $ rigSafe rigb rig` (`0 * q = 0` scales context) | `if ep1 == Irr then Env.extendCtx (Demote Rel) else id` (`full/src/TypeCheck.hs:58`) |
| **Definitional equality (`equate` / `convert`)** | **Compared normally:** `NTCon`/`NDCon` call `allConv` on all args (`Convert.idr:388–395`) | **Ignored unconditionally:** `equateArg (Arg Irr t1) (Arg Irr t2) = return ()` (`full/src/Equal.hs:127`) |
| **Runtime representation** | Dropped from arity/closures (`Compiler/CompileExpr.idr:107–124, 198–203`) | Erased in extraction, or untyped |
| **Sound for type-distinguishing indices (`n` in `Vect n A`)?** | **Yes:** `Vect 2 Int != Vect 3 Int` at compile time, yet `n` costs `0` bytes at runtime | **No:** `TyCon "Vect" [Arg Irr 2, Arg Rel Int]` equates with `Vect [Arg Irr 3, Int]`, breaking memory safety |

In `Idris 2` (`cf66cb4ccb8f0df7876fd07842f056f6222b9dce`), runtime erasure is tag-free and arity-shrinking:
1. During declaration elaboration (`src/TTImp/ProcessType.idr:172–181`), `findErased fullty` computes two `NatSet` bitmaps stored in `GlobalDef` (`src/Core/Context/Context.idr:307`): `eraseArgs` (all runtime `Rig0` positions) and `safeErase` (positions safe to erase during case-tree detagging).
2. During IR lowering (`src/Compiler/CompileExpr.idr:27–40, 107–124, 166–170, 212–233`), `numArgs` classifies every data constructor `DCon` and function `PMDef` into `NewTypeBy arity pos` (when `arity - size eraseArgs == 1`, unboxing wrapper types completely without matching unless `WorldVal` IO sequencing is involved at lines `249–260`) or `EraseArgs arity epos`.
3. `eraseConArgs` and `mkDropSubst` physically remove `Rig0` slots from constructor heap layouts, function call argument lists, and pattern-match variable environments (`shrinkCExp sub sc'`), while `Let _ rig val _` compiles via `branchZero (shrinkCExp (Drop Refl) sc') (CLet ...) rig` (`CompileExpr.idr:168–170`), eliding `Rig0` let-bindings entirely.

Because `QTT` types are formed in a `0`-multiplied context ($0\Gamma \vdash A : \text{Type}$), a type expression cannot *consume* a linear resource (`1` multiplied by `0` is `0`, not `1`). Consequently, `QTT` rejects propositions that assert ownership of linear state inside dependent types, whereas `Atkey (2018)` §2.3 notes that strong projections `fst` on `(x :_0 A) * B(x)` must be restricted whenever `B` depends computationally on `x`, requiring pattern-matching eliminators `let (x, y) = p in ...` so `x` stays bound at multiplicity `0`.

---

### 2. Value-versus-Capability Macro-Expressibility (`Ur a`, Lazy Thunk Forcing, and CBV Promotion Guards)

`Basis: source + derived`

A recurring core-calculus minimization question asks whether pure duplicable values (`Val`) can be eliminated as an independent primitive and macro-expressed—in the sense of Felleisen (*On the Expressive Power of Programming Languages*, Science of Computer Programming 17, 1991)—as linear capabilities carrying an unrestricted, drop-free comonadic grade (`!A` / `Ur A` / `[]_[0..Inf] A`). Under Girard's linear logic translation $(A \to B)^\circ = {!A^\circ} \multimap B^\circ$, `tweag/linear-base` (`bb5182a76c84eedcf78536c9ce24cb900882b2f3`, `src/Data/Unrestricted/Linear.hs:15`) witnesses the type isomorphism `(Ur a %1-> b) ~= (a -> b)`. Direct inspection of `linear-base` and `Granule`, however, establishes three operational and representational obstructions to collapsing pure values into boxed capabilities:

1. **Mandatory Heap Boxing in Non-Strict Semantics (`Ur` Cannot Be a `newtype`):**
   In `linear-base` (`src/Data/Unrestricted/Linear/Internal/Ur.hs:34–35`), `Ur` is defined as a GADT `data` box rather than a zero-cost `newtype`:
   ```haskell
   data Ur a where
     Ur :: a -> Ur a
   ```
   Its `Generics.Linear` representation (`Ur.hs:81–95`) wraps the field in `MP1 'Many (Rec0 a)`. In lazy Linear Haskell, if `Ur` were a `newtype` (erased to `coerce`), a linear binding $x :_1 A$ captured inside an unevaluated `Ur` expression could be duplicated or discarded without ever evaluating the linear computation that discharges $x$. Pattern-matching `case u of Ur x -> ...` must force the `Ur` constructor closure to Weak Head Normal Form (`WHNF`), paying a pointer indirection and heap-closure header per wrapped value unless worker/wrapper unboxing eliminates it statically.
2. **$O(N)$ Deep-Copy Coalgebra Cost (`Movable.move`):**
   Converting a linearly bound pure value into an unrestricted capability requires a coalgebra of the `Ur` comonad (`src/Data/Unrestricted/Linear/Internal/Movable.hs:58–59`):
   ```haskell
   class (Dupable a) => Movable a where
     move :: a %1 -> Ur a
   ```
   For recursive algebraic data types such as lists (`Movable.hs:140–146`), `move` cannot reinterpret ownership in $O(1)$ time; it traverses and reallocates every spine cell:
   ```haskell
   go :: [a] %1 -> Ur [a]
   go [] = Ur []
   go (a : l) = (:) Data.<$> move a Data.<*> go l
   ```
   As documented at `Movable.hs:45` (*"bear in mind that this typically induces a deep copy of the value"*), encoding ordinary pure data uniformly as linear values that must be lifted into `Ur` whenever shared turns $O(1)$ pointer sharing of immutable structures into $O(N)$ heap copying.
3. **Call-by-Value Promotion Unsoundness Without Allocator Guards (`Granule`):**
   In a strict (`CBV`) graded language, promoting an expression `[e] : []_r \tau` evaluates `e` under graded context multiplication (`[G]*r |- [e] : []_r t`, `Granule` `frontend/src/Language/Granule/Checker/Checker.hs:716–749`). If `e` allocates a mutable array or channel from pure inputs (e.g., `newFloatArray 16`, whose input `16 : Int` is unrestricted!), context multiplication `[] * 2 = []` succeeds, yet CBV evaluation of `let [arr] = [newFloatArray 16] in ...` would allocate *one* physical buffer and duplicate its pointer across $r = 2$ uses. `Granule` must therefore maintain a hard-coded syntactic side condition in `Checker.hs:726–734`:
   ```haskell
   promotable <-
     if CBN `elem` globalsExtensions ?globals
       then return True
       else return (not (resourceAllocator e)
                  || (UnsafePromotion `elem` globalsExtensions ?globals))
   unless promotable (throw $ UnpromotableError{errLoc = s, errTy = ty})
   ```
   backed by the explicit primitive denylist `unpromotables = ["newFloatArray", "newRef", "forkLinear", "forkMulticast", "forkReplicate", "forkReplicateExactly"]` (`Primitives.hs:835–836`). Under Felleisen's criterion, adding mutable capabilities forces a global syntactic non-local check (`resourceAllocator`) into the promotion rule of the unrestricted comonad under CBV.

---

### 3. Polarity Duality Between Linearity Restrictions and Uniqueness Guarantees

`Basis: normative + source + execution (standalone finite-domain verification)`

`Marshall, Vollmer, and Orchard (ESOP 2022)` (`DOI: 10.1007/978-3-030-99336-8_13`) and `Granule` (`85a463f18914353669ff291677c47190fff43b23`) demonstrate that **linearity** and **uniqueness** cannot be collapsed into a single coeffect grade with uniform variance because they constrain opposite halves of a value's timeline:

- **Linearity (`A` vs. `!A` / `a [0..Inf]`)** is a *prospective restriction* on the consumer: the continuation promises to consume the value linearly ($1$ time). If a producer supplies an unrestricted capability `!A` (permitting $[0..\infty]$ uses), a consumer expecting linear `A` can safely accept it by restricting its own future actions (**dereliction** `!A -> A` is sound; promotion `A -> !A` is unsound). In `Granule`, coeffect approximation in `relGrades` (`Checker/Types.hs:69–74`) encodes this contravariant demand ordering (`addConstraint (rel s (inj2 c') (inj1 c) kind)`).
- **Uniqueness (`*A` vs. `!A`)** is a *retrospective guarantee* from the producer: no alias to the underlying heap storage has ever been duplicated in the past, licensing destructive in-place mutation (`writeFloatArray`, `swapRef`) and deterministic deallocation (`deleteFloatArray`, `Primitives.hs:712–739`). Forgetting that guarantee by sharing `*A` into `!A` is a sound one-way transition (`uniqueReturn : *a -> a [r]`, `Primitives.hs:660–663`), whereas coercing `!A -> *A` is unsound because pre-existing aliases would observe in-place mutation.

`Granule`'s canonical test suite (`examples/uniqueness.gr:3–18`) witnesses all four higher-order variance cases directly:

| Combinator Signature in `Granule` | Status | Semantic Polarity Justification |
| :--- | :---: | :--- |
| `redeem : (!p -> *q) -> *p -> *q` (`f (share x)`) | **Valid** | Contravariant Lift of `*p -> !p`: forgetting uniqueness on input `*p` yields `!p` |
| `derelict : (*p -> *q) -> !p -> *q` | **Rejected** | Unsound `!p -> *p`: cannot fabricate past non-aliasing from a shared `!p` |
| `derelict' : (p -> q) -> !p -> q` (`\f !a -> f a`) | **Valid** | Dereliction `!p -> p`: an unrestricted `!p` satisfies a linear consumer `p -> q` |
| `redeem' : (!p -> q) -> p -> q` | **Rejected** | Unsound `p -> !p`: cannot duplicate/drop a linear obligation `p` |

Consequently, ownership states form the **non-symmetric three-point directed chain**

$${*A} \;\xrightarrow{\;\text{uniqueReturn / share}\;}\; {!A} \;\xrightarrow{\;\text{derelict}\;}\; A$$

where neither endpoint embeds into the other without runtime work or scoped lifetime discipline. `Granule` provides two distinct, non-interchangeable mechanisms to cross back toward exclusive mutation (`Checker.hs:938–1002`, `Primitives.hs:683–706`):
1. **Deep-Copy Recovery (`uniqueBind` / `clone e as x in body`):** Requires solver constraint `(1 : s) <= r` on input `e : a [r]`, predicate constraint `Cloneable a`, and existential region freshening `exists {id' : Name} . *(Rename id id' a)` (`Checker.hs:961–999`), paying an $O(N)$ copy to create a physically fresh unique allocation.
2. **Fractional Scoped Borrowing (`& f a`):** Unifies `*a` internally as `& Star a` (`Checker.hs:975`, `Primitives.hs:117`) and introduces `withBorrow : (& 1 a -> & 1 b) -> *a -> *b`, `split : {f /= Star} => & f a -> (& (f * 1/2) a, & (f * 1/2) a)`, and `join : {f /= Star, g /= Star} => (& f a, & g a) -> & (f + g) a`. Read-only operations (`readFloatArray`) accept arbitrary permission `& f`, mutable updates (`writeFloatArray`, `swapRef`) require `{mut f}` ($f = 1$), and `deleteFloatArray` requires full unborrowed `*` (`Star`), preventing deallocation during an active borrow without copying.

---

### 4. Non-Distributive Peak High-Water-Mark Algebras, `(net, peak)` AARA Transformers, and Duoidal Interchange

`Basis: normative + derived + execution (standalone Python exhaustive algebraic verification)`

Systems intermediate representations frequently attempt to attach multi-dimensional physical resource grades—such as Worst-Case Execution Time (`WCET`) alongside stack or scratchpad `SRAM` peak high-water marks and current-slew bounds—to a single semiring-graded capability modality. Algebraic analysis and exhaustive finite-domain verification establish why this fails and identify the minimal sound replacement.

#### 4.1 Failure of Semiring Distributivity and Scalar `max` Sequential Composition

1. **Failure of Semiring Distributivity (`seq = max`, `par = +`):** For zero-net stack-scoped frames where sequential execution takes the maximum peak $\max(s, a)$ and parallel execution sums simultaneous peaks $a + b$, sequential composition does **not** distribute over parallel composition:
   $$\max(5,\; 1 + 1) = 5 \;\neq\; 10 = \max(5, 1) + \max(5, 1).$$
   Moreover, parallel addition is non-idempotent ($1 + 1 = 2 \neq 1$), so `par` is not a join-semilattice either. By contrast, `WCET` (`seq = +`, `par = max`) *does* form a tropical max-plus semiring because $t + \max(a, b) = \max(t + a, t + b)$. A product of `WCET` and `SRAM` is therefore **not** a product semiring.
2. **Unsoundness of Scalar `max` Under Surviving Allocations:** When sequential step $e_1$ retains net heap/arena memory ($n_1 > 0$), scalar $\max(p_1, p_2)$ under-counts true peak usage. If $e_1$ allocates $4\text{ KiB}$ and retains it ($n_1 = 4, p_1 = 4$) and $e_2$ allocates and frees $3\text{ KiB}$ ($n_2 = 0, p_2 = 3$), peak live memory during $e_1 \fatsemi e_2$ is $4 + 3 = 7\text{ KiB} > \max(4, 3) = 4\text{ KiB}$.

#### 4.2 Exact AARA `(net, peak)` Monoid Isomorphism

In `Hofmann and Jost (POPL 2003)` (`DOI: 10.1145/604131.604148`) and `RaML` (`Hoffmann, Das, and Weng, POPL 2017`, `DOI: 10.1145/3009837.3009842`), heap high-water marks are tracked by affine potential judgements $\Gamma;\, q \vdash e : (A,\, q')$, where $q \ge 0$ is incoming free heap cells before $e$ and $q' \ge 0$ is free cells remaining after $e$ (plus linear/polynomial potential stored in data constructors). Extracting the minimal initial potential $p = q_{\min} \ge 0$ needed to execute $e$ without exhaustion and the net allocation $n = q - q' \in \mathbb{Z}$ yields the **AARA net-plus-peak carrier**:

$$\mathcal{M} = \{(n, p) \in \mathbb{Z} \times \mathbb{N} \mid p \ge \max(0, n)\}$$

equipped with shared identity $I = (0, 0)$ and two associative monoid operations:
- **Sequential high-water-mark composition:** $(n_1, p_1) \fatsemi (n_2, p_2) = \big(n_1 + n_2,\; \max(p_1,\; n_1 + p_2)\big)$. (Closure proof: since $p_1 \ge 0$ and $p_2 \ge 0$, $\max(p_1, n_1 + p_2) \ge p_1 \ge 0$, and since $p_2 \ge n_2$, $\max(p_1, n_1 + p_2) \ge n_1 + p_2 \ge n_1 + n_2$.)
- **Parallel shared-pool composition:** $(n_1, p_1) \parallel (n_2, p_2) = (n_1 + n_2,\; p_1 + p_2)$. Crucially, because $p_i \ge 0$ bounds each thread's maximum excursion over its entire execution interval $[0, T_i]$ *including its $t = 0$ baseline before any deallocation ($n_i < 0$) occurs*, $\max_{t} (m_1(t) + m_2(t)) \le \max_t m_1(t) + \max_t m_2(t) = p_1 + p_2$ remains sound across **all** asynchronous thread interleavings even when $n_1 < 0$ or $n_2 < 0$.

#### 4.3 Opposite Lax vs. Colax Duoidal Interchange Laws (`Shapiro and Spivak, arXiv:2210.01962v2`)

`Shapiro and Spivak (2022/2025)` (`arXiv:2210.01962v2`) model systems with independent (`||`) and dependent (`;`) composition as normal duoidal categories (whose free expressions correspond to $N$-free / zig-zag-free finite posets). Refining $(a \fatsemi b) \parallel (c \fatsemi d)$ into $(a \parallel c) \fatsemi (b \parallel d)$ adds causal barrier edges $a \prec d$ and $c \prec b$:

1. **Cumulative Latency (`WCET`, max-chain weight) is Lax in Cost Order ($\le$):**
   $$\max(t_a + t_b,\; t_c + t_d) \;\le\; \max(t_a, t_c) + \max(t_b, t_d)$$
   At $(t_a, t_b, t_c, t_d) = (5, 0, 0, 5)$, asynchronous pipelines finish in $\max(5, 5) = 5$, whereas barrier-synchronized stages take $\max(5, 0) + \max(0, 5) = 10$ ($5 < 10$). Adding causal dependencies increases chain length.
2. **Peak Memory (`(net, peak)`, max-antichain width) is Universally Colax in Cost Order ($\sqsubseteq$):**
   For **every** $a, b, c, d \in \mathcal{M}$ (including negative net deallocations $n < 0$), $((a \parallel c) \fatsemi (b \parallel d)).\text{net} = ((a \fatsemi b) \parallel (c \fatsemi d)).\text{net} = n_a + n_b + n_c + n_d$, and:
   $$\begin{aligned}
   ((a \parallel c) \fatsemi (b \parallel d)).\text{peak}
   &= \max\big(p_a + p_c,\; (n_a + p_b) + (n_c + p_d)\big) \\
   &\le \max(p_a,\; n_a + p_b) + \max(p_c,\; n_c + p_d)
   = ((a \fatsemi b) \parallel (c \fatsemi d)).\text{peak}.
   \end{aligned}$$
   At zero-net $(0,5), (0,0), (0,0), (0,5)$, barrier synchronization caps simultaneous memory at $5$, whereas unbarriered pipelines can overlap $a$ and $d$ to hit $10$ ($5 < 10$). At signed $(-2,0), (-2,0), (-2,0), (-2,3)$, barrier synchronization forces $a$ and $c$ to free $4$ units before $d$'s $+3$ spike (peak $0$), whereas unbarriered execution allows $d$ to spike while $a$ has not yet freed its $2$ units (peak $1 > 0$). Adding causal dependencies eliminates antichains and lowers peak memory.

Thus, in cost order, `(wcet, net, peak)` is a **contravariantly split duoidal product**: substituting a barrier-synchronized schedule for an unbarriered parallel schedule is a sound *upper-bound relaxation* for peak memory if and only if the compiler checks the *unbarriered* cost, whereas substituting an unbarriered schedule is a sound upper-bound relaxation for `WCET` if and only if the compiler checks the *barriered* cost.

#### 4.4 Leaf-Bounded Side Condition for Reconvergence / Slack Credits

When static analyses subtract reconvergence or cache-refill pessimism credits $\Delta$ from raw cost $t$ via truncated subtraction $\text{eff}(t, d) = \max(0, t - d)$ while composing $(t_1, d_1) \oplus (t_2, d_2) = (t_1 + t_2, d_1 + d_2)$, unconstrained credits violate monotonicity: for $(t_1, d_1) = (0, 5)$ and $(t_2, d_2) = (10, 0)$, $\text{eff}(0 + 10, 5 + 0) = 5 < \text{eff}(10, 0) = 10$ (prepending a zero-cost step with excess credit artificially shrinks a subsequent real cost). Imposing the **leaf-wise bound** $0 \le d_i \le t_i$ at every primitive node preserves $d_1 + d_2 \le t_1 + t_2$ inductively and restores exact additivity $\text{eff}(t_1 + t_2, d_1 + d_2) = \text{eff}(t_1, d_1) + \text{eff}(t_2, d_2)$.

---

### 5. Multi-Level Performance and Resource Footprint (`L1`–`L6`)

`Basis: source + documentation + execution (SLOC inventory) + derived`

| Level | Metric / Dimension | Quantitative Evidence Across Examined Systems | Architectural Implication |
| :--- | :--- | :--- | :--- |
| **`L1` Authoring Velocity** | Annotation density & human/LLM repair effort | `Idris 2` defaults binders to `RigW` (implicit `0` in types, explicit `0`/`1` only at linear/erased boundaries); `linear-base` requires explicit `dup2`/`consume`/`move` plumbing (`Unrestricted/Linear.hs:25–57`); `RaML` infers polynomial heap potentials automatically via LP with `0` user potential annotations on standard OCaml functions (`Hoffmann et al. 2017` `DOI: 10.1145/3009837.3009842`) | Automatic inference (`AARA` LP or `Idris 2` hole-multiplicity inference `updateHoleUsage` at `LinearCheck.idr:104–150`) eliminates manual structural-combinator boilerplate (`dup2`/`lseq`) that inflates linear functional code by `1.3x–2.5x` |
| **`L2` Toolchain Build** | Compiler / checker source size & build footprint | Measured non-blank/non-comment SLOC: `pi-forall/full/src` `2,787` (`9` files); `Granule` `Checker/` `7,573` (`28` files, `14,758` frontend total across `59` files); `linear-base/src` `9,057` (`87` files, `788` in `Unrestricted/`); `Idris 2` `src/Core` `22,992` (`64` files) + `src/Compiler` `9,224` (`33` files) | Adding SMT-backed arbitrary semiring/interval/fraction solving (`Granule` `SBV` bridge) roughly triples checker SLOC relative to a fixed `{0, 1, omega}` syntactic checker (`pi-forall` / `Idris 2` `LinearCheck.idr` at `706` raw lines) |
| **`L3` Elaboration & Synthesis** | Constraint solving & interactive latency | `Idris 2` `lcheck` (`LinearCheck.idr`) is a single syntax-directed $O(\text{AST})$ pass (`< 5 ms` per definition); `Granule` (`Constraints.hs:46–73`) fast-paths `isTrivial predicate` in `0.0 ms` but spawns external Z3 via `Data.SBV` on non-trivial grade predicates (tens of ms to `solverTimeoutMillis` tail timeouts); `RaML` degree-$d$ `AARA` generates $O(\binom{k+d}{d})$ LP variables per constructor solved in `10 ms–2 s` via CLP | Keep core multiplicity checking decidable in linear AST time (`{0, 1, omega}` + closed-form `(net, peak)` propagation); invoke LP/SMT only during off-path bound inference and export dual witnesses |
| **`L4` Generated Code** | Runtime throughput, boxing & copy cost | `Idris 2` `EraseArgs` + `NewTypeBy` (`CompileExpr.idr:82–113`) achieves `0`-cycle/byte overhead for `Rig0` indices; `Granule` `*FloatArray` (`Primitives.hs:718`) mutates arrays in-place with `0` GC barriers; `linear-base` `Ur a` adds `1` heap pointer indirection (`2` words in GHC) and `Movable.move` on `[a]` costs $O(N)$ allocations | Native unboxed pure values + `Rig0` arity dropping + `*A`/`& f A` borrowing preserve zero-copy register/SIMD codegen; encoding pure values via `Ur` degrades tight loops unless aggressively worker/wrapper unboxed |
| **`L5` Certificate Checking** | Kernel / certificate verification speed | Checking a pre-elaborated `QTT` term or `(net, peak)` derivation tree is $O(|\text{AST}|)$ arithmetic with zero search; checking an `AARA` bound via Farkas/LP primal-dual feasibility certificates (`Ax = b, x >= 0`) is $O(\text{nnz}(A))$ sparse dot-product checking (`< 1 ms` for $10^4$ constraints) vs. $O(n^3)$ Simplex search | Externalizing `AARA` LP/SMT search into linear potential annotations on AST binders reduces kernel admission to single-pass `max`/`+` evaluation without linking Z3 or CLP into the TCB |
| **`L6` Memory & Artifact Size** | Compiler RSS, interface `.ttc` & runtime SRAM | `Idris 2` serializes `RigCount` as `1` byte (`0`, `1`, `2`) in `.ttc` binaries (`Core/TTC.idr:126–137`) and `eraseArgs` as a compact `NatSet` (`TTC.idr:1143`); stripping `Rig0` fields shrinks runtime closure and constructor words proportionally to index count (e.g., `Cons {0 a} {0 n} x xs` drops from `4` fields to `2` fields, a `50%` heap reduction) | `0`-erasure directly halves heap allocation on length-indexed/proof-carrying inductive structures while costing `1` byte per binder in compiled interface metadata |

---

### 6. Human Comprehensibility and Conceptual Simplicity (`C1`–`C2`)

`Basis: source + derived`

- **`C1` Human Comprehensibility and Mental-Model Ergonomics:**
  - *Concept count and temporal orientation:* Programmers routinely confuse "this binding cannot be used twice (`1`)" with "no other reference to this allocation exists (`*`)". `Granule`'s separation of `[r]` (brackets for future usage count), `*` (star for uniqueness guarantee), and `& f` (ampersand for fractional borrow) makes the distinction syntactically explicit, whereas overloading a single `linear` keyword hides whether in-place mutation is safe.
  - *Diagnostic legibility:* Syntactic `QTT` checkers (`Idris 2` `LinearCheck.idr:171`, `LinearMisuse fc name l r`) pinpoint the exact variable and multiplicity mismatch locally (`"Trying to use linear name x in non-linear context"`). Conversely, solver-backed coeffect checkers (`Granule` `Constraints.hs:80–99`) emit negated existential-universal `SBV` countermodels over generated grade variables (`nec_[line]`, `.lower`, `.upper`) whenever `trivialUnsatisfiableConstraints` fails to isolate a `1 = 0` atom—requiring global reasoning across case-join equations (`joinCtxts` at `Checker.hs:855`).
- **`C2` Conceptual Simplicity, Orthogonality, and Model Refinement:**
  - *Refusing false unification:* Attempting to unify pure values into `Ur`-capabilities, collapse `*` and `!` into one modality, or model `(WCET, SRAM)` as a semiring violates Ousterhout's deep-module principle: it shrinks surface BNF production counts by `1–2` constructors while pushing syntactic `resourceAllocator` exceptions (`Checker.hs:730`), $O(N)$ `Movable` deep-copy typeclasses, or unsound peak-memory under-counts into every pass consumer.
  - *True minimal factorization:* Three orthogonal, algebraically honest components cover all examined cases without ad-hoc patches:
    1. **Multiplicity semiring `{0, 1, omega}`** on binders (governing runtime erasure vs. linear obligation, keeping `0`-binders conversion-relevant for dependent indices);
    2. **Aliasing/permission lattice (`Unique 1` -> `SharedFraction f` -> `SharedUnrestricted`)** on memory-bearing references (governing in-place mutation vs. read sharing);
    3. **Normal duoidal resource grades** parameterized by variance (`lax` tropical `(+, max)` for cumulative latency vs. `colax` `AARA` `(net, peak)` for high-water-mark space).

---

### 7. End-to-End Solution and Implementation Validation (`V1`–`V4`)

`Basis: source + documentation + derived`

Formal type soundness over an idealized lambda or heap machine leaves four concrete reality gaps that require complementary validation layers:

- **`V1` Specification Adequacy, Negative Polarity Suites, and Golden Usage-Heap Bisimulation:**
  - *Negative typing suites:* `Granule` validates polarity boundaries via dedicated negative test cases (`frontend/tests/cases/negative/unique/{uniqueProduct.gr,uniqueFunction.gr,badClone.gr,cloneNonCloneable.gr}`) ensuring that unique closures capturing linear/shared environment variables and clones of non-`Cloneable` handles are rejected.
  - *Golden usage-heap differential bisimulation & `QuickCheck`:* `pi-forall` includes property-based AST generators (`full/src/Arbitrary.hs`); extending PBT to run well-typed terms simultaneously on an instrumented `GraD` usage-counting heap (`x |->^q v`) and on the `CompileExpr`-erased target detects both premature `0`-lookup bugs and vacuous resource specifications (`q` over-approximated by `omega` when `1` was intended).
- **`V2` Erasure-Lowering, `newtype`-Detagging, and `Unsafe.Linear` Fuzzing:**
  - *Compiler erasure edge cases:* `Idris 2`'s `Compiler.CompileExpr` (`lines 247–260`) contains a critical soundness guard in `getNewType`: unwrapping a single-non-erased-field constructor without pattern matching is **unsound** if the constructor wraps `%World` (`WorldVal`), because eliding the match can drop or reorder strict `IO` side effects! Differential fuzzing (`CSmith`/`QuickCheck`-style random GADT + `%World` + `Rig0` generators comparing Chez Scheme, Racket, and RefC backends) is essential to catch over-eager detagging.
  - *Trusted coercion audits:* `linear-base` relies on `Unsafe.Linear.coerce` (`lcoerce` in `Movable.hs:193,196`) inside `Generic` instances; mutation-testing those instances by injecting duplicate field references verifies whether linear property tests catch reference-count leaks.
- **`V3` Runtime System (`GC`/Thunk), Concurrency, and Hardware Stack/Side-Channel Validation:**
  - *GHC RTS & GC aliasing gap:* In `linear-base`, GHC's lazy runtime and parallel copying garbage collector may hold transient internal pointers (blackholed thunks, remembered-set cards) to a linearly typed heap object; hence `Data.Array.Mutable.Linear` allocates mutable buffers in off-heap pinned/unmanaged memory (`Foreign.Marshal.Pure`) rather than mutating normal GC heap closures in place.
  - *Weak-memory session channels:* Concurrent linear session primitives (`forkLinear`, `send`, `recv` in `Granule` `Primitives.hs:410–426`) require stateless weak-memory model checking (`GenMC` / `Loom`) of the underlying lock-free channel runtime to ensure release/acquire publication before ownership handoff.
  - *Hardware stack slack & leakage:* Abstract `AARA` `(net, peak)` counts heap/frame cells, omitting ABI register-spill slots, `16`-byte stack alignment padding, red-zone clobbers, and asynchronous interrupt (`ISR`) frames on embedded targets, which must be validated against binary machine-code stack analyzers (`llvm-readobj --stack-sizes` + WCET/stack CFG solvers). Furthermore, if a `0`-graded secret index participates in dependent pattern matching that compiles to runtime tag dispatch before erasure, microarchitectural branch/cache leakage (`TVLA` Welch's $t$-test / `Revizor`) can observe it unless `Rig0` non-interference is verified down to machine assembly.
- **`V4` High-Water-Mark HIL Telemetry Replay and Programmer Mental-Model Validation:**
  - *Physical watermark falsification:* On SRAM-constrained microcontrollers, static `(net, peak)` certificates are validated via `S-TaLiRo`/evolutionary input search maximizing observed stack/heap watermarks measured via `0xDEADBEEF` SRAM stack painting and hardware `MPU` guard pages (`ModelPlex`-style runtime envelope traps) under real `HIL` interrupt bursts.
  - *Behavioral mental-model litmus tests (`SMoL`):* Because programmers frequently conflate Rust `&mut` (scoped uniqueness borrow `& 1 a`), Clean `*a` (full unique value), and Linear Haskell `%1 ->` (consumption linearity without uniqueness), empirical `SMoL`-style litmus programs testing aliasing + mutation + exception recovery validate whether diagnostic wording prevents misinterpreting linearity as thread/alias exclusivity.

## Boundaries

1. **Higher-order polynomial `AARA` under parallel composition (`not examined`):** Our exhaustive algebraic verification covers the first-order affine `(net, peak)` monoid $\mathcal{M}$ and tropical `(+, max)` `WCET`. Multivariate polynomial `AARA` (`RaML` degree $d \ge 2$ over nested lists/trees) introduces mixed binomial potential terms $\binom{|x_1| + |x_2|}{k}$ whose interaction with asynchronous parallel composition was `not examined`.
2. **Full mechanization of `GraD` + uniqueness + fractional borrowing simultaneously (`unknown`):** `GraD` (`DOI: 10.1145/3434331`) mechanizes graded dependent types over `{0, 1, omega}`-like semirings without uniqueness or fractional permissions, whereas `Granule` (`85a463f18914353669ff291677c47190fff43b23`) implements indexed GADTs, coeffects, `*A`, and `& f A` while explicitly forbidding dependent/GADT case elimination in `checkExpr[Case]` (`Checker.hs:777–779`: `when ixed (throw $ CaseOnIndexedType s guardTy)`, requiring top-level function equations instead). Soundness of full-spectrum dependent pattern matching combined with fractional mutable borrows `& f A` remains `unknown` across the examined sources.
3. **Semiring grade polymorphism over peak memory (`known not to apply`):** Any theorem or compiler pass parametric over an arbitrary `Semiring` (such as `Idris 2`'s `Algebra.Semiring` or `Granule`'s `ExactSemiring s` session primitives at `Primitives.hs:444–446`) is `known not to apply` to peak high-water-mark `SRAM` or slew resources, because $\max(s, a + b) \ne \max(s, a) + \max(s, b)$ refutes semiring distributivity unconditionally.
4. **Live `ghc` / `cabal` execution of `Granule` and `Idris 2` binaries (`not examined`):** Neither `ghc`, `cabal`, nor `idris2` is installed in the observation environment; behavioral claims about `Granule`, `Idris 2`, `pi-forall`, and `linear-base` are grounded in exact pinned source inspection (`Basis: source`) and peer-reviewed specifications (`Basis: normative`), while execution claims (`Basis: execution`) are strictly scoped to the standalone Python verification script over repository trees and finite algebraic models below.

## Evidence

### Pinned Repository Source Locations

- **`granule-project/granule` (`85a463f18914353669ff291677c47190fff43b23`):**
  - `frontend/src/Language/Granule/Syntax/Type.hs:40–69` — core `Type` GADT defining `Box Coeffect Type`, `Diamond Effect Type`, `Star Guarantee Type`, and `Borrow Permission Type`.
  - `frontend/src/Language/Granule/Checker/Types.hs:60–76, 172–239` — `relGrades` contravariant coeffect constraint reversal (`inj2 c'` vs. `inj1 c`) and structural equality/approximation on `Box`, `Star`, and `Borrow`.
  - `frontend/src/Language/Granule/Checker/Checker.hs:722–768, 777–779, 938–1003` — CBV `resourceAllocator` promotion guard (`UnpromotableError`), `CaseOnIndexedType` restriction, and `uniqueBind` (`clone`) elaboration with `1 <= r`, `Cloneable`, and existential `Name` renaming.
  - `frontend/src/Language/Granule/Checker/Primitives.hs:660–758, 835–836` — built-in types for `uniqueReturn`, `withBorrow`, `split`, `join`, `newFloatArray`, `writeFloatArray`, `deleteFloatArray`, and `unpromotables`.
  - `frontend/src/Language/Granule/Checker/Constraints.hs:39–111, 188–250` — `Data.SBV` Z3 constraint compilation, `isTrivial` fast path, and `SFrac` / `SNatX` symbolic grade encodings.
  - `examples/uniqueness.gr:3–44` — verified `redeem` / `derelict'` and commented-out rejected `derelict` / `redeem'` polarity witness programs.
- **`sweirich/pi-forall` (`75feff0f86f10d02c9e69999f0a112d0d289c948`):**
  - `full/src/Equal.hs:124–132` — `equateArg (Arg Irr t1) (Arg Irr t2) = return ()` (compile-time proof irrelevance during definitional equality).
  - `full/src/TypeCheck.hs:33–36, 53–59, 153–156` — `Env.checkStage`, `Demote Rel` context resurrection on `Irr` arguments, and `Env.withStage Irr` during `tcType`.
- **`idris-lang/Idris2` (`cf66cb4ccb8f0df7876fd07842f056f6222b9dce`):**
  - `src/Algebra/ZeroOneOmega.idr:9–74` & `src/Algebra/Semiring.idr:10–58` — `Rig0 | Rig1 | RigW` preorder (`Rig0 <= Rig1 <= RigW`, note ordering convention where `Rig0` is bottom and `LinearCheck.idr:170` rejects `rigb < rig` so `Rig0` fails when `Rig1` or `RigW` is demanded, and `Rig1` fails when `RigW` is demanded) and `branchZero` / `isErased`.
  - `src/Core/LinearCheck.idr:156–260` — syntax-directed QTT usage checker `lcheck`, `eraseLinear` across `RigW` lambdas, and `updateHoleUsage`.
  - `src/Core/Normalise/Convert.idr:324–395` — conversion checking confirming `NTCon`/`NDCon` compare all arguments regardless of `Rig0` multiplicity.
  - `src/TTImp/ProcessType.idr:172–181` & `src/Compiler/CompileExpr.idr:20–260` — `findErased`, `EraseArgs`, `NewTypeBy`, `eraseConArgs`, `mkDropSubst`, and `WorldVal` detagging guard.
- **`tweag/linear-base` (`bb5182a76c84eedcf78536c9ce24cb900882b2f3`):**
  - `src/Data/Unrestricted/Linear.hs:1–89`, `src/Data/Unrestricted/Linear/Internal/Ur.hs:34–105`, and `src/Data/Unrestricted/Linear/Internal/Movable.hs:43–200` — boxed GADT `Ur a`, `MP1 'Many`, and $O(N)$ deep-copy `Movable` instances.

### Primary Literature

- Robert Atkey, *"Syntax and Semantics of Quantitative Type Theory,"* LICS 2018, pp. 56–65 (`DOI: 10.1145/3209108.3209189`).
- Pritam Choudhury, Harley Eades III, Richard A. Eisenberg, and Stephanie Weirich, *"A Graded Dependent Type System with a Usage-Aware Semantics,"* Proc. ACM Program. Lang. 5, POPL, Article 50, 2021 (`DOI: 10.1145/3434331`).
- Daniel Marshall, Michael Vollmer, and Dominic Orchard, *"Linearity and Uniqueness: An Entente Cordiale,"* ESOP 2022, LNCS 13240, pp. 346–375 (`DOI: 10.1007/978-3-030-99336-8_13`).
- Martin Hofmann and Steffen Jost, *"Static Prediction of Heap Space Usage for First-Order Functional Programs,"* POPL 2003, pp. 185–197 (`DOI: 10.1145/604131.604148`).
- Jan Hoffmann, Ankush Das, and Shu-Chun Weng, *"Towards Automatic Resource Bound Analysis for OCaml,"* POPL 2017, pp. 123–137 (`DOI: 10.1145/3009837.3009842`).
- Brandon T. Shapiro and David I. Spivak, *"Duoidal Structures for Compositional Dependence,"* 2022, rev. v2 Jan 2025 (`arXiv:2210.01962v2`, `DOI: 10.48550/arXiv.2210.01962`).

### Standalone Executable Verification Output (`2026-11-19`)

Running the self-contained Python 3.13 probe below on Linux `x86_64` over the pinned repository trees and finite algebraic models (`|M| = 36` signed `(net, peak)` states, `36^4 = 1,679,616` 4-tuples) produced:

```text
Granule Checker (frontend/.../Checker/*.hs)             :   28 files,   11119 raw lines,    7573 non-blank/non-line-comment
Granule Frontend total (frontend/src/**/*.hs)           :   59 files,   21081 raw lines,   14758 non-blank/non-line-comment
pi-forall full typechecker (full/src/*.hs)              :    9 files,    4249 raw lines,    2787 non-blank/non-line-comment
Idris2 Core (src/Core/**/*.idr)                         :   64 files,   27333 raw lines,   22992 non-blank/non-line-comment
Idris2 Compiler/Erasure (src/Compiler/**/*.idr)         :   33 files,   11316 raw lines,    9224 non-blank/non-line-comment
linear-base Unrestricted (src/Data/Unrestricted/**/*.hs):    7 files,    1281 raw lines,     788 non-blank/non-line-comment
linear-base total (src/**/*.hs)                         :   87 files,   15610 raw lines,    9057 non-blank/non-line-comment

(net, peak) closure + shared unit (0,0) + seq assoc + par comm/assoc: True
Scalar max undercount witness: e1=(4, 4), e2=(0, 3) -> seq_np=(4, 7) (peak 7) vs max(4,3)=4
Semiring left-distributivity s;(a||b) vs (s;a)||(s;b) at s=5,a=1,b=1: (0, 5) != (0, 10)
WCET (seq=+, par=max) lax interchange (a;b)||(c;d) <= (a||c);(b||d) universal: True; strict witness (5,0,0,5): 5 < 10
Zero-net Peak SRAM (seq=max, par=+): lax <= holds? False; colax (a||c);(b||d) <= (a;b)||(c;d) holds? True
General signed (net, peak) colax rhs.peak <= lhs.peak universal? True
General signed (net, peak) lax lhs.peak <= rhs.peak universal? False
```

## Revalidation

To revalidate the algebraic findings unconditionally or re-check upstream implementation invariants after bumping any repository pin:

1. **Standalone Algebraic & Credit-Invariant Probe (`< 1 s`, Python 3.10+ stdlib only):**
   ```bash
   python3 - <<'PY'
   import itertools
   valid = lambda n, p: p >= 0 and p >= n
   seq_np = lambda x, y: (x[0] + y[0], max(x[1], x[0] + y[1]))
   par_np = lambda x, y: (x[0] + y[0], x[1] + y[1])
   M = [(n, p) for n in range(-2, 3) for p in range(0, 5) if valid(n, p)]
   assert seq_np((4, 4), (0, 3)) == (4, 7)
   assert seq_np((0, 5), par_np((0, 1), (0, 1))) != par_np(seq_np((0, 5), (0, 1)), seq_np((0, 5), (0, 1)))
   for a, b, c, d in itertools.product(M, repeat=4):
       lhs, rhs = par_np(seq_np(a, b), seq_np(c, d)), seq_np(par_np(a, c), par_np(b, d))
       assert lhs[0] == rhs[0] and rhs[1] <= lhs[1]
   eff = lambda t, d: max(0, t - d)
   assert eff(0 + 10, 5 + 0) < eff(10, 0)  # non-monotone without d_i <= t_i
   assert all(eff(t1+t2, d1+d2) == eff(t1, d1) + eff(t2, d2)
              for t1 in range(4) for d1 in range(t1+1) for t2 in range(4) for d2 in range(t2+1))
   print("All duoidal, AARA (net, peak), and leaf-credit invariants verified.")
   PY
   ```
2. **Upstream Semantic Diff Anchors:**
   - In `Idris 2`, diff `src/Core/Normalise/Convert.idr` (`NTCon`/`NDCon` `allConv`) and `src/Compiler/CompileExpr.idr` (`eraseConArgs`, `getNewType` `WorldVal` check) to confirm `Rig0` remains conversion-relevant while erased at runtime.
   - In `Granule`, diff `frontend/src/Language/Granule/Checker/Checker.hs` (`checkExpr[Box]` `resourceAllocator` guard and `synthExpr[Clone]` `uniqueBind`) and `Checker/Types.hs` (`relGrades` argument order) to check CBV promotion safety and uniqueness-versus-linearity polarity.
   - In `linear-base`, check whether `Ur` in `src/Data/Unrestricted/Linear/Internal/Ur.hs` remains a `data` declaration rather than `newtype`.
