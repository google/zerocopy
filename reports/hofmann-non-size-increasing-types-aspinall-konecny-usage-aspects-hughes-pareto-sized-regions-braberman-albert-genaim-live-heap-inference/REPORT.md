# Space bounds under sharing: non-size-increasing types, usage aspects, potential splitting, and peak-live-heap inference

## Summary

- **Every system examined handles a second reference to heap data in one of five ways:** (1) **forbid** it (LFPL: only heap-free variables may be contracted); (2) **order** it (usage aspects: read-only uses may precede one destructive use, unless a retained read-only result aliases the argument); (3) **split** it (amortized analyses: shared potential satisfies `q = q1 + q2`, all `≥ 0`); (4) **charge** it (Niu–Hoffmann: sharing typed as copying, one extra unit per shared cell); or (5) **compute** it (live-heap analyses use reachability, escape, liveness, or reference counts).
- **ReSyn has a concrete splitting rule.** At `tjknoth/resyn@54ff304c635f26b4b498b82be267923a65e0662d`, `src/Synquid/Solver/Resource.hs:104-109` compiles each `SharedForm env f fl fr` constraint to `f = fl + fr` conjoined with `f ≥ 0, fl ≥ 0, fr ≥ 0`. `shareContext` (`src/Synquid/Synthesis/Util.hs:435-452`) emits such constraints wherever a context is used twice: for `if` and `match` (`TypeChecker.hs:181`, `:205`) and for application (`:315`).
- **Space theorems have different shapes.** LFPL proves *no heap growth*: the result's region is a subset of the union of the input regions, so the heap needs no `malloc`. Usage aspects strengthen that theorem with "in-place updates touch only aspect-1 regions." Amortized systems prove *high-water mark ≤ initial potential*. Peak-live-heap analyses give symbolic upper bounds under an assumed collector: scope-based, reachability, liveness/ideal, or explicit `dispose`.
- **A bound composes only if the per-function interface carries what composition needs.** For a non-accumulative resource the minimum is two numbers: a peak bound and a residual (escaped) bound. Albert–Genaim–Gómez-Zamalloa use the rule `peak(m1; m2) = max(peak(m1), escaped(m1) + peak(m2))`. For potential-based typing the interface needs **resource polymorphism**. RaML-style monomorphic annotations force reanalysis at each call site. Jost et al. 2010 store constraint sets in function types. ReSyn gets it from type-variable instantiation. Closures may capture only zero potential in Jost et al. 2010 and in Liquid Resource Types.
- **Reported precision is good but tested on small programs.** Chin et al. 2008 heap estimates equal the measured watermarks on all 11 programs. Jost et al. 2010 heap bounds are exact; time bounds exceed measurement by at most 13–30%, depending on the benchmark. Niu–Hoffmann bounds are exact for 7 of 10 functions; quicksort's bound is 0 above the input. In ISMM 2010, reachability-based bounds equal the measured minimum for 3 of 7 methods. The paper itself describes them as "very close to RR in most of them, except for the first two benchmarks".
- **Toy probe (toy model, not any of these systems).** In-place execution of a program that uses one diamond twice yields a cyclic list. A usage-aspect `let` check accepts `cons(d,sumlist(l),reverse(l))` and rejects `cons(d,nth_tail(2,l),cons(d',reverse(l),nil))`, whose in-place execution is wrong. For `appTwice`, total allocation is `2m` but peak live heap above the input is `m` (minimal potentials 2 vs 1 per element).

## Applicability

The report compares published *type systems* and *static analyses* for heap-space bounds on one question: how each states and establishes a bound when data are shared or aliased, and whether that bound composes across calls. The papers are compared, not combined. ReSyn is the only implementation inspected at source level, read through the Liquid Resource Types and Resource-Guided Synthesis papers, which define its rules.

Exact observations:

- **ReSyn source** at the pinned revision. On the observation date this was the repository's `HEAD`, a commit dated 2020-12-09 with message "add a license". Read: `README.md`, `resyn.cabal`, `stack.yaml`, and 12 modules under `src/Synquid/` (cited in Evidence). ReSyn was **not built or run**.
- **Papers.** Full text of the copies listed under **Evidence** (works table). Some differ from the DOI version: ESOP 2000 was read in the author's full version (2000-11-22); ISMM 2009 only as the authors' slides; the ISMM 2010 copy is anonymized ("the system name is withheld"); FP² as report MSR-TR-2023-19. Quoted numbers may differ from archival versions.
- **Works not read directly.** Hughes–Pareto 1999, Hofmann–Jost 2003, Dal Lago–Hofmann 2011, and the Information and Computation 2003 journal version were not read, so they are not listed as subjects. Statements about them are labelled `documentation (secondary)` and come from the cited later papers. The JFP 2008 paper was read as its abstract only.

Scope: strict first- or second-order functional languages (LFPL, aspects, AARA/RaML, Liquid Resource Types); Java bytecode (COSTA, the ISMM 2009/2010 tool; Braberman et al.); assembly-level C via CIL (Chin et al.); a first-order functional language (Unnikrishnan et al.). Concurrency and laziness are outside all of them; general higher-order functions only in Jost et al. 2010.

## Findings

### F1. Synthesis matrix: how each system treats a second reference

| System | What may be shared | What may be destroyed or reused | Accounting of sharing | Bound form | Per-function interface composes? | Soundness basis |
|---|---|---|---|---|---|---|
| LFPL (Hofmann 1999/2000) | Heap-free values (`Contr` only on heap-free types); one variable in both components of an additive product `×` | Every match on `L(A)`/`T(A)` is destructive and yields a `◇` | **Forbid**: `◇` and heap-typed variables are affine | Result region ⊆ union of input regions (zero growth); non-size-increasing denotations | Yes: ordinary linear types; zero growth is closed under composition | normative proof (set-theoretic semantics plus a semi-formal C semantics) |
| Usage aspects (Aspinall–Hofmann 2002; Aspinall–Hofmann–Konečný 2008) | Aspect 2 (read-only, may alias the result) and aspect 3 (read-only, does not alias the result) | Aspect 1 (destructive), at most once, last | **Order**: in `let`, a variable may be read in `e1` and destroyed in `e2` only if `e1`'s result does not alias it (aspect 3) | Same zero-growth theorem plus "only aspect-1 regions are updated" | Yes: aspect-annotated signatures; principal types (JFP abstract) | normative proof (abstract machine) |
| AARA (Hofmann–Jost 2003; Jost et al. 2010; RaML) | Any value via `share` | Matched cells may return potential (heap metric with deallocation) | **Split**: `Φ(A) = Φ(B) + Φ(C)` | Linear (original) or polynomial potentials; LP-inferred constants | Jost et al. 2010: yes, via constraint sets in arrow types; RaML: resource-monomorphic per LP solution | normative proof plus execution (measured on a microcontroller platform) |
| Niu–Hoffmann 2018 (AARA with ideal collection) | Any value via `share` | Destructive pattern match models collection, even for shared data | **Charge**: split plus 1 unit per shared cell (`L:ShareCopy`) | Polynomial (RaML) | Type-based; peak `let` composition by cost-free typing listed as future work | normative proof via a copying semantics plus execution |
| ReSyn / Liquid Resource Types | Scalars via context sharing; closures only with zero potential | n/a (cost via `tick`) | **Split**: `f = fl + fr`, all `≥ 0` (source F4.4) | Value-dependent refinement bounds; polynomial and exponential via annotated datatypes | Yes: polymorphism yields resource polymorphism | normative proof (progress and preservation) |
| Atkey 2011 (separation logic) | Heap only under separation (shared-heap variant discussed) | Imperative update | **Separate**: `∗` splits heap and resources | Linear (automation); polynomial lists in the logic | Procedure pre/post specs | Coq-formalized soundness |
| Hughes–Pareto 1999 | Region-based | Regions freed when all their objects are dead | Sized types with regions | Heap and stack bounds (type checking) | Type-checked signatures; no inference | documentation (secondary) |
| Unnikrishnan–Stoller–Liu 2003 | Any (functional) | GC; liveness via reference counts on partially known structures | **Compute** (whole-program abstract interpretation) | Concrete bound per input size; closed forms fitted afterwards | No: whole-program bound function | execution (tight on examples) |
| Chin et al. 2008 | Unique data only for `dispose` insertion | Explicit `dispose` | **Compute** (Presburger fixpoints per method) | Linear (Presburger) guarded expressions, per object type | Yes: per-method frame, stack, net-heap, and watermark annotations | execution (estimate vs measured) |
| Braberman et al. 2008 | Java objects | Scoped regions tied to method lifetimes | Escape-based regions | Parametric polynomial (Bernstein basis over polyhedra) | Per method, over transitive callees (abstract) | documentation (abstract) |
| Albert–Genaim–Gómez-Zamalloa 2009 | Java objects | Scope-based GC at method return | Escape analysis gives `collectable(m)` | Cost relations with `max` | Yes: two summaries per method (`peak`, `escaped`) | documentation (slides) |
| Albert–Genaim–Gómez-Zamalloa 2010 | Java objects | Parametric object lifetime (reachability or liveness) | Points-to/reachability or liveness at program points | Cost relations, solved symbolically | Program-point equations; whole-program lifetime analyses | normative proof (Theorem) plus execution |
| FP² / Koka `fip` (2023) | Borrowed parameters `^x` (no destructive match, not returned) | Owned linear values; `match!` yields reuse credit `◇k` | **Forbid/borrow**: credits never split or merged | `fip`: no allocation, constant stack; `fbip`: only deallocation; `fip(n)`: ≤ n allocations | Yes: per-function keywords | normative proof (store semantics) |

Basis: derived from the per-system findings below.

### F2. Non-size-increasing typing (LFPL)

**Resource type and rules.** Basis: normative (LICS 1999 text; full ESOP 2000 version).

- LICS 1999 types the binary successors and list cons as `S0, S1 : ◇ ⊸ N ⊸ N` and `cons_A : ◇ ⊸ A ⊸ L(A) ⊸ L(A)`. `◇` has interpretation `{∗}` and size `s_◇(∗) = 1`, so the constructors become size-preserving.
- Size measures: `s_{A⊗B}(u,v) = s_A(u) + s_B(v)`, `s_{A×B}(u,v) = max(s_A(u), s_B(v))`, `s_{A⊸B}(f) = min{c | ∀a. s_B(f a) ≤ c + s_A(a)}`.
- Proposition 3.1: if operators map size-0 arguments to size-0 results, then `s_A([[e]]η) ≤ Σ_{x∈dom Γ} s_{Γ(x)}(η(x))`. This is the non-size-increasing property.
- **Sharing rule:** `T-PROD-I` lets one variable occur in both components of a cartesian product (`λx.⟨x,x⟩ : A ⊸ A×A` is typable, `λx.x⊗x` is not). That additive sharing is paid for by the `max` in `s_{A×B}`.
- In the ESOP 2000 language, `Contr` applies only to heap-free types. "Application of function symbols … is linear in the sense that several operands must in general not share common free variables."

**Excluded programs (all because of sharing).** Basis: normative.

| Program | Why rejected | Consequence if executed in place |
|---|---|---|
| `twice` (two conses from one matched cell) | `◇` value `d` used twice | "returns a circular list" (ESOP 2000 text) |
| `insert` with last line `cons(d,l.hd,insert(d,a,l.tl))` | `d` used twice | same class of overwrite |
| `f(0)=1, f(x)=4f(x/2)` via `h = λc:◇.λz.S0(c)(S0(c)(z))` | `c:◇` used twice (LICS 1999) | quadratic growth would be definable |
| Guard and branches sharing non-heap-free variables | Base `If` rule is multiplicative | Additive `If-Add` is sound only on a linear-space TM with stack, by saving and restoring heap on the stack; the C translation does not carry over |

**Space theorem.** Theorem 4.3 of the full ESOP 2000 version assumes inputs with pairwise disjoint regions `R_x`. It concludes that the translated C code either diverges or yields a value whose region `R ⊆ ⋃ R_x`, leaving the heap outside `⋃ R_x` unchanged. Hence the translation is `malloc()`-free. Additional space must be passed in, e.g. input type `L(◇⊗A)`. Expressivity (Theorems 5.1–5.3): tail-recursive programs capture linear space, and full LFPL captures `ETIME` (via Cook's theorem) for non-size-increasing `f : N → N`. Basis: normative.

**Soundness models.** Basis: normative for LICS 1999; documentation (secondary) for Dal Lago–Hofmann.

- The PTIME result (LICS 1999, Corollary 5.14) uses realizability over a BCK-algebra subalgebra `C0` with a length measure, not the size function.
- Dal Lago–Hofmann 2011 generalize this to resource monoids and length spaces, proving soundness for LFPL, Elementary Affine Logic, and Soft Affine Logic (per a 2021 MSCS paper on the framework; the 2011 paper was not read).

**Measured performance (as reported).** Basis: documentation (ESOP 2000 full version, §7). The benchmark was breadth-first traversal of full binary trees of depths 12–15. SML/NJ 110.0.6 and OCaml 3.00 "would run slightly faster than the generated C-code [but] use about 10 times as much space". Native `ocamlopt` code "ran faster and used even less space than the generated C-code". No absolute times are given.

### F3. Usage aspects (Aspinall–Hofmann 2002; JFP 2008 extension)

**Aspects.** Basis: normative (ESOP 2002).

- 1 = modifying use (`l` in `reverse(l)`);
- 2 = non-modifying use whose result may alias the argument (`m` in `append(l,m)`);
- 3 = non-modifying use that does not alias the result (`l` in `sumlist(l)`).

The order is `1 < 2 < 3` by permissiveness. Signatures: `reverse : L^1 → L`, `sumlist : L^3 → N`, `nth_tail : L^2 × N^3 → L`, `append : L^1 × L^2 → L`, `cons_A : ◇^1, A^2, L(A)^2 → L(A)`, `fst : (A×B)^2 → A`. Heap-free types always carry aspect 3.

**Rules that govern sharing.** Basis: normative (ESOP 2002, Fig. 3 and prose).

- `var` gives aspect 2. `raise` promotes aspect 2 to 3 when the result type is heap-free. `drop` weakens to a more destructive aspect.
- **`let x = e1 in e2`** splits the context into `Γ` (only in `e1`), `Θ` (only in `e2`), and common variables `Δ1`/`Δ2`. The conclusion `Γ^i, Θ, Δ1^i ∧ Δ2` commits aspect-2 variables of `e1` to `x`'s aspect `i` in `e2`. Here `∧` takes the worst aspect.
- Side condition, as the authors state it: "`Δ1[z] = 1` is not allowed …; `Δ1[z] = 3` is always allowed …; and `Δ1[z] = 2` is allowed provided neither `i = 1` nor `Δ2[z] = 1`." A derived rule is contraction for aspect-3 variables.
- **×-pair:** shared variables between components need aspects `≥ 2` in both, so no shared memory is destroyed while building the pair.
- **Destructors** (`list-elim`, `pair-elim`) propagate the minimum aspect of the bound pieces. Destroying half a pair destroys the pair.

**Soundness statement (Theorem 1, ESOP 2002).** Preconditions on aliasing: the stack meaningfully represents the valuation, *and* any two distinct variables whose regions overlap both have aspect `≥ 2`. That is, aspect-1 variables are disjoint from everything. The conclusions are:

(1) `R_C(v,σ') ⊆ R_Γ(S,σ)` (no new memory); (2) locations outside `R_Γ` unchanged; (3) regions of aspect-`≥2` variables unchanged; (4) machine result = set-theoretic result; (5) under stronger no-internal-sharing assumptions, the result is safe to update and disjoint from every aspect-3 region. Basis: normative.

**Accepted and rejected examples.** Basis: normative (ESOP 2002, §1.1–1.2).

| Expression | Verdict | Cause |
|---|---|---|
| `cons(d, sumlist(l), reverse(l))` | accepted | `sumlist` is aspect 3, so its result does not alias `l` |
| `cons(d, nth_tail(2,l), nil)` | accepted | no later destruction |
| `cons(d, nth_tail(2,l), cons(d', reverse(l), nil))` | rejected | **sharing**: `nth_tail`'s result aliases `l` (aspect 2), then `l` is destroyed; functional value `[[3],[3,2,1]]` |
| `let x=append(u,w) and y=append(v,w) in e`; `let u=node(d,a,t,t) in e` | motivating examples the authors "would like to allow" if `e` does not modify both parts | DAG sharing |

The paper adds `sharednode_A : ◇^1, (A × ST(A) × ST(A))^2 → ST(A)` for trees with unrestricted internal sharing. The `◇` argument can never be shared, because its region is overwritten. `new : → ◇` and `dispose : ◇^1 → N` are noted as extensions that break heap-boundedness. Basis: normative.

**JFP 2008.** The abstract describes an extended version "with detailed proofs and type reconstruction algorithm" with "principal types and feasible type reconstruction". Basis: documentation (abstract only).

### F4. Splitting potential (amortized analyses) and composition over calls

**F4.1 Splitting rule.** Basis: normative (Jost et al. 2010, Lemma 5.7); documentation (secondary) for Hofmann–Jost 2003.

- Jost et al. 2010 write sharing as `.(A | B, C)`. Lemma 5.7: if the sharing constraints hold, then `Φ(ℓ:A) = Φ(ℓ:B) + Φ(ℓ:C)`. "The SHARE rule does not increase the total available potential." Self-sharing `A = B = C` forces `Φ(ℓ:A) = 0`.
- Lemma 5.6: each duplicate's type is a subtype of the original.
- Atkey 2011 describes the Hofmann–Jost lineage as "a linear type system … used to ensure that data structures carrying resources are not duplicated". He notes that both his automated search and the original Hofmann–Jost work infer only bounds linear in list sizes.

**F4.2 Closures.** Function bodies may capture only zero-potential free variables: Jost et al. 2010 Lemma 5.8 requires `.(D | D, D)` for captured types; Liquid Resource Types' `T-Abs`/`T-Fix` require `⊢ Γ ⋎ Γ | Γ`, relaxed by `T-Abs-Lin` for functions applied at most `m` times. Basis: normative.

**F4.3 Composition over calls.** Basis: documentation (PLDI 2019, ICFP 2020; Jost et al. 2010).

- **RaML (resource-monomorphic per LP solution):** "RaML's monomorphic type system is unable to assign a single general type to `append`, which can be used at both call sites. So the function has be [sic] reanalyzed at every (monomorphic) call site."
- **Re2/ReSyn:** a type variable instantiated at two potentials (`Int` and `Int¹`) gives one signature for both uses. README: "polymorphism implies resource polymorphism… Instantiating `List {a| |1}` with `a |-> {Int| |2}` yields `List {Int| |3}`."
- **Jost et al. 2010:** arrow types `∀r∈ψ. A –p/p'→ C` carry constraint sets `ψ`.

ReSyn's bound inference (`--infer`) "only admits the inference of constant resource bounds" (README).

**F4.4 ReSyn source, pinned revision.** Basis: source.

- `src/Synquid/Program.hs:630-631` declare the constraint forms `SharedEnv !Environment !Environment !Environment` and `SharedForm !Environment !Formula !Formula !Formula`.
- `src/Synquid/Solver/Resource.hs:104-109`, the SMT meaning of sharing:

  ```haskell
  SharedForm env f fl fr -> do
    let sharingFml = f |=| (fl |+| fr)
    let wf = conjunction [f |>=| fzero, fl |>=| fzero, fr |>=| fzero]
  ```

- `Resource.hs:411-433` (`partitionType`/`partitionBase`) split structurally: a nonzero top-level annotation yields `SharedForm env' f fl fr`; datatype arguments recurse; integer-sorted abstract potentials split; type-variable multiplicities split only under `checkMultiplicities` (line 432).
- `Util.hs:435-452` (`shareContext`) re-annotates every non-ghost scalar on both sides, splits free and conditional free potential (`shareFreePotential`, 454-464, `error` on `Ite`-shaped free potential), and records `SharedEnv env envl envr`. Only arity-0 symbols are re-annotated (line 547); function-typed symbols are added without potential (line 226).
- **Use sites.** `TypeChecker.hs:181` (`if` with hole guard), `:194-195` (`if`), `:205-208` (`match`: scrutinee vs cases), `:315` (`PApp`: `shareAndExtractFP` splits between function and argument).
- **Variable use is affine in potential.** `Explorer.hs:453-455` remove the symbol and re-add it with `schemaMultiply fzero sch`. A referenced variable keeps its refinement but loses its potential to the use site.

The LRT paper's rule `Share-Pot` (`Γ,ν:R ⊨ ϕ = ϕ1 + ϕ2`) matches this code.

**F4.5 Charging sharing as copying under collection (Niu–Hoffmann).** Basis: normative plus documentation of reported measurements.

- The cost model is a perfect collector, with an explicit construct `share x as x1,x2 in e`.
- `L:MatLD` (destructive match returns potential) "is not sound for programs with aliasing of data". `L:ShareCopy` fixes it: split as usual and "pay an 'overhead' of 1 for every cons node". Soundness is proved against a copying semantics, then the collecting semantics is shown to use no more memory.
- For `appTwice l = share l as l1,l2 in (append(l1,[]), append(l2,[]))`: the allocation metric needs `p ≥ r+s+2`; the GC metric needs `p ≥ r+s+1`.
- Table 2 (RaML heap metric vs GC metric; analysis time in seconds):

  | Function | Heap-metric bound | Time | GC-metric bound | Time | Exact |
  |---|---|---|---|---|---|
  | quicksort | `1+3.5M+1.5M²` | 0.52 | `0` | 0.48 | `0` |
  | bfs | `5+10M` | 4.15 | `4` | 1.62 | `4` |
  | map it (shares its input) | `2+2LM+4M` | 1.58 | `M+1` | 1.57 | `M+1` |
  | pairs | `1+M²` | 0.60 | `0.5M+0.5M²` | 0.64 | `0.5M²−1.5M+2` |

  Mergesort is not tight (no logarithmic bounds), and closures are accounted only by allocation.
- Composing peaks across `let` with a cost-free metric is explicitly future work.

**F4.6 Separation logic (Atkey 2011).** Basis: normative (paper text).

- The logic embeds affine BI resource assertions in separation logic. `φ1 ∗ φ2` "separates both heaps and consumable resources".
- Separating resources while sharing the heap is discussed as a variant, motivated by a merge-sort helper.
- Formalized in Coq with an extracted certified VC generator; examples include in-place reversal of lists with cyclic tails.

**F4.7 Sized types with regions (Hughes–Pareto 1999).** Basis: documentation (secondary).

- Chin et al. 2008 describe "a type-checking system on space usage estimation for a first-order functional language, extended with regions… no inference mechanism… each region is only deleted when all objects in its region are dead".
- Campbell's depth paper states that Hughes and Pareto "used their sized-types work to certify heap and stack space bounds in a first-order 'embedded ML' language … but do not provide any inference".

How Hughes–Pareto handles a value referenced twice was **not determined** (see Boundaries).

### F5. Static peak-live-heap inference with aliasing and collection

| Analysis | Program model | Collection, escape, and aliasing treatment | Bound form | Composition | Reported precision (quoted) |
|---|---|---|---|---|---|
| Unnikrishnan–Stoller–Liu 2003 | First-order functional, source-level transform | Reference counts on partially known structures (`uk` unknowns); max over branches; live heap = minimum heap under ideal GC | Numbers per input size; closed forms fitted afterwards ("using Matlab to fit polynomials") | Whole program; bound functions may diverge | "accurate results (i.e., tight bounds) for all these examples"; selection sort `n(n+3)/2` cells vs tail-recursive `2n`; 600-line calendar benchmark in "only a few seconds" |
| Braberman et al. 2008 | Java-like | Scoped memory: regions bound to method lifetimes | Parametric polynomial; maximization over polyhedra via Bernstein basis | Per method over transitively called methods | not examined (abstract states "several benchmarks") |
| Chin et al. 2008 | Assembly-level (C via CIL) | Explicit `dispose`, inserted with an alias/uniqueness type system that "cannot handle data structures with shared nodes" | Presburger guarded expressions; counts per object type; separate net usage and high watermark | Modular: per-method `φpr; F; φpo; S; Hpo; Mpo` over call-graph SCCs | Heap estimate = execution on 11/11 programs (e.g. Sparse Mult. 160800/160800). Stack: FFT 856 vs 846; Ackermann not captured. Heap inference 0.26–17.74 s (Pentium 2.8 GHz) |
| Albert–Genaim–Gómez-Zamalloa 2009 | Java bytecode, COSTA | Scope-based GC: objects created during a call that do not escape are collectable at return | `peak(m1;m2) = max(peak(m1), escaped(m1)+peak(m2))`; `escaped(p) = total(p)[size(c)↦0 for c ∈ collectable(p)]` | Two summaries per method | Example: `total(m)=2ⁿ·(total(f)+size(Tree))` vs `peak(m)=2ⁿ·size(Tree)+peak(f)`; "successfully analyzed the JOlden benchmark suite" |
| Albert–Genaim–Gómez-Zamalloa 2010 | Java bytecode, COSTA | Parametric object lifetime: reachability (points-to) or heap liveness; program-point equations | Recurrence relations; partial evaluation before generation | Needs whole-program lifetime analysis; context-insensitive points-to loses precision | JOlden: `UT ≥ US ≥ UR ≥ UL` always; measured minimum `RR` from a JVMTI-based tool forcing GC before each allocation (per-method counts in F7). E.g. `bisort.Value.inOrder`: total exponential, scope `2·nat(A−1)+2`, `UR` = `RR` = 2 |

Basis: documentation (paper copies and slides as listed).

**Worked comparison of collector assumptions** (ISMM 2010, Fig. 1). The paper gives `T = s(A)+s(B)+s(C)+s(D)+s(E)`, `S = s(A)+s(B)+max(s(C)+s(E), s(E)+s(D))`, `R = max(s(A)+s(B)+s(C), s(A)+s(C)+s(E), s(E)+s(D))`, and `L = max(s(A)+s(B)+s(C), s(E), s(D))`. With every `s(·) = 1`: `T = 5`, `S = 1+1+max(2,2) = 4`, `R = max(3,3,2) = 3`, `L = max(3,1,1) = 3`. Basis: derived (arithmetic on the quoted formulas).

**Consequences for composition under aliasing.** Basis: derived.

- Two quantities per callee make peak bounds composable under scope-based or escape-based collection: the peak, and the amount still live at return.
- Under reachability or liveness collection, the residual depends on caller-side aliasing. ISMM 2010 therefore works at program-point granularity with whole-program lifetime facts rather than per-method summaries.
- Type systems avoid that dependency by construction. LFPL forbids sharing. Aspects order destruction after reads. AARA bakes the sharing split into the caller's typing.

### F6. Toy probe (support/sharing_toy.py)

Basis: execution (toy model of the cited rules, not any of the cited systems).

Command: `python3 support/sharing_toy.py`, run on an x86_64 Linux workstation with Python 3.13.15. Output, verbatim (`support/sharing_toy.out.txt`):

```text
reverse [1..5] -> [5, 4, 3, 2, 1] | cells before/after: 5 5
twice [1,2]: functional [0,0,0,0]; in-place reads [0] then revisits a cell (cyclic)
cons(d,sumlist(l),reverse(l)): functional (6,[3,2,1]); in-place (6, [3, 2, 1])
cons(d,nth_tail(2,l),cons(d',reverse(l),nil)): functional [[3],[3,2,1]]; in-place [[3, 2, 1], [3, 2, 1]]
aspect check: sumlist-then-reverse accepted = True | nth_tail-then-reverse accepted = False
 m  total_alloc  peak_live_minus_input
   1           2                      1
  10          20                     10
 100         200                    100
 500        1000                    500
minimal per-element potential p: {'allocation metric': 2, 'GC metric + copy-on-share': 1}
```

In the toy, a matched cell's location is the `◇` (as in the ESOP 2002 machine's `xd ↦ l`). The wrong value `[[3,2,1],[3,2,1]]` is the toy's result under that representation; the paper states only the correct value and that the in-place version differs. The reference-counted heap frees a cell at count 0 (an ideal collector for acyclic data); `peak_live_minus_input = m` agrees with Niu–Hoffmann's `appTwice` overhead and `total_alloc = 2m` with the allocation-metric bound.

### F7. Performance and resource footprint (L1–L6)

| Level | LFPL / aspects | AARA (Jost 2010; RaML; Niu–Hoffmann) | ReSyn / LRT | Live-heap analyses | Toy probe |
|---|---|---|---|---|---|
| L1 authoring velocity | not measured | not measured | not measured | not measured | not measured |
| L2 toolchain build | not measured | not measured | not measured (requires stack and Z3 4.8.8 per README; not built) | not measured | none (standard library only) |
| L3 analysis latency | Type checking "decidable in linear time" (ESOP 2000 claim; not measured) | Niu–Hoffmann 0.04–4.15 s per function; constraints 515–30703 | LRT verification "under a second" (benchmarks 1-9), "up to six seconds" (10-12). ReSyn synthesis median ≈2.5× Synquid on 43 benchmarks (e.g. `drop` 20.4 s vs 0.3 s) | Chin heap inference 0.26–17.74 s; USL calendar "a few seconds"; COSTA times not examined | not measured |
| L4 generated code | Generated C slightly slower than SML/NJ and OCaml with ≈1/10 of their space; slower than `ocamlopt` (qualitative, ESOP 2000) | Jost 2010 time bounds 18–26%, ≤13%, ≤22%, ≤30% above measured cost | n/a | n/a | n/a |
| L5 certificate checking | not measured | Type derivations proposed as certificates (Niu–Hoffmann); not measured | not measured | Atkey: Coq-extracted VC generator; speed not measured | n/a |
| L6 memory and footprint | Zero heap growth (theorem); analyzer RSS not measured | Jost 2010 heap bounds exact; Niu–Hoffmann exact for 7/10 functions | analyzer RSS not measured | Chin heap estimate = measured on 11/11; ISMM 2010 `UR` = `RR` on 3/7 methods; analyzer RSS not measured | `appTwice`: total `2m`, peak above input `m` (toy) |

Basis: documentation (quoted), except the toy cells (execution, toy) and the counts 11/11, 7/10, and 3/7, which are derived by counting rows of the quoted tables.

- **Chin Fig. 7:** heap Estimation = Execution in every row. **Niu–Hoffmann Table 2:** GC bound = exact for quicksort, ocamlsort, selection sort, eratosthenes, dfs, bfs, map it; not for mergesort, transpose, pairs.
- **ISMM 2010 Table 1:** `UR` = `RR` for `em3d.BiGraph.toString` (4 = 4), `voronoi.Vertex.print` (2 = 2), and `bisort.Value.inOrder` (2 = 2). It differs for `mst.MST.computeMST` (`4+2·nat(A−1)` vs 2), `bh.Tree.vp` (`28·nat(A)+8` vs `12·A+24`), `bh.Body.hackGravity` (21 vs 12), and `bh.MathVector.toString` (10 vs 2).

### F8. Comprehensibility (C1) and conceptual simplicity (C2)

**C1. Reasoning locality and diagnostic legibility.** Basis: derived from the rule forms above.

- **LFPL:** one extra concept (`◇`), a purely local check (count `◇` uses), and a diagnostic naming the duplicated variable; the burden is moving `◇`s by hand (Hofmann: inference "might be helpful").
- **Aspects:** three ordered aspects plus a `let` condition depending on evaluation order and the *result's* aliasing (`i`); the reason for a rejection may lie in a callee's aspect-2 signature (non-local).
- **AARA/ReSyn:** rational annotations and LP/SMT feasibility; a failure is an infeasible constraint system that locates no program point. ReSyn's README warns the incremental CEGIS solver "currently has some bugs with constraints involving abstract potentials".
- **Live-heap analyses:** symbolic bounds whose imprecision traces only to points-to or liveness precision (ISMM 2010: context-insensitive points-to).

**C2. One invariant behind several mechanisms.** Basis: derived. All type-based systems enforce one invariant: *the resource accounted for at a contraction point is not counted twice.*

- LFPL picks the trivial split (forbid).
- Aspects add a temporal ordering, read-before-destroy, which no additive split expresses.
- AARA picks additive splitting in a commutative monoid. Niu–Hoffmann add a per-cell surcharge to model copying.
- A minimal common abstraction is a sharing relation `A ⋎ (A1, A2)` over a resource algebra, plus an optional evaluation-order relation for destructive uses. In this abstraction, LFPL is the relation restricted to heap-free `A`, AARA is the additive instance, and aspects are the ordered instance.

ReSyn carries this one invariant in four places (variable annotations, datatype abstract potentials, free potential, conditional free potential), each split by its own code path (`partitionType`, `shareFreePotential`, `shareCondFP`). The analyses separate a realization choice, the collector policy (scope / reachability / liveness), from the core invariant (`peak` vs `escaped`); ISMM 2010 makes that policy a parameter.

### F9. Validation of the systems (V1–V4)

- **V1 (specification adequacy).** Bounds are compared with executions: Chin 2008 (watermark vs execution), Jost 2010 (measured micro-controller costs), ISMM 2010 (forced-GC measurement), Niu–Hoffmann (exact high-water mark "derived by hand and verified by running the cost semantics"), USL 2003 (bound vs space functions on worst-case inputs). No spec-mutation or property-based adequacy testing is reported. Basis: documentation.
- **V2 (checker soundness testing).** No differential or fuzz testing of any checker or solver is reported. Atkey's VC generator is extracted from a Coq proof. ReSyn's README documents known CEGIS bugs. Basis: documentation.
- **V3 (concurrency, crashes, hardware).** Known not to apply to the sequential calculi examined; not examined for COSTA or the C front end.
- **V4 (field and human validation).** No empirical study of programmer comprehension is reported. Jost 2010 takes costs from "a simple micro-controller platform that is used in safety-critical automotive applications". Basis: documentation.

## Boundaries

- **Not examined (primary text):** Hughes–Pareto 1999 (its rule for a value referenced twice is unknown); Hofmann–Jost 2003 (exact `share` rule, benchmarks); Dal Lago–Hofmann 2011; the Information and Computation 2003 journal version; JFP 2008 full text (proofs, reconstruction, further examples); Konečný TLCA 2003, "Functional in-place update with layered datatype sharing" (DOI 10.1007/3-540-44904-3_14); Hoffmann–Aehlig–Hofmann multivariate analysis (POPL 2011, DOI 10.1145/1926385.1926427; TOPLAS 2012, DOI 10.1145/2362389.2362393), so how multivariate potentials split under sharing is not covered; Braberman et al. 2008 beyond the abstract (benchmarks, precision unknown); the ISMM 2009 paper text (slides only).
- **Not examined (source):** RaML, COSTA, and Koka's `fip` checker sources; ReSyn's `test/` corpus.
- **Not measured:** every L1 cell; L2 build time and memory for all tools; L3 for COSTA, Braberman et al., and the toy; all L5 checking speeds; analyzer peak RSS for every system; energy. ReSyn was not run, so nothing about it was measured.
- **Unknown:**
  - whether ReSyn's sharing constraints are complete for abstract potentials, given the README's CEGIS bug warning;
  - whether a per-function summary under *reachability* collection (not scope-based) can be made compositional without whole-program lifetime information. No examined paper gives one.
- **Unsupported (per the sources):** LFPL C translation with additive conditionals; Chin et al. `dispose` insertion for shared or cyclic structures and exponential stack bounds; Niu–Hoffmann closures beyond allocation counting; ReSyn inference of non-constant bounds.
- **Toy-model limits:** the probe illustrates rules on hand-coded programs. It neither checks any published type system nor measures any implementation. Its usage-aspect check implements only the prose `let` side condition for two fixed terms.
- **Stronger conclusions not established:**
  - that additive splitting is optimal for read-only sharing. Aspects show read-only sharing can be free, and LFPL's `×` with `max` sizing shows another non-additive option;
  - that any analysis examined is sound for concurrent mutators or finalization;
  - that reported precision on small benchmarks extrapolates to large programs.

## Evidence

- **Source pin.** `tjknoth/resyn` at `54ff304c635f26b4b498b82be267923a65e0662d`, which was `HEAD` on 2026-11-21 via the GitHub commits API; commit date 2020-12-09. Raw files fetched from `raw.githubusercontent.com` at that revision. Lines used: `src/Synquid/Solver/Resource.hs:104-109, 411-433`; `src/Synquid/Synthesis/Util.hs:226, 435-464, 537-549`; `src/Synquid/Synthesis/TypeChecker.hs:181-208, 315`; `src/Synquid/Synthesis/Explorer.hs:446-465`; `src/Synquid/Solver/TypeConstraint.hs:545-559`; `src/Synquid/Program.hs:630-631`; `README.md`. sha256 of the fetched `Resource.hs` is `da3829b65f3ed00a3bd9efda3999e24a70fb44f8d0af4a96c318a8f6213010df`; of `Util.hs`, `802cf01942f63875687df3bc2ce79bf124fbf8fbd38ab75f4aff5dac5af76eb4`.
- **DOIs.** All 22 DOIs in this report (the 19 in the works table below plus Konečný 2003, Hoffmann–Aehlig–Hofmann POPL 2011 and TOPLAS 2012) were verified against the Crossref REST API (`api.crossref.org/works`) on 2026-11-21 for title, authors, venue, and year. Crossref quirks:
  - VMCAI 2003 shows `published-online`/`issued` 2002-12-16 and `published-print` 2003;
  - `10.29007/xkwx` has a null issue date and page field `543-521`;
  - the LICS 1999 record has a null date.
- **Works and examined copies.** All were fetched on 2026-11-21. Passages are identified at each finding by theorem, lemma, rule, figure or table.

  | Work | DOI | What was read |
  |---|---|---|
  | Hofmann, LICS 1999 | 10.1109/LICS.1999.782641 | full conference text, CiteSeerX PDF copy (found by title search on `citeseerx.ist.psu.edu`) |
  | Hofmann, Information and Computation 183(1), 2003 | 10.1016/S0890-5401(03)00009-9 | metadata only |
  | Hofmann, ESOP 2000 | 10.1007/3-540-46425-5_11 | author's full version, 2000-11-22, https://www.cs.cmu.edu/~fp/courses/15417-s25/misc/Hofmann00njc.pdf |
  | Aspinall–Hofmann, ESOP 2002 | 10.1007/3-540-45927-8_4 | https://homepages.inf.ed.ac.uk/da/papers/readonly/readonly.pdf |
  | Aspinall–Hofmann–Konečný, JFP 18(2), 2008 | 10.1017/S0956796807006399 | abstract (first author's page) |
  | Dal Lago–Hofmann, TCS 412(20), 2011 | 10.1016/j.tcs.2010.12.025 | metadata and secondary descriptions |
  | Hughes–Pareto, ICFP 1999 | 10.1145/317636.317785 | metadata and secondary descriptions |
  | Hofmann–Jost, POPL 2003 | 10.1145/604131.604148 | metadata and secondary descriptions |
  | Jost–Hammond–Loidl–Hofmann, POPL 2010 | 10.1145/1706299.1706327 | https://www.macs.hw.ac.uk/~hwloidl/publications/POPL10.pdf |
  | Atkey, LMCS 7(2:17), 2011 | 10.2168/LMCS-7(2:17)2011 | https://lmcs.episciences.org/685 |
  | Knoth et al., PLDI 2019 | 10.1145/3314221.3314602 | https://tjknoth.github.io/raw/resyn.pdf |
  | Knoth et al., PACMPL 4(ICFP), 2020 | 10.1145/3408988 | https://www.cs.cmu.edu/~janh/assets/pdf/WangKRPH20.pdf |
  | Niu–Hoffmann, LPAR-22, 2018 | 10.29007/xkwx | https://www.cs.cmu.edu/~janh/assets/pdf/NiuH18.pdf |
  | Unnikrishnan–Stoller–Liu, VMCAI 2003 | 10.1007/3-540-36384-X_9 | https://www3.cs.stonybrook.edu/~stoller/papers/dar012.pdf |
  | Braberman et al., ISMM 2008 | 10.1145/1375634.1375655 | abstract only |
  | Chin et al., ISMM 2008 | 10.1145/1375634.1375656 | https://www.comp.nus.edu.sg/~chinwn/papers/ismm08.pdf |
  | Albert–Genaim–Gómez-Zamalloa, ISMM 2009 | 10.1145/1542431.1542450 | authors' slides, https://pdfs.semanticscholar.org/79f7/a4cc3e358e7a7012d50ce48656d605bcfec7.pdf |
  | Albert–Genaim–Gómez-Zamalloa, ISMM 2010 | 10.1145/1806651.1806671 | anonymized copy, https://cliplab.org/papers/heap-usage-ISMM10.pdf |
  | Lorenzen–Leijen–Swierstra, PACMPL 7(ICFP), 2023 | 10.1145/3607840 | MSR-TR-2023-19 v1.0, https://www.microsoft.com/en-us/research/wp-content/uploads/2023/05/fbip.pdf |
- **Secondary descriptions:**
  - Hughes–Pareto: Chin et al. 2008 §9 and Campbell, "Amortised memory analysis using the depth of data structures";
  - Dal Lago–Hofmann: a 2021 MSCS paper on resource monoids, seen as a search-result excerpt;
  - Hofmann–Jost 2003: Atkey 2011 §1 and Niu–Hoffmann §4.
- **Execution.** The toy probe command, host, and output are given in F6. Script sha256: `7096d32f79b6fee2bf54e9cef56838d9507b68471e95bdc31b31261d41146e87`.

## Revalidation

- **ReSyn sharing semantics:** fetch `src/Synquid/Solver/Resource.hs` at a new revision and confirm that the `SharedForm` case still generates `f = fl + fr` with three non-negativity conjuncts. Then check that `shareContext` call sites in `TypeChecker.hs` (`PIf`, `PMatch`, `PApp`) are unchanged. Diff `Explorer.hs` `retrieveAndCheckVarType` for the `schemaMultiply fzero` re-insertion.
- **Rules from papers:** re-read only the cited rule or theorem (ESOP 2002 `let` side condition and Theorem 1; Jost 2010 Lemma 5.7; Niu–Hoffmann `L:ShareCopy`; ISMM 2009 `peak` equation). A newer paper version that changes these invalidates F1 rows.
- **Toy:** `python3 support/sharing_toy.py` must reproduce `support/sharing_toy.out.txt` byte-for-byte (tested only with Python 3.13.15). A difference indicates a script change, not a change in any cited system.
- **Not cheaply revalidatable:** reported precision and timings (Chin, ISMM 2010, Niu–Hoffmann, Jost, LRT/ReSyn) require rebuilding the respective tools, which was not done here.
