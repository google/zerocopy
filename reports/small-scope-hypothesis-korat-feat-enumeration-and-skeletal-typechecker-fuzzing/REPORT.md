# Small-scope evidence, term-enumeration reach, and the structural parameters that trigger type-checker and proof-checker bugs

## Summary

- **The small-scope hypothesis is supported where "scope" is the parameter the defect depends on, and silent elsewhere.** In the one controlled evaluation read (Andoni et al., ten Java data structures, 203–302 mutants each), exhaustive inputs with at most 3–7 objects per class killed 89–99% of mutants in under half an hour per benchmark. In the Redex seeded-bug benchmark (50 bugs in 8 semantics models), the smallest known counterexamples have 3–52 s-expression nodes (median 13.5; measured here from the pinned sources), yet no generator found more than 38 of the 50 within 24 hours per bug.
- **Which strategy wins depends on the budget.** On that benchmark, in-order enumeration with fair combinators found the most bugs for budgets under about 3 minutes (22 bugs at the crossover); a hand-tuned random generator found more afterwards; random indexing into the enumeration was never best.
- **"Small" is defined by the enumerator's cost function, and the choice changes reach by many orders of magnitude.** Depth-bounded series (SmallCheck) grow doubly exponentially for tree-shaped types; size-indexed parts (Feat, LeanCheck) grow singly exponentially. Feat's authors could not finish depth 4 of a Template Haskell syntax series in several hours while its size-20 part holds 65,072,965 values.
- **Reach in one structural parameter costs a constant factor per unit only if the generator has a knob for that parameter.** In a toy checker with a seeded context-truncation bug that needs `k+1` nested binders, size-ordered exhaustive enumeration needs 5, 20, 119, 863, 6,931, 59,275 tests for `k = 0..5` (a factor rising from 4 to about 8.5 per additional binder); depth-bounded enumeration needs 23 values, then 309,697, then about 10^21.
- **Documented checker bugs fall into classes with very different relation to that reach.** Rule errors over one small term (most seeded Redex bugs; the reproducers stored with 178 reported JVM-compiler typing bugs have a median of 10 non-blank lines and 2 class-like declarations) lie inside enumeration or random reach. Bugs gated by a numeric threshold (Rocq's list includes a collision "when more than 256 constructors in a type" and unchecked array literals longer than 4,194,304 elements) lie outside any size-ordered enumeration and are reached only by sweeping the parameter. Bugs that need several interacting declarations or features (43 of 101 entries in Rocq's list by a keyword classification) need generators with declaration-level structure.
- **Passing a bounded-exhaustive run is a statement about one cost function.** It does not bound nesting depth, counter values, or the number of declarations unless the cost function charges for exactly those.

## Applicability

The report is about automatically generated tests for programs whose inputs are structured terms: data structures with invariants, programs of a small calculus, programs of an industrial language. It relates four kinds of material:

- **Enumeration and generation tools, read as source at pinned revisions (not compiled or run; no Haskell or Racket toolchain was available):** `Bodigrim/smallcheck` at `433ada587bf4ff898031aaa5530c0b7aaab10e3a`, `rudymatela/leancheck` at `1723ba7f4e8d1381d93797bf333d57aae9432f8f`, `JonasDuregard/testing-feat` at `a1b32842a8cc8ab467d93a9f97f2365330a02113`, `racket/redex` at `df9e634fe6f48487b8e611b23fcc5945c5c77a6f` (benchmark models and their documentation), `hephaestus-compiler-project/hephaestus` at `4123d504b15686a3e7a0bb28c8614cc7fe53f47a` (generator configuration and the database of bugs it reported).
- **A bug compilation maintained by a proof-assistant project:** `dev/doc/critical-bugs.md` of `rocq-prover/rocq` at `25f5b18a320e4796f181f938d3b74bebe7db4dc4`.
- **Published evaluations, read as text:** Andoni et al. (small-scope hypothesis), Korat, Feat, Fair Enumeration Combinators (the Redex benchmark evaluation), Run Your Research, Skeletal Program Enumeration, Finding Typing Compiler Bugs.
- **Measurements and probes made for this report.** Three scripts *measure upstream data* (counterexample literals in the Redex models; reproducers in Hephaestus's bug database; entries of Rocq's bug list). One script is a *toy model* of enumerating lambda terms against a seeded checker bug; its numbers are properties of the toy only.

The tools are compared, not combined. Findings about a tool's cost function come from its source; findings about its measured reach come from the cited papers and apply to the versions those papers evaluated, which are not the pinned revisions. The Rocq list covers "critical bugs found in Coq since version 8.0" as its maintainers recorded them; it is not a sample of all checker bugs. Nothing here concerns concurrency or distributed-system defects.

## Findings

### 1. Published evaluations: how small the exposing input was and which strategy reached it

| Study | Defects | Measure of "small" | Smallest exposing input | Strategy and budget that reached it |
| :--- | :--- | :--- | :--- | :--- |
| Andoni, Daniliuc, Khurshid, Marinov (2003) | 203–302 generated mutants for each of ten Java data-structure benchmarks | scope = maximum number of objects of each class (and of elements) | "sufficient" scopes: SearchTree 6, DisjSet 4, HeapArray 6, BinomialHeap 7, FibonacciHeap 5, LinkedList 3, SortedList 6, TreeMap 6, HashSet 5, AVTree 5 | Korat, exhaustive within scope; mutants killed 89.07% (FibonacciHeap) to 99.26% (SearchTree); generation plus checking "in less than 0.5 hour", often seconds |
| Redex benchmark (documentation and models in `racket/redex`; evaluation in New et al. 2017) | 50 seeded bugs in 8 models (typed lambda calculi, let-polymorphism, a list machine, red-black trees, delimited continuations, the Racket virtual machine) | s-expression size: one per atom and per parenthesis pair | 3 to 52, median 13.5; nesting depth 2 to 9 (measured, section 2) | 7 generator configurations, up to 24 h per bug and generator; "No strategy was able to find more than 38 of the 50 bugs" |
| Duregård, Jansson, Wang (2012) | bugs in the Template Haskell pretty-printer | Feat size (constructor count) versus SmallCheck depth | not tabulated per bug | Feat enumeration by size; SmallCheck series stalled at depth 4 |
| Zhang, Sun, Su (2017) | "217 confirmed GCC/Clang bug reports, 119 of which have already been fixed" in under six months; "29 CompCert crashing bugs and 42 bugs in two Scala optimizing compilers" in three weeks | existing small test programs used as skeletons; variables re-bound exhaustively | not tabulated | enumeration of all non-α-equivalent variable usage patterns of each skeleton |
| Chaliasos et al. (2022) | "156 bugs (137 confirmed and 85 fixed)": 113 in groovyc, 32 in kotlinc, 11 in javac; 147 classified as typing bugs | — | reproducers stored in the tool's repository: median 10 non-blank lines (measured, section 5) | random generation up to a depth bound plus two mutations; nine months, "three months of CPU time" |
| Klein et al. (2012) | "mistakes in all nine papers" among nine ICFP 2009 papers modelled in Redex, "including one whose essential result had been verified in Coq" | — | not tabulated | unit tests and checking of claims translated into testable conjectures |

Basis: documentation (paper texts), except the measured cells.

Details that qualify the first row. Coverage is not the criterion: the authors show a mutant of `SearchTree.remove` whose loop body is changed, for which "trees that have up to four nodes" already give complete statement and branch coverage but only a five-node tree executes the loop twice and exposes the mutant; they therefore define the sufficient scope by mutant kill rate. Surviving mutants were inspected by hand and "most of them are semantically equivalent to the original programs", but equivalence was not established for all. The scope parameter (objects per class) is exactly the parameter a data-structure bug depends on; the study says nothing about defects gated by other parameters.

The benchmark evaluation of New et al. adds a time axis. Their ad hoc generator "is only better than the best enumeration strategy after 3 minutes. Before that time, the fair in-order enumeration strategy is the best approach"; the figure annotation at the crossover reads 22 bugs. Random selection of an index into the enumeration "is never the best approach, on any time scale". The ad hoc generator and fair in-order enumeration were each at least ten times faster than every other generator on six (different) bugs. Replacing fair combinators by unfair ones made enumeration worse "across the board".

### 2. The Redex seeded-bug benchmark, measured from source

Each buggy model file defines `the-error` (a one-line description) and `small-counter-example`; the benchmark documentation classifies every bug as S (shallow: "errors in the encoding of the system into Redex, due to typos or a misunderstanding"), M (medium: "errors in the algorithm behind the system"), D (deep: "errors in the developer's understanding of the system, such as when a type system really isn't sound and the author doesn't realize it") or U (unnatural), and defines counterexample size as "the number of pairs of parentheses and atoms in the s-expression representation of the term". Applying that definition (and the companion depth function from `redex-doc/redex/scribblings/bug-info.rkt`) to the literals in the pinned tree gives:

| Class | Bugs | Size min / median / max | Depth min / median / max |
| :--- | ---: | :--- | :--- |
| S | 23 | 3 / 13 / 52 | 2 / 4 / 8 |
| M | 19 | 3 / 13 / 46 | 2 / 4 / 9 |
| D | 4 | 12 / 25 / 33 | 5 / 6 / 8 |
| U | 2 | 12 / 13.5 / 15 | 5 / 5 / 5 |
| S or M (two bugs carry both letters) | 2 | 17 / 17 / 17 | 6 / 6 / 6 |
| all | 50 | 3 / 13.5 / 52 | 2 / 5 / 9 |

18 counterexamples have size at most 10, 36 at most 20, and 2 exceed 40. Examples: the application-rule typo of `stlc-1` ("app rule the range of the function is matched to the argument") is exposed by `(hd 0)`, size 3; "the classic polymorphic let + references bug" of `let-poly-2` needs a `let`, a reference cell, a `get` and a `set` (size 28, depth 7); the two largest belong to the delimited-continuation model (46 and 52). Basis: source + execution (`redex_cx.py` under Evidence; a literal-size count, so the three red-black-tree counterexamples that use the `num->n` metafunction are undercounted relative to their expanded values).

Two consequences. The "deep" class (understanding errors) has the largest median, and "medium" and "shallow" are indistinguishable by size, so the documentation's difficulty classes are not a size ordering. And since at most 38 of 50 were found in 24 hours although 36 of 50 have a known counterexample of at most 20 nodes, small size alone does not put a counterexample within reach: the well-formedness and typing preconditions of the models thin the space. (For that reason the benchmark supplies four generator kinds per model: the grammar-based random generator `'grammar`, the in-order enumerator `'ordered`, the random-index enumerator `'enum`, and a `'search` generator that produces terms `#:satisfying` the typing judgment.) Basis: derived from the measured table and the quoted evaluation; per-bug outcomes were not available in the text read.

### 3. Enumeration techniques and their cost functions

| Technique (tool) | What counts as small | Pruning | Indexing | Facts from source or paper |
| :--- | :--- | :--- | :--- | :--- |
| Predicate-pruned (Korat) | finitization: bound on objects per class and field domains | runs the class invariant (`repOk`) on a candidate, monitors which fields it reads, and skips all candidates that differ only in unread fields; generates only nonisomorphic structures | none (backtracking search) | `finBinaryTree(7)`: "429 trees in less than one second"; binary trees of size 12: 208,012 structures from 12,284,830 candidates in 233.59 s out of a state space of 2^92; TreeMap size 9: 122 structures from 50,209,400 candidates in 2,148.50 s (state space 2^130) |
| Depth-bounded series (SmallCheck) | depth of construction | `==>` preconditions filter after generation; the driver reports how many tests "did not meet ==> condition" | none | every `consN` wrapper calls `decDepth`, which requires depth > 0 and subtracts one; naturals at depth `d` are `take (d+1) [0..]`; lists are `cons0 [] \/ cons2 (:)` |
| Size-ordered tiers (LeanCheck) | sum of constructor costs | filtering | none (lists of tiers) | `cons0 x = [[x]]`; `consN f = delay $ mapT ... tiers` with `delay = ([]:)`, i.e. each non-nullary constructor adds one to size; documented default of 200 tests per property |
| Size-indexed parts with cardinalities (Feat) | sum of `pay` costs | none | random access and uniform sampling within a size | `data Finite a = Finite {fCard :: Index, fIndex :: Index -> a}`; defaults "60 seconds timeout, maximum size of 100, bound of 100000 tests per size"; the paper indexes a list-of-booleans enumeration at `10^1000` and states indexing is worst-case quadratic in the size of the selected value |
| Fair combinators (Racket `data/enumerate`, used by the Redex benchmark) | position in a bijection with the naturals | none | random access | the paper cites extraction of the 2^100-th element "in milliseconds"; with an unfair pairing combinator one specific counterexample moves from position 345 to a position whose smallest known index is a 78-digit number |
| Generation from the typing judgment (Redex `#:satisfying`) | derivation depth bound (5 in the benchmark module) | well-typed by construction | none | present as the `'search` generator in the benchmark's model directories; its published evaluation was not read |
| Skeletal enumeration (Zhang, Sun, Su) | number of holes and variables of a given skeleton | only non-α-equivalent fillings; a naive filling of `n` holes with `k` variables gives `k^n` programs | none | "six orders of magnitude reduction" reported for the canonical set |
| Bounded random generation with mutation (Hephaestus) | generator limits | type-directed generation; a type-erasure mutation targets inference, a type-overwriting mutation targets soundness | none | defaults in `src/generators/config.py`: `max_depth=6`, `max_top_level=10`, `min_top_level=5`, `max_type_params=3`, `max_var_decls=3`, `max_functional_params=3`, classes with at most 2 fields and 2 functions, functions with at most 2 parameters |

Basis: source for the tool rows at the pinned revisions; documentation for quoted measurements.

Depth versus size (Feat paper, Template Haskell expression syntax): the number of values per part is 1, 9, 951 for SmallCheck depths 1–3 and "we are not able to complete the enumeration of size 4 (given several hours of execution time)", against 0, 1, 5, 11, 20, 49 for Feat sizes 1–6 and 65,072,965 at size 20. Sampling "the first 10000 values of the series on depth 4" showed "the maximum size in this sample is 35, with more than 50% of the values having a size more than 20". A depth bound therefore does not mean small values. Basis: documentation.

### 4. Toy probe: enumeration reach against a bug that needs nested binders

`enum_reach.py` (under Evidence) is a toy, not a run of any tool above. It enumerates closed untyped de Bruijn lambda terms (variable `i` costs `i+1`, abstraction and application cost 1 plus their parts), decides simple typability by unification, and compares against a checker with a seeded bug `S_k`: a variable with de Bruijn index at least `k` receives a fresh type at every use (a context truncated to `k` entries). A witness is a term the reference rejects and the buggy checker accepts; any witness needs `k+1` nested binders.

| Size | Closed terms | Typable | Cumulative |
| ---: | ---: | ---: | ---: |
| 6 | 17 | 13 | 28 |
| 8 | 116 | 74 | 185 |
| 10 | 895 | 508 | 1,393 |
| 12 | 7,450 | 3,809 | 11,393 |
| 14 | 65,168 | 29,116 | 98,442 |
| 20 | 52,506,837 | — | — |
| 30 | about 5.1 × 10^12 | — | — |

| Binders needed (`k+1`) | Smallest witness size | Tests before first witness, size order | Smallest depth containing a witness | Values in a depth-bounded series up to that depth | Estimated share of witnesses among terms of size 20 / 30 |
| ---: | ---: | ---: | ---: | ---: | :--- |
| 1 | 4 | 5 | 3 | 23 | 0.696 / 0.848 |
| 2 | 6 | 20 | 5 | 309,697 | 0.176 / 0.190 |
| 3 | 8 | 119 | 7 | about 10^21 | 0.035 / 0.040 |
| 4 | 10 | 863 | 9 | about 10^87 | 0.0067 / 0.0080 |
| 5 | 12 | 6,931 | 11 | about 10^351 | 0.0008 / 0.0012 |
| 6 | 14 | 59,275 | 13 | about 10^1405 | 0.0002 / 0.0002 |

Basis: execution (toy model; the depth-bounded column applies the SmallCheck rule "every constructor application costs one unit of depth, a natural at depth `e` ranges over `0..e`" to the three-constructor term type by the recurrence `S(d) = d + S(d-1) + S(d-1)^2`; it is not a SmallCheck run; the last column is a Monte Carlo estimate from 20,000 and 5,000 uniform samples with a fixed seed).

What the toy shows, and only the toy:

- Under size order the cost of one more binder is a factor that rises from 4 to about 8.5 (5 → 20 → 119 → 863 → 6,931 → 59,275). A budget of 10^5 tests reaches six nested binders; each further binder needs roughly a decade more.
- Under depth order the same bug is out of reach beyond two binders, because the witness depth grows by 2 per binder and the series size squares per unit of depth.
- Uniform sampling at a fixed larger size hits this particular bug with a probability that also falls by a factor of 4–8 per binder; in expected test count it beats size-ordered enumeration at every `k` measured (for six binders about 1/0.0002 = 5,000 samples against 59,275 enumerated terms), but each test is a size-20 or size-30 term and the witness is not minimal.
- Neither generic strategy makes nesting depth cheap. A generator with an explicit knob (emit `k+1` abstractions, then a body) reaches any `k` in one test.

The seeded bug is dense among large terms (any ill-typed use of a deep variable triggers it) and the property is checked on all closed terms, so the toy has no well-typedness precondition to satisfy. Bugs that need a specific small pattern inside an otherwise well-typed program behave differently; the toy says nothing about them.

### 5. Reproducers of reported typing bugs in JVM compilers, measured from source

Hephaestus's repository stores `reported/bugs.json` with 178 entries (Groovy 134, Kotlin 33, Java 11; reports dated 2020–2022), each with the reproducer text. Symptoms: unexpected compile-time error 122, crash 33, unexpected runtime behaviour 23. Finding component: generator 90, inference mutation 61, soundness mutation 25, both 2. Status: 117 closed, 14 resolved, 40 open, 7 in other states; resolution "Fixed" for 112. (The paper's count of 156 is an earlier snapshot.)

| Reproducer metric | min | median | 90th percentile | max |
| :--- | ---: | ---: | ---: | ---: |
| non-blank lines | 1 | 10 | 18 | 36 |
| class-like declarations (`class`, `interface`, `object`, `trait`, `enum`) | 0 | 2 | 4 | 8 |
| nesting of generic angle brackets within a line | 0 | 1 | 2 | 5 |
| brace nesting | 0 | 2 | 3 | 5 |

98 reproducers have at most 10 lines, 165 at most 20, 2 more than 30. Generic nesting is at most 2 in 173 of 178. The 23 runtime-behaviour bugs (programs accepted and then misbehaving) have a median of 10 lines and 3 class-like declarations. No reproducer has more class-like declarations (maximum 8) than the generator's default limit on top-level declarations (10). Basis: source + execution (`heph_bugs.py`; lexical heuristics over the stored text; reproducers are as reported, typically after manual or automatic reduction, so they bound the size of a sufficient input, not the size of the program that first triggered the bug).

For this population the structural parameter is the *number of interacting declarations and type parameters*, not depth: a typical reproducer is two or three small classes with one level of generics.

### 6. Entries of Rocq's critical-bug list by trigger parameter

`dev/doc/critical-bugs.md` records for each of 101 entries the component, affected versions, an exploit (often a file in the test suite) and a free-text risk. A keyword classification of each entry's title, risk, exploit and component text (first matching class wins; patterns in `rocq_bugs.py`) gives:

| Class by trigger named in the entry | Entries | Examples (titles quoted) |
| :--- | ---: | :--- |
| numeric size or width threshold | 11 | "collision between constructors when more than 256 constructors in a type" (virtual machine; introduced V8.1; exploit `test-suite/bugs/bug_4157.v`); "array literals longer than max_length not rejected by the typechecker" (risk: "requires constructing an array literal longer than `max_length` (4194304 elements) through the typechecker"); "buffer overflow on large accumulators" (risk: "medium, as it can happen for large irreducible applications"); "buffer overflow on large records and closures" (not fixed; "requires very large number of arguments, fix block size or nested letins") |
| nesting, lifting, de Bruijn index handling | 12 | "missing lift in checking guard" (risk: "unprobable by chance"); "de Bruijn indice bug in checking guard of nested cofixpoints"; "guard checker computes uniform parameters of nested fixpoints in the wrong environment" |
| several interacting declarations or features (modules, functors, sections, universes, template or sort polymorphism) | 43 | "missing universe constraints in typing \"with\" clause of a module type"; "projections are cooked in wrong environment" (risk: "needs local definition in record parameters, in a section with variables") |
| rule error over a single term, and everything else | 35 | "substitution missing in the body of a let" |

Basis: source + execution. The classification is a heuristic over the maintainers' own wording; it was not validated against the exploit files, and the first class also catches entries about primitive integer and floating-point operations, whose trigger is a numeric *value* or an operation rather than a size: 7 of the 11. The four quoted examples are the strict size thresholds.

The list also records which bugs an independent checker would have caught: entries carry an "impacted coqchk versions" field, some reading "none (no virtual machine in coqchk)", and one unfixed entry is titled "coqchk checks too little about primitive declarations".

### 7. Relating bug classes to enumeration reach

| Trigger parameter | Evidence of how small the witness is | Size-ordered or scope-bounded enumeration | Random generation at larger size | What reaches it reliably |
| :--- | :--- | :--- | :--- | :--- |
| wrong or missing rule over one small term | Redex: sizes 3–52, median 13.5; JVM reproducers: median 10 lines | reaches the smallest within seconds to minutes (22 Redex bugs inside 3 minutes); stalls where typing preconditions thin the space | finds more given hours (up to 38 of 50) | either; typed generation or mutation of well-typed programs for the remainder |
| objects per class in a data structure | sufficient scope 3–7 (Andoni et al.) | reaches with predicate pruning in seconds to half an hour | not compared in the study read | predicate-pruned enumeration |
| nesting depth of binders or (co)fixpoints | Rocq: 12 entries by keyword; toy: witness size grows by 2 and size-ordered rank by ×4 to ×8.5 per binder | exponential in depth under size order; infeasible beyond two levels under depth order (toy) | probability falls by ×4–8 per level (toy) | a generator parameterized by depth |
| numeric threshold (counter width, tag width, table size) | 257 constructors; 4,194,305 array elements; "large" accumulators | **never**: the witness is larger than any enumerated size | only if the generator can emit huge literals | sweeping the parameter across powers of two and documented limits |
| number of interacting declarations or features | JVM reproducers: median 2, maximum 8 class-like declarations; Rocq: 43 of 101 entries | needs an enumerator over declaration sequences; per-term enumerators do not produce them | Hephaestus generates 5–10 top-level declarations per program | declaration-aware generators; skeletons taken from existing test suites |
| length of a required command script | Rocq exploit files exist for many entries; their lengths were not measured | not examined | not examined | unknown |

Basis: derived from sections 1–6. The practical reading: a bounded-exhaustive campaign should state its cost function next to its bound, and a checker test plan needs, besides a small-term enumerator, one generator per structural parameter the implementation is known to branch on (context length, tag and counter widths, number of declarations in scope).

### 8. Cost and footprint

| Level | Observation | Basis |
| :--- | :--- | :--- |
| Authoring effort | Tool sizes at the pinned revisions: SmallCheck `Test/` 2,176 lines of Haskell; LeanCheck `src/` 6,614; testing-feat `Test/` 624; Hephaestus `src/` 14,941 lines of Python (generator 2,923; the two mutations 71 and 118); Redex benchmark models 99 files, 5,695 lines. An enumerator instance costs one combinator per constructor (`cons0 [] \/ cons2 (:)`). Korat needs an executable invariant and a finitization per class. Hephaestus reports that a translator for a new target language is "roughly 800 LoC". | source; documentation |
| Agent or person-time, maintenance on change | not reported in the material read | unknown |
| Toolchain build time and memory | not measured (no toolchain available) | not examined |
| Generation throughput | Korat (2002 hardware): 12,284,830 candidates in 233.59 s for binary trees of size 12, about 5 × 10^4 candidates per second. Andoni et al.: BinomialHeap scope 7, 2,577,984 inputs generated in 232.33 s and checked in 67.05 s; FibonacciHeap scope 5, 941,058 inputs in 1,258.95 s. Toy: 98,442 terms enumerated and type-inferred in about 3 s of CPython. | documentation; execution (toy) |
| Random access | Feat: index `10^1000` of a boolean-list enumeration; fair combinators: 2^100-th element in milliseconds | documentation |
| Campaign budgets | Redex benchmark: up to 24 h per bug and generator, 350 combinations; Hephaestus: nine months elapsed, three months of CPU time; skeletal enumeration: under six months for 217 GCC/Clang reports | documentation |
| Execution cost in the product, proof-checking cost | not applicable: these are test generators | — |
| Footprint of results | counterexamples of 3–52 nodes (Redex), reproducers of 1–36 lines (JVM compilers) | execution on upstream data |

### 9. Comprehensibility and conceptual economy

- **A bounded-exhaustive result is the easiest test result to state and the easiest to over-read.** "No counterexample among all inputs up to bound `n`" is auditable in one line, but four tools give four meanings to `n` (objects per class, construction depth, constructor count, position in a bijection). The Feat measurement that a depth-4 series contains values of size 35 is the standard illustration.
- **Diagnostics.** Enumeration in size order returns a smallest counterexample with no shrinking step; random generation returns a large one and depends on a reducer. SmallCheck's driver separately reports tests whose precondition failed, which exposes vacuous runs.
- **One abstraction covers the generic techniques.** An enumeration is a sequence of finite parts ordered by a cost function. Korat's finitization, SmallCheck's depth, LeanCheck's tiers, Feat's parts and fair combinators differ only in the cost function and in whether the parts support counting and indexing. Under this view the bug classes of section 7 are not exceptions: each is reached when its trigger parameter is cheap in the cost function, and missed when it is expensive. A threshold bug is the limiting case in which the parameter must cost O(1) or O(log) rather than O(value).
- **Where the complexity goes.** Choosing the cost function presupposes knowing which parameters the implementation branches on. That knowledge is exactly what a black-box "all small inputs" campaign was meant to avoid needing; skeletal enumeration and mutation of existing test programs import it from human-written tests instead.

### 10. How the cited results were themselves validated

| Concern | Evidence in the material read | Gap |
| :--- | :--- | :--- |
| Do the generators find seeded defects (mutation adequacy)? | Andoni et al.: 89–99% of mutants killed, survivors inspected by hand; Redex benchmark: at most 38 of 50 seeded bugs per strategy | equivalent mutants not fully resolved; per-bug outcomes of the benchmark not read |
| Are passing runs vacuous? | SmallCheck reports unmet preconditions; the toy shows 45% of closed terms of size 14 are typable, so an untyped enumerator wastes about half its tests there | the well-typed share for the real models was not measured |
| Soundness of checkers and compilers | Hephaestus uses derived oracles (its README shows an error class "SHOULD NOT BE COMPILED"); skeletal enumeration reports crashes and wrong code; Rocq keeps exploit files in its test suite and names an independent checker's exposure per entry | no differential run across independent proof checkers was examined |
| Concurrency, crash and hardware faults | out of scope of every tool examined | not examined |
| Human-written semantics and specifications | Klein et al.: errors in all nine modelled papers | no study of how engineers interpret "passed up to bound n" |

Basis: documentation + source + execution (toy) as marked.

## Boundaries

- **Not examined (cited by the material read, identifiers checked against registry metadata, text not read):** Jackson and Damon, "Elements of Style" (DOI `10.1109/32.538605`), which Andoni et al. cite for the hypothesis; Runciman, Naylor and Lindblad, "SmallCheck and Lazy SmallCheck" (DOI `10.1145/1411286.1411292`), so nothing is claimed about Lazy SmallCheck beyond the Feat paper's remark that it can avoid refining unevaluated parts; Pałka et al. (DOI `10.1145/1982595.1982615`); Fetscher et al., "Making Random Judgments" (DOI `10.1007/978-3-662-46669-8_16`), so the measured reach of generation from typing judgments is not reported here; Chaliasos et al.'s study of typing-related JVM compiler bugs (DOI `10.1145/3485500`). Also not examined: the exploit files of Rocq's list, bug lists of other proof checkers, and any study of concurrency or distributed-system defects.
- **Not executed:** SmallCheck, LeanCheck, testing-feat, Redex, Korat and Hephaestus. Every statement about their reach is either from their source text or from the cited papers.
- **Unknown:** which 12 or more Redex benchmark bugs no strategy found and how their counterexample sizes compare with the found ones; the minimal script length for Rocq's module- and section-related entries; whether the keyword classes of section 6 would survive reading each exploit.
- **Known not to apply:** the small-scope evidence of Andoni et al. to defects whose trigger is not the number of objects (their own five-node loop example shows even coverage at smaller scope is insufficient); size-ordered enumeration to threshold-gated bugs; the toy's comparison of random and exhaustive generation to properties with a typing precondition.
- **Unsupported by the tools:** random access into SmallCheck series or LeanCheck tiers; counting without enumerating in LeanCheck and SmallCheck; generation of multi-declaration scripts by the per-term enumerators.
- **Attractive conclusions the evidence does not support:** that most checker bugs have small witnesses *and therefore* bounded-exhaustive testing finds them (the Redex data show small witnesses that 24 hours did not reach); that a depth bound implies a size bound; that the classification of Rocq's list measures how often each class occurs in checkers generally; that the toy's per-binder factor (4 to 8.5) holds for any real checker.

## Evidence

Repository material was read on 2026-11-19 (US Pacific time; 2026-11-20 UTC) from source archives of the pinned revisions; papers were retrieved the same day.

Source locations:

- `racket/redex` @ `df9e634fe6f48487b8e611b23fcc5945c5c77a6f`: `redex-benchmark/redex/benchmark/models/*/*-N.rkt` (`the-error`, `small-counter-example`); `.../models/stlc+lists/generators.rkt` (generator kinds `'grammar`, `'enum`, `'ordered`, `'search`); `redex-doc/redex/scribblings/benchmark-models.scrbl` (classes, size definition); `redex-doc/redex/scribblings/bug-info.rkt` (`type->num->cat`, `count-size`, `count-depth`).
- `Bodigrim/smallcheck` @ `433ada587bf4ff898031aaa5530c0b7aaab10e3a`: `Test/SmallCheck/Series.hs` (`decDepth`, `checkDepth`, `cons0`..`cons6`, instances for `N a` and lists); `Test/SmallCheck/Drivers.hs` (`smallCheck`); `README.md`.
- `rudymatela/leancheck` @ `1723ba7f4e8d1381d93797bf333d57aae9432f8f`: `src/Test/LeanCheck/Core.hs` (`Listable`, `cons0`..`cons5`, `delay`, `holds`, `counterExample`); `src/Test/LeanCheck/IO.hs` (`check`, `checkFor`).
- `JonasDuregard/testing-feat` @ `a1b32842a8cc8ab467d93a9f97f2365330a02113`: `Test/Feat/Enumerate.hs` (`Enumerate`, `parts`); `Test/Feat/Finite.hs`; `Test/Feat/Access.hs` (`index`, `select`, `uniform`, `bounded`, `sizeRange`); `Test/Feat/Driver.hs` (`defOptions`).
- `hephaestus-compiler-project/hephaestus` @ `4123d504b15686a3e7a0bb28c8614cc7fe53f47a`: `src/generators/config.py` (`GenConfig`); `src/transformations/type_erasure.py`, `type_overwriting.py`; `reported/bugs.json`; `README.md`.
- `rocq-prover/rocq` @ `25f5b18a320e4796f181f938d3b74bebe7db4dc4`: `dev/doc/critical-bugs.md`.

Papers (identifiers checked against registry metadata): Andoni et al., `https://groups.csail.mit.edu/sdg/pubs/2002/SSH.pdf` (Tables 2 and 3; no DOI); Korat, DOI `10.1145/566172.566191` (Table 3); Feat, DOI `10.1145/2364506.2364515` (Table 4); New et al., DOI `10.1017/S0956796817000107` (evaluation section, Figures 6–9); Klein et al., DOI `10.1145/2103656.2103691`; Zhang, Sun and Su, DOI `10.1145/3062341.3062379` (arXiv 1610.03148); Chaliasos et al., DOI `10.1145/3519939.3523427`.

### Measurement 1: Redex counterexample literals

Run with `python3 redex_cx.py <path to the redex tree>`.

```python
#!/usr/bin/env python3
"""Measure the `small-counter-example` literal of every seeded bug in the Redex benchmark,
using the upstream definitions of size (1 per atom, 1 per parenthesis pair) and depth."""
import re, sys, pathlib
root = pathlib.Path(sys.argv[1]) / 'redex-benchmark/redex/benchmark/models'
CAT = {'stlc': dict(zip(range(1,10), 'S M S S S M M U S'.split())),
       'poly-stlc': dict(zip(range(1,10), 'S M S S S M M U S'.split())),
       'stlc-sub': dict(zip(range(1,10), 'S S S D SM S S S SM'.split())),
       'let-poly': dict(zip(range(1,8), 'S D M S M M D'.split())),
       'list-machine': {1:'S',2:'M',3:'S'}, 'rbtrees': {1:'M',2:'M',3:'S'},
       'delim-cont': {1:'M',2:'M',3:'S'}, 'rvm': {2:'M',3:'D',4:'M',5:'M',6:'M',14:'M',15:'S'}}
DIR = {'stlc': 'stlc+lists', 'stlc-sub': 'stlc-subst'}

def read(s, i):                      # minimal Racket-ish reader: lists, atoms, 'x -> (quote x)
    while s[i].isspace(): i += 1
    c = s[i]
    if c in '([':
        out, i = [], i + 1
        while True:
            while s[i].isspace(): i += 1
            if s[i] in ')]': return out, i + 1
            v, i = read(s, i); out.append(v)
    if c in "'`,":
        v, i = read(s, i + 1); return ['quote', v], i
    if c == '"':
        j = s.index('"', i + 1); return s[i:j+1], j + 1
    j = i
    while not s[j].isspace() and s[j] not in '()[]': j += 1
    return s[i:j], j
size  = lambda l: 1 + sum(map(size, l)) if isinstance(l, list) else 1
depth = lambda l: 1 + max([0] + list(map(depth, l))) if isinstance(l, list) else 1

rows = []
for typ, cats in CAT.items():
    for num, cat in cats.items():
        src = (root / DIR.get(typ, typ) / f'{typ}-{num}.rkt').read_text()
        src = re.sub(r';[^\n]*', '', src)
        i = src.index('(define small-counter-example') + len('(define small-counter-example')
        v, _ = read(src, i)
        note = ''
        if isinstance(v, list) and v and v[0] in ('quote', 'term'):
            note = 'term' if v[0] == 'term' else ''
            v = v[1]
        flat = re.sub(r'\s+', ' ', src[i:i+400])
        if 'num->n' in flat.split('(test')[0] or ',' in flat.split('(test')[0]: note += '*'
        rows.append((typ, num, cat, size(v), depth(v), note))
        print(f'{typ:13s} {num:3d} {cat:3s} size={size(v):3d} depth={depth(v):2d} {note}')
import statistics as st
for cat in ('S', 'M', 'D', 'U', 'SM'):
    xs = [r[3] for r in rows if r[2] == cat]; ds = [r[4] for r in rows if r[2] == cat]
    if xs: print(f'class {cat:2s}: n={len(xs):2d} size min/median/max = {min(xs)}/{st.median(xs)}/{max(xs)}  depth min/median/max = {min(ds)}/{st.median(ds)}/{max(ds)}')
xs = [r[3] for r in rows]; ds = [r[4] for r in rows]
print(f'all: n={len(xs)} size min/median/max = {min(xs)}/{st.median(xs)}/{max(xs)}; depth min/median/max = {min(ds)}/{st.median(ds)}/{max(ds)}; size<=10: {sum(x<=10 for x in xs)}; size<=20: {sum(x<=20 for x in xs)}; size>40: {sum(x>40 for x in xs)}')
```

Output:

```text
stlc            1 S   size=  3 depth= 2 term
stlc            2 M   size=  5 depth= 3 term
stlc            3 S   size=  8 depth= 4 term
stlc            4 S   size=  9 depth= 4 term
stlc            5 S   size=  7 depth= 4 term
stlc            6 M   size=  7 depth= 4 term
stlc            7 M   size=  9 depth= 4 term
stlc            8 U   size= 12 depth= 5 term
stlc            9 S   size= 15 depth= 6 term
poly-stlc       1 S   size=  6 depth= 3 term
poly-stlc       2 M   size= 11 depth= 4 term
poly-stlc       3 S   size= 14 depth= 4 term
poly-stlc       4 S   size= 15 depth= 5 term
poly-stlc       5 S   size= 16 depth= 5 term
poly-stlc       6 M   size= 16 depth= 5 term
poly-stlc       7 M   size=  9 depth= 4 term
poly-stlc       8 U   size= 15 depth= 5 term
poly-stlc       9 S   size= 18 depth= 5 term
stlc-sub        1 S   size=  8 depth= 4 term
stlc-sub        2 S   size= 13 depth= 5 term
stlc-sub        3 S   size= 10 depth= 4 term
stlc-sub        4 D   size= 22 depth= 8 term
stlc-sub        5 SM  size= 17 depth= 6 term
stlc-sub        6 S   size=  8 depth= 4 term
stlc-sub        7 S   size= 13 depth= 5 term
stlc-sub        8 S   size= 10 depth= 4 term
stlc-sub        9 SM  size= 17 depth= 6 term
let-poly        1 S   size=  8 depth= 4 term
let-poly        2 D   size= 28 depth= 7 
let-poly        3 M   size=  3 depth= 2 term
let-poly        4 S   size=  8 depth= 4 term
let-poly        5 M   size=  3 depth= 2 term
let-poly        6 M   size=  8 depth= 4 term
let-poly        7 D   size= 12 depth= 5 term
list-machine    1 S   size= 22 depth= 5 term
list-machine    2 M   size= 22 depth= 5 term
list-machine    3 S   size= 29 depth= 6 term
rbtrees         1 M   size= 13 depth= 4 term*
rbtrees         2 M   size= 13 depth= 4 term*
rbtrees         3 S   size= 31 depth= 5 term*
delim-cont      1 M   size= 46 depth= 9 
delim-cont      2 M   size= 25 depth= 7 
delim-cont      3 S   size= 52 depth= 8 term
rvm             2 M   size= 24 depth= 6 
rvm             3 D   size= 33 depth= 5 
rvm             4 M   size= 17 depth= 5 
rvm             5 M   size= 23 depth= 7 
rvm             6 M   size= 15 depth= 5 term
rvm            14 M   size= 27 depth= 5 
rvm            15 S   size= 21 depth= 7 
class S : n=23 size min/median/max = 3/13/52  depth min/median/max = 2/4/8
class M : n=19 size min/median/max = 3/13/46  depth min/median/max = 2/4/9
class D : n= 4 size min/median/max = 12/25.0/33  depth min/median/max = 5/6.0/8
class U : n= 2 size min/median/max = 12/13.5/15  depth min/median/max = 5/5.0/5
class SM: n= 2 size min/median/max = 17/17.0/17  depth min/median/max = 6/6.0/6
all: n=50 size min/median/max = 3/13.5/52; depth min/median/max = 2/5.0/9; size<=10: 18; size<=20: 36; size>40: 2
```

### Measurement 2: reproducers in Hephaestus's bug database

Run with `python3 heph_bugs.py <path to the hephaestus tree>`.

```python
#!/usr/bin/env python3
"""Structural size of the reproducer stored with each bug in hephaestus `reported/bugs.json`."""
import json, sys, re, ast, statistics as st, collections
bugs = json.load(open(sys.argv[1] + '/reported/bugs.json'))
def lines(b):
    t = b.get('test')
    if isinstance(t, str):
        try: t = ast.literal_eval(t)
        except Exception: t = t.splitlines()
    return [l for l in (t or []) if l.strip()]
def nest(s, o, c):
    d = m = 0
    for ch in s:
        if ch == o: d += 1; m = max(m, d)
        elif ch == c: d = max(0, d - 1)
    return m
rows = []
for b in bugs:
    L = lines(b)
    if not L: continue
    src = '\n'.join(L)
    rows.append(dict(mut=b['mutator'], sym=b['symptom'], lang=b['language'], loc=len(L),
                     decl=len(re.findall(r'\b(class|interface|object|trait|enum)\b', src)),
                     gen=max(nest(re.sub(r'[-=]>|<=|>=|<<|>>', '', l), '<', '>') for l in L),
                     brace=nest(src, '{', '}'), paren=max(nest(l, '(', ')') for l in L)))
print('bugs in file:', len(bugs), ' with stored reproducer:', len(rows))
print('by language:', dict(collections.Counter(b['language'] for b in bugs)))
print('by symptom :', dict(collections.Counter(b['symptom'] for b in bugs)))
print('by mutator :', dict(collections.Counter(b['mutator'] for b in bugs)))
print('by status  :', dict(collections.Counter(b['status'] for b in bugs)), ' resolution Fixed:', sum(b['resolution'] == 'Fixed' for b in bugs))
def q(xs): xs = sorted(xs); n = len(xs); return f'min {xs[0]} / median {st.median(xs)} / p90 {xs[int(0.9*(n-1))]} / max {xs[-1]}'
def block(name, rs):
    print(f'[{name}] n={len(rs)}')
    for k, lab in (('loc', 'non-blank lines'), ('decl', 'class-like declarations'), ('gen', 'generic <> nesting'), ('brace', 'brace nesting'), ('paren', 'paren nesting')):
        print(f'   {lab:24s} {q([r[k] for r in rs])}')
block('all', rows)
for m in ('generator', 'inference', 'soundness'): block('mutator=' + m, [r for r in rows if r['mut'] == m])
block('symptom=Unexpected Runtime Behavior', [r for r in rows if r['sym'] == 'Unexpected Runtime Behavior'])
print('reproducers with <=10 lines:', sum(r['loc'] <= 10 for r in rows), ' <=20:', sum(r['loc'] <= 20 for r in rows), ' >30:', sum(r['loc'] > 30 for r in rows))
print('generic nesting histogram:', dict(sorted(collections.Counter(r['gen'] for r in rows).items())))
print('declaration-count histogram:', dict(sorted(collections.Counter(r['decl'] for r in rows).items())))
```

Output:

```text
bugs in file: 178  with stored reproducer: 178
by language: {'Groovy': 134, 'Kotlin': 33, 'Java': 11}
by symptom : {'Unexpected Compile-Time Error': 122, 'crash': 33, 'Unexpected Runtime Behavior': 23}
by mutator : {'inference': 61, 'generator': 90, 'soundness': 25, 'inference/soundness': 2}
by status  : {'Open': 40, 'Resolved': 14, 'Closed': 117, 'In Progress': 2, 'Submitted': 4, 'New': 1}  resolution Fixed: 112
[all] n=178
   non-blank lines          min 1 / median 10.0 / p90 18 / max 36
   class-like declarations  min 0 / median 2.0 / p90 4 / max 8
   generic <> nesting       min 0 / median 1.0 / p90 2 / max 5
   brace nesting            min 0 / median 2.0 / p90 3 / max 5
   paren nesting            min 0 / median 1.0 / p90 2 / max 4
[mutator=generator] n=90
   non-blank lines          min 1 / median 10.0 / p90 16 / max 36
   class-like declarations  min 0 / median 2.0 / p90 4 / max 7
   generic <> nesting       min 0 / median 1.0 / p90 2 / max 5
   brace nesting            min 0 / median 2.0 / p90 3 / max 5
   paren nesting            min 0 / median 1.0 / p90 2 / max 3
[mutator=inference] n=61
   non-blank lines          min 4 / median 12 / p90 18 / max 24
   class-like declarations  min 0 / median 2 / p90 4 / max 8
   generic <> nesting       min 0 / median 1 / p90 2 / max 4
   brace nesting            min 0 / median 2 / p90 3 / max 4
   paren nesting            min 1 / median 2 / p90 2 / max 4
[mutator=soundness] n=25
   non-blank lines          min 4 / median 9 / p90 16 / max 33
   class-like declarations  min 1 / median 2 / p90 3 / max 5
   generic <> nesting       min 0 / median 1 / p90 1 / max 2
   brace nesting            min 1 / median 2 / p90 3 / max 3
   paren nesting            min 0 / median 1 / p90 2 / max 3
[symptom=Unexpected Runtime Behavior] n=23
   non-blank lines          min 4 / median 10 / p90 17 / max 33
   class-like declarations  min 1 / median 3 / p90 4 / max 5
   generic <> nesting       min 0 / median 1 / p90 1 / max 2
   brace nesting            min 1 / median 2 / p90 3 / max 3
   paren nesting            min 0 / median 1 / p90 2 / max 3
reproducers with <=10 lines: 98  <=20: 165  >30: 2
generic nesting histogram: {0: 33, 1: 120, 2: 20, 3: 3, 4: 1, 5: 1}
declaration-count histogram: {0: 6, 1: 50, 2: 48, 3: 45, 4: 17, 5: 9, 6: 1, 7: 1, 8: 1}
```

### Measurement 3: keyword classes of Rocq's critical-bug list

Run with `python3 rocq_bugs.py <path to critical-bugs.md>`.

```python
#!/usr/bin/env python3
"""Keyword classification of entries in Rocq's dev/doc/critical-bugs.md by the structural
parameter named in the entry's own title / risk / exploit text (heuristic, see patterns)."""
import re, sys, collections
t = open(sys.argv[1]).read()
ents = [x for x in re.split(r'\n#{4,6} ', t) if 'component:' in x]
def field(x, f):
    m = re.search(r'- ' + f + r': *(.*(?:\n  .*)*)', x); return re.sub(r'\s+', ' ', m.group(1)).strip() if m else ''
PAT = [('size/width threshold', r'overflow|very large|more than \d+|\b25[56]\b|2\^\d+|max_length|too many|large (number|record|accumulat|arit|block|induct)|bigger than|exceed|\d{3,} (constructors|arguments|fields)|int63|31.bit|63.bit|uint63|float|bignum|arity'),
       ('nesting', r'nested|nesting|under (a|binders?)|de bruijn|lift'),
       ('several interacting declarations', r'module|functor|section|universe|template|polymorph|side.effect|opaque|inline|abstract|cumulativ'),
       ]
rows = []
for x in ents:
    title = x.split('\n', 1)[0].strip(); txt = ' '.join([title, field(x, 'risk'), field(x, 'exploit'), field(x, 'component')]).lower()
    cls = next((c for c, p in PAT if re.search(p, txt)), 'single-term rule error / other')
    rows.append((cls, title, field(x, 'component'), field(x, 'risk'), field(x, 'introduced'), field(x, 'fixed in')))
print('entries:', len(rows))
for c, n in collections.Counter(r[0] for r in rows).most_common(): print(f'  {n:3d}  {c}')
if len(sys.argv) > 2:
    for r in rows:
        if r[0] == sys.argv[2]: print(f'- {r[1][:95]} | risk: {r[3][:110]}')
```

Output:

```text
entries: 101
   43  several interacting declarations
   35  single-term rule error / other
   12  nesting
   11  size/width threshold
```

### Toy probe: enumeration reach

Run with `python3 enum_reach.py 14` (CPython 3, standard library only; about 30 s).

```python
#!/usr/bin/env python3
"""Toy model (NOT smallcheck/leancheck/testing-feat/redex): how far depth-bounded and
size-ordered exhaustive enumeration of untyped de Bruijn lambda terms reaches, and the rank
of the first term exposing a seeded checker bug that needs k+1 nested binders.
  term ::= ('v', i) | ('l', t) | ('a', t, u);  size(v i) = i+1, size(l t) = 1+size t,
  size(a t u) = 1+size t+size u.
Reference checker: Curry-style simple-type inference by unification.
Seeded bug S_k: a variable whose de Bruijn index is >= k gets a FRESH type at every use
(a context truncated to k entries), so ill-typed uses of deep variables are accepted."""
import sys, time
from functools import lru_cache
sys.setrecursionlimit(10000)

@lru_cache(None)
def terms(n, m):            # all terms of size n with free indices < m
    out = []
    if 1 <= n <= m: out.append(('v', n - 1))
    if n >= 2: out += [('l', t) for t in terms(n - 1, m + 1)]
    for a in range(1, n - 1):
        out += [('a', t, u) for t in terms(a, m) for u in terms(n - 1 - a, m)]
    return tuple(out)

@lru_cache(None)
def count(n, m):
    c = 1 if 1 <= n <= m else 0
    if n >= 2: c += count(n - 1, m + 1)
    return c + sum(count(a, m) * count(n - 1 - a, m) for a in range(1, n - 1))

def typable(t, k=None):
    sub, fresh = {}, [0]
    def new(): fresh[0] += 1; return fresh[0]
    def find(x):
        while isinstance(x, int) and x in sub: x = sub[x]
        return x
    def occurs(v, x):
        x = find(x)
        return x == v if isinstance(x, int) else occurs(v, x[0]) or occurs(v, x[1])
    def unify(x, y):
        x, y = find(x), find(y)
        if x == y: return True
        if isinstance(x, int):
            if occurs(x, y): return False
            sub[x] = y; return True
        if isinstance(y, int): return unify(y, x)
        return unify(x[0], y[0]) and unify(x[1], y[1])
    def go(t, ctx):
        if t[0] == 'v':
            return new() if (k is not None and t[1] >= k) else ctx[-1 - t[1]]
        if t[0] == 'l':
            a = new(); r = go(t[1], ctx + [a]); return None if r is None else (a, r)
        f = go(t[1], ctx); x = go(t[2], ctx)
        if f is None or x is None: return None
        r = new(); return r if unify(f, (x, r)) else None
    return go(t, []) is not None

def big(x): return str(x) if x < 10**7 else f'~10^{int((x.bit_length() - 1) * 0.30103)}'

def depth_count(d):          # values of (Var Nat | Lam Tm | App Tm Tm) at SmallCheck-style depth d:
    if d <= 0: return 0      # every constructor application costs one unit of depth; Nat at depth e has e+1 values
    s = depth_count(d - 1); return d + s + s * s

print('size n : closed terms | well-typed (reference) | cumulative closed')
cum = 0; N = int(sys.argv[1]) if len(sys.argv) > 1 else 15
t0 = time.time(); per = {}
for n in range(1, N + 1):
    ts = terms(n, 0); cum += len(ts); ok = [typable(t) for t in ts]; per[n] = (ts, ok, cum)
    print(f'{n:6d} : {len(ts):12d} | {sum(ok):12d} | {cum:12d}')
print(f'(enumeration + reference inference of {cum} terms: {time.time()-t0:.1f}s CPython)')
print('counts only, size 20/30/40:', count(20, 0), count(30, 0), count(40, 0))
print('depth-bounded counts d=1..7:', [big(depth_count(d)) for d in range(1, 8)])

def sc_depth(t):             # depth at which a SmallCheck-style series first contains t
    return t[1] + 1 if t[0] == 'v' else 1 + max(sc_depth(x) for x in t[1:])

def unrank(n, m, r):         # r-th term of size n with free indices < m (uniform sampling by counting)
    if 1 <= n <= m:
        if r == 0: return ('v', n - 1)
        r -= 1
    if n >= 2:
        c = count(n - 1, m + 1)
        if r < c: return ('l', unrank(n - 1, m + 1, r))
        r -= c
    for a in range(1, n - 1):
        ca, cb = count(a, m), count(n - 1 - a, m)
        if r < ca * cb: return ('a', unrank(a, m, r // cb), unrank(n - 1 - a, m, r % cb))
        r -= ca * cb
    raise IndexError

import random
rng = random.Random(20261119)
def density(k, n, samples=20000):   # Monte Carlo estimate of the exposing fraction at size n
    hits = 0
    for _ in range(samples):
        t = unrank(n, 0, rng.randrange(count(n, 0)))
        hits += (not typable(t)) and typable(t, k)
    return hits / samples

print('seeded bug S_k: first size-ordered witness (reference rejects, buggy checker accepts)')
print('  k binders | witness size | rank (tests before first hit) | min depth | depth-bounded values to reach it | est. exposing fraction at size 20 / 30')
for k in range(0, 6):
    rank = 0; hit = None; mind = None
    for n in range(1, N + 1):
        ts, ok, _ = per[n]
        for t, o in zip(ts, ok):
            if hit is None: rank += 1
            if not o and typable(t, k):
                if hit is None: hit = (n, rank)
                d = sc_depth(t); mind = d if mind is None else min(mind, d)
    if hit:
        assert mind == 2 * k + 3
        w = f'{hit[0]:12d} | {hit[1]:29d} | {mind:9d} | {big(depth_count(mind)):>32s}'
    else:
        below = sum(count(i, 0) for i in range(1, 2 * k + 4))
        w = f'  (> {N}; predicted {2*k+4}) | (> {per[N][2]}; predicted > {below}) | (pred. {2*k+3}) | {big(depth_count(2*k+3)):>32s}'
    print(f'  {k} {k+1:7d} | {w} | {density(k, 20):.4f} / {density(k, 30, 5000):.4f}')
```

Output:

```text
size n : closed terms | well-typed (reference) | cumulative closed
     1 :            0 |            0 |            0
     2 :            1 |            1 |            1
     3 :            1 |            1 |            2
     4 :            3 |            2 |            5
     5 :            6 |            5 |           11
     6 :           17 |           13 |           28
     7 :           41 |           27 |           69
     8 :          116 |           74 |          185
     9 :          313 |          198 |          498
    10 :          895 |          508 |         1393
    11 :         2550 |         1371 |         3943
    12 :         7450 |         3809 |        11393
    13 :        21881 |        10477 |        33274
    14 :        65168 |        29116 |        98442
(enumeration + reference inference of 98442 terms: 2.8s CPython)
counts only, size 20/30/40: 52506837 5116010587910 614709794573921359
depth-bounded counts d=1..7: ['1', '4', '23', '556', '309697', '~10^10', '~10^21']
seeded bug S_k: first size-ordered witness (reference rejects, buggy checker accepts)
  k binders | witness size | rank (tests before first hit) | min depth | depth-bounded values to reach it | est. exposing fraction at size 20 / 30
  0       1 |            4 |                             5 |         3 |                               23 | 0.6959 / 0.8478
  1       2 |            6 |                            20 |         5 |                           309697 | 0.1762 / 0.1902
  2       3 |            8 |                           119 |         7 |                           ~10^21 | 0.0348 / 0.0398
  3       4 |           10 |                           863 |         9 |                           ~10^87 | 0.0067 / 0.0080
  4       5 |           12 |                          6931 |        11 |                          ~10^351 | 0.0008 / 0.0012
  5       6 |           14 |                         59275 |        13 |                         ~10^1405 | 0.0002 / 0.0002
```

## Revalidation

- **Redex benchmark.** Rerun `redex_cx.py` on a newer tree; a change in the number of bugs (50) or in any size is immediately visible. To extend the finding, obtain per-bug results of a benchmark run and join them with the size column.
- **Cost functions.** In SmallCheck, check that `consN` still wraps `decDepth` and that `decDepth` still guards on positive depth; in LeanCheck, that `consN` still applies `delay` once; in testing-feat, that `defOptions` still reads 60 s, sizes 0–100, 100,000 tests per size. A change in any of these changes what "bound n" means for that tool.
- **Hephaestus.** Rerun `heph_bugs.py`; compare the generator limits in `src/generators/config.py` with the maxima of the reproducer metrics. A reproducer with more declarations than the default top-level limit would contradict the statement in section 5.
- **Rocq list.** Rerun `rocq_bugs.py`; new entries appear in the counts. To validate the classes, read the exploit file of each entry in the two smallest classes (23 files or fewer) and record the actual trigger.
- **Toy probe.** Rerun `enum_reach.py 14`; the rank column must read 5, 20, 119, 863, 6931, 59275. To test whether the per-binder factor transfers to a real checker, replace the toy checker by calls to that checker and seed an equivalent context-truncation bug.
- **Depth versus size in a real enumerator.** With a Haskell toolchain, count `length (listSeries d :: [T])` for the three-constructor term type and compare with 1, 4, 23, 556, 309697; this converts the recurrence in section 4 into a measurement of SmallCheck itself.
- The evaluations quoted in section 1 can only be revalidated by rerunning the original experiments; no cheap check exists.
