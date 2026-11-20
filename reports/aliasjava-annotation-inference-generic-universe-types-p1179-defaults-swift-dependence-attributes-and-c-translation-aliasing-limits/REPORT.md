# Where ownership and lifetime annotations come from: AliasJava and generic-universe-type inference, Rust elision, C++ lifetime-profile defaults, Swift lifetime-dependence defaults, and aliasing limits of C-to-safe-Rust translation

## Summary

- **Inferred ownership typings have no principal solution, so ownership inference is an optimization problem, not a decision problem.**
  - Dietl, Ernst, and Müller (ECOOP 2011) state that "ownership types have no single most general typing" and that "a flat ownership structure gives a trivial typing".
  - Inference therefore always succeeds in the trivial sense. What it proves is *validity*: the inferred typing satisfies the checker, because "all type rules are encoded as mandatory constraints". Among valid typings it picks one by heuristic weights solved with weighted Max-SAT.
  - Huang et al. (ECOOP 2012) instead define an objective "best typing" metric and maximize it.
  - No examined system proves completeness relative to operational safety. AliasJava's alias-parameter inference has "no proof that [it] terminates".
- **Measured cost and coverage of research inference.**
  - AliasJava inferred annotations for 408 JDK 1.2.1 classes. `lent` took 33 s and `unique` 151 s, versus about 100 s to parse and type-check; alias-parameter solving took about 30 min with 2 GB.
  - About 50% of parameters came out `lent` or `unique`. However, many classes received "dozens if not hundreds of inferred parameters". That is a comprehensibility failure, not a soundness failure.
  - Generic Universe Types inference ran in 3.5–6.2 s of constraint generation plus 1.0–2.0 s of solving on 1.8–4.7 kSLOC programs. JabRef (about 74 kSLOC) took 41 s plus 66 s, but those results could not be re-checked because annotation insertion crashed.
- **Production languages default rather than infer.** Each default is a local, syntactic choice of *one* full annotation:
  - Rust elision: "the elided form is just a shorthand", and the alternative is an error. RFC 141 measured that the rules would remove 147 of the 169 annotations then required in `libstd` (87%).
  - The C++ lifetime profile (P1179R1): "Defaults are never central to the analysis method, and so they can use heuristics."
  - Swift `@_lifetime` defaults: introduced "slowly", and "Inference cases can be added but not removed".
  - Because each default picks one member of a non-singleton set, a default can reject a program that a *different* full annotation accepts. A real `rustc` run confirms this for Rust (see the Findings section).
- **Today's Rust standard library leans heavily on elision** (syntactic survey, nightly 2026-11-11 sources).
  - 1,547 parsed function signatures have a lifetime position in the return type. 1,040 (67.2%) elide every output lifetime, and only 16 (1.0%) write a function-level lifetime that RFC 141 elision would have produced.
  - 113 (7.3%) need an explicit function-level lifetime, 336 (21.7%) name an impl- or trait-level lifetime, and 42 (2.7%) use only `'static`.
- **Recovering ownership from unannotated C hits the borrow checker's precision, not just the analysis's.**
  - Emre et al. (OOPSLA 2023) find that existing translation methods make only 12% of pointers safe references. Encoding a more precise analysis in a form the unmodified compiler accepts raises this to 21%. They attribute the limit to "a lack of precision in the Rust compiler's safety checker, causing many safe pointer manipulations to be labeled as potentially unsafe".
  - Crown (CAV 2023) reports median reductions of 37.3% in raw pointer declarations and 62.1% in raw pointer uses. Its authors state that the translation "is in theory neither sound nor complete".

## Applicability

**Subjects and their relationship.** The subjects are compared, not composed. They fall into three groups:

1. **Research ownership/alias inference.**
   - Papers: Aldrich–Kostadinov–Chambers 2002, Dietl–Ernst–Müller 2011, Huang–Dietl–Milanova–Ernst 2012.
   - Implementations: `opprop/checker-framework-inference` at `2b6e1d9e4ea1a5e2908fecb1691700021b22d3dd` and `opprop/universe` at `ee75b409f57b0aaff733e0b5a3682dd2768dccc9`. These are maintained descendants of the GUT inference implementation. The 2011 paper's original Scala tool was not examined.
2. **Production defaults.**
   - Rust: `rust-lang/rfcs` at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (RFC 141). Also `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, built from `rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, and its shipped `library/` sources.
   - C++: Sutter's P1179R1 as `docs/Lifetime.pdf` in `isocpp/CppCoreGuidelines` at `5baf9fe252d034e8363217efc6e12c2215f2a442`, plus Clang's lifetime attribute inference in `llvm/llvm-project` at `21dba964640e0a1e037caea23f6afd86dd0567e0`.
   - Swift: SE-0446 and SE-0103 in `swiftlang/swift-evolution` at `f75d0a0456d72c2ca3ae418cc6a9939d32f42779`, and `docs/ReferenceGuides/LifetimeAnnotation.md`, `lib/AST/LifetimeDependence.cpp`, and `test/Sema/lifetime_depend_infer.swift` in `swiftlang/swift` at `4b7146ceb4f284a962f7669f3c7780ddb5b643ff`.
3. **C-to-safe-Rust translation.** Emre et al. 2023 (abstract only), Zhang et al. 2023 (arXiv:2303.10515 full text), and the Crown repository `KomaEc/crown` at `621904cd356b433215d5f55db39ffd71714f44ff` (README only).

**Scope limits.**

- Swift lifetime annotations are experimental. They are enabled by `-enable-experimental-feature Lifetimes` and spelled `@_lifetime`. SE-0446 (status "Implemented (Swift 6.2)") defines `~Escapable` but defers dependence annotations to a future proposal. Statements about Swift defaults apply to the pinned compiler revision only.
- Rust execution results apply to the stated nightly compiler with editions 2021 and 2024 as labelled.
- The standard-library survey is syntactic. It covers the 933 of 1,046 files under `library/{core,alloc,std}/src` that `syn` 2.0.119 parses.
- No Swift or Clang binary was run. Swift and C++ statements are documentation/source-based.

## Findings

### 1. A common frame for annotation sources

Let `C(P, A)` be a checker that accepts or rejects program `P` under annotations `A`. Annotations can come from three sources:

- **programmer** `A_p`;
- **default** `D`, a function from a *declaration signature alone* to annotations;
- **inference** `I`, a function from the *whole program or module* to annotations.

The properties at issue are:

```text
validity          C(P, I(P)) = accept whenever I returns
soundness of C    C(P, A) = accept  ⇒  P is safe under semantics S
completeness/C    (∃A. C(P, A) = accept)  ⇒  C(P, I(P)) = accept
principality      ∃A*. ∀A. C(P, A) = accept ⇒ A ⊑ A*  (A* most general)
default fidelity  (∃A. C(P, A) = accept)  ⇒  C(P, D(sig(P)) ∪ A_p) = accept   -- generally false
```

| System | Source of annotations | Validity | Principal? | Complete w.r.t. checker | Complete w.r.t. semantics |
|---|---|---|---|---|---|
| AliasJava (2002) | inference + programmer refinement | annotation system proved sound (subject reduction, progress, uniqueness, ownership consistency; proofs in a companion report) | not claimed | alias-parameter solver: "no proof that our inference algorithm terminates" | not claimed |
| GUT tunable inference (2011) | weighted Max-SAT + partial annotations | "Any such typing is guaranteed to be correct, as all type rules are encoded as mandatory constraints" | **no**: "ownership types have no single most general typing" | trivially, since a flat typing always exists | not claimed |
| Ownership inference and checking (2012) | maximize a "best typing" metric | via the checker (abstract) | defines an objective optimum instead | not examined | not examined |
| Rust elision | default | elided form ≡ expanded form ("just a shorthand") | n/a | **no** (§4) | n/a |
| C++ lifetime profile | default (heuristic chain) | defaults "can use heuristics" | n/a | not claimed | not claimed |
| Swift `@_lifetime` | default (four rules) + explicit | strict inference diagnoses ambiguity | n/a | not claimed | not claimed |
| Crown (C→Rust) | constraint solving (SAT) | translations compiled in all reported benchmarks | — | "in theory neither sound nor complete" | — |

Basis: documentation (papers, proposals) + source, as cited per row in §§2–5.

### 2. Research inference systems

**AliasJava** (Aldrich, Kostadinov, Chambers, OOPSLA 2002; full text).

- Annotations: `unique`, `owned`, `lent`, `shared`, and alias parameters on classes and methods.
- Algorithm, in three stages:
  1. `lent` by a constraint graph;
  2. `unique` by a graph that depends on the inferred `lent`. Both graphs are "linear in the size of the source text", so these stages are linear time.
  3. The remaining annotations come from a constraint-based alias analysis over equality, component, and instantiation constraints. "The underlying problem of finding an optimal solution … is undecidable [KTU93], and we have no proof that our inference algorithm terminates. However, in practice our algorithm works well".
- Results on small examples: inference reproduced the paper's hand annotations "up to renaming of parameters". Where it differed, it inferred `lent`/`unique` "more precise than the ones in the figures".
- JDK 1.2.1, 408 classes reachable from `java.lang.Object`:
  - `lent` inference took 33 s and `unique` 151 s, against about 100 s for parsing and type-checking;
  - alias-parameter solving took about 30 min using 2 GB;
  - about 50% of method and constructor parameters were inferred `lent` or `unique`, with the rest split about equally between `shared` and alias parameters plus a few `owned`;
  - imprecision showed up mainly as unnecessary `shared`, and was "very sensitive to the way that the type system is encoded into constraints".
- Understandability: "many classes had dozens if not hundreds of inferred parameters. In a sense, the analysis is too precise".
- Manual annotation costs (L1 data):
  - `java.util.Hashtable` (934 lines including comments) took about 2 h 20 min and needed one source change, plus partial unchecked annotations on 17 other classes.
  - The Aphyds model (7 classes, 3,550 lines by `wc`) took about 3 h 40 min.
  - Derived rates: about 400 lines/hour and about 970 lines/hour of annotated code.

**Generic Universe Types tunable static inference** (Dietl, Ernst, Müller, ECOOP 2011; full text).

- Constraint variables are introduced per type-use location and per viewpoint-adaptation expression. Type rules become mandatory constraints, and preferences become breakable weighted constraints. A weighted Max-SAT solver returns a maximum-weight solution.
- Soundness of results comes from the encoding. `lost` is forbidden in pseudo-assignments "to ensure soundness of the inferred results".
- Benchmarks:

| Benchmark | SLOC | Constraint vars | CNF vars / clauses (topology) | Gen + solve, topology (s) | `rep` / `any` share (topology) |
|---|---|---|---|---|---|
| zip | 2,611 | 455 | 2,949 / 13,639 | 4.5 + 1.1 | 18% / 15% |
| javad | 1,846 | 364 | 3,113 / 14,989 | 3.5 + 1.0 | 24% / 25% |
| jdepend | 2,460 | 824 | 6,024 / 28,110 | 5.1 + 1.4 | 21% / 15% |
| classycle | 4,658 | 1,548 | 10,242 / 53,062 | 6.0 + 1.8 | 13% / 14% |
| JabRef | ≈74,000 | 24,402 vars, 248,858 constraints | 521,152 / 1,606,319 | 41 + 66 (42 in SAT solver) | — |

- Hardware: two 4-core Xeon E5405 at 2.0 GHz, single-threaded, Java heap limited to 1 GB. Peak pre-GC memory was about 160 MB on the four case studies and 510 MB on JabRef.
- Correctness of the four case studies was checked independently: "We inserted the inferred annotations into the source code and ran the GUT type checker on these programs. In each case, the type checker verified the correctness of the inference results". The inference tool and the checker "are independent implementations".
- Inferring the owner-as-modifier encapsulation discipline required "around 300 purity annotations" added by hand across the four projects.
- The authors call "10–20% inferred rep annotations" promising and blame flatness on the library default `peer`. JDK code was not analysed and defaulted to `peer`, which "force[s] structures to be flatter than desired".
- On JabRef, "the Annotation File Utilities crash when inserting the annotations, so we cannot use the GUT type checker to verify the results".
- Basis: documentation (paper Figs. 8–9, §5).
- Implementation today (source):
  - `opprop/universe` `src/main/java/universe/solver/UniverseSolverEngine.java` lines 9–18 select `MaxSatSolverFactory`.
  - `UniverseInferenceChecker.java` exposes lint options `checkOaM` and `checkStrictPurity` (line 20).
  - `checker-framework-inference` `InferenceMain.java` lines 56–67 state that "inference only generates constraints, it does not enforce type-checking rules". Constraints are solved and a JAIF file is produced to insert annotations. Lines 69–70 say that type-checking with inferred annotations without inserting them first is future work.
  - Derived: validity of an inferred typing is established by *re-running the checker on the annotated program*. That step failed on JabRef in 2011.

**Ownership inference and checking** (Huang, Dietl, Milanova, Ernst, ECOOP 2012; abstract only).

- A unified framework for Universe Types and Ownership Types with "an objective metric defining a 'best typing'".
- An inference that maximizes the metric, with programmer influence through partial annotations, implemented on the Checker Framework.
- Benchmark coverage figures were not examined.

**Uno** (Ma and Foster, OOPSLA 2007): bibliographic metadata only. A search-indexed summary states that some aliasing properties are common while field and argument ownership are relatively uncommon. This was not verified against the paper; see Boundaries.

### 3. Production default and elision rules

#### 3.1 Rust

RFC 141 (normative for the rules it introduced; `text/0141-lifetime-elision.md`):

- Each elided input lifetime becomes a distinct parameter. With exactly one input lifetime position, it is assigned to all elided outputs. With `&self`/`&mut self`, self's lifetime is assigned to all elided outputs. "Otherwise, it is an error to elide an output lifetime" (line 123).
- "the *actual* signature of a `fn` or `impl` is based on the expansion rules above; the elided form is just a shorthand" (lines 125–126).
- Impact: "of the 169 lifetimes that currently require annotation for `libstd`, 147 would be elidable under the new rules, or 87%" (lines 240–241). The figure excludes lifetimes already elidable under the previous rules.

**Execution probe** (`support/rust_defaults/cases.sh`; `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`; each case compiled as `--crate-type lib --emit=metadata`):

| Case | Edition | Result | Meaning |
|---|---|---|---|
| A1 `fn pick(&self, o: &str) -> &str { o }` | 2021 | REJECT "lifetime may not live long enough" | elision ties output to `self` |
| A2 same with `<'a>(&self, o: &'a str) -> &'a str` | 2021 | ACCEPT | a different full annotation accepts the same body |
| B1 `fn longest(x: &str, y: &str) -> &str` | 2021 | REJECT E0106 | no default exists, so annotation is mandatory |
| B2 annotated with one `'a` | 2021 | ACCEPT | |
| C1 `fn mk<'a>(x: &'a u8) -> Box<dyn Fn() -> u8>` | 2021 | REJECT "lifetime may not live long enough" | default object lifetime bound on `Box<dyn …>` is `'static` |
| C2 `… Box<dyn Fn() -> u8 + 'a>` | 2021 | ACCEPT | |
| D1 `fn it(v: &Vec<u8>) -> impl Iterator<Item = u8>` | 2021 | REJECT E0700 | 2021 return-position `impl Trait` does not capture the elided lifetime |
| D2 same | 2024 | ACCEPT | edition 2024 changed the capture default |
| D3 2021 with `+ use<'a>` | 2021 | ACCEPT | explicit capture list |
| E1 closure `\|x: &u8\| -> &u8 { x }` | 2021 | REJECT "lifetime may not live long enough" | closure signatures do not get `fn`-style elision |
| E2 `fn f(x: &u8) -> &u8 { x }` | 2021 | ACCEPT | |
| F1 `impl R for B<&u8>` | 2021 | ACCEPT | impl-header elision |
| G1 `const S: &str`, `static T: &[u8]` | 2021 | ACCEPT | elided `'static` in item types |

Derived:

- Rust has at least five distinct default regimes for lifetimes: `fn` elision, impl-header elision, `dyn` object-lifetime defaults, `impl Trait` capture (edition-dependent), and const/static `'static`. Closures behave differently from `fn` items.
- A1 vs A2 is a concrete instance of "a default rejects what some full annotation accepts". The error is recoverable only by writing the annotation.
- D1 vs D2 shows that a default was changed across editions, and the change turned rejections into acceptances.

**Standard-library survey** (`support/elision_survey`, a `syn`-based visitor; Basis: execution, syntactic approximation over real source, not compiler-verified):

| `library/` | Files parsed / total | fn signatures | with output lifetime | ELIDED | EXPLICIT_ELIDABLE | EXPLICIT_NEEDED | OUTER_LIFETIME | STATIC_ONLY |
|---|---|---|---|---|---|---|---|---|
| `core/src` | 221 / 295 | 2,995 | 496 | 278 (56.0%) | 10 | 52 | 138 | 18 |
| `alloc/src` | 90 / 97 | 2,693 | 494 | 314 (63.6%) | 3 | 34 | 139 | 4 |
| `std/src` | 622 / 654 | 7,767 | 557 | 448 (80.4%) | 3 | 27 | 59 | 20 |
| **total** | 933 / 1,046 | 13,455 | 1,547 | 1,040 (67.2%) | 16 (1.0%) | 113 (7.3%) | 336 (21.7%) | 42 (2.7%) |

Derived:

- Among signatures whose output lifetimes are function-level (ELIDED + EXPLICIT_*, 1,169), elision covers 1,040 as written (89.0%), and could cover 1,056 (90.3%) if the 16 redundant explicit forms were elided.
- This is a different metric from RFC 141's 87% (annotations *required under the old rules*). The two should not be equated.
- 113 parse failures are mostly nightly-only syntax that `syn` 2.0.119 rejects ("expected identifier or `_`": 83; "expected curly braces": 27).
- Lifetimes hidden in paths without explicit arguments (e.g. `Foo` for `Foo<'a>`) are invisible to the survey.

#### 3.2 C++ lifetime profile (P1179R1) and Clang

P1179R1 (Sutter, "Lifetime safety: Preventing common dangling", R1 version 1.1, dated 2019-11-22; `docs/Lifetime.pdf` SHA-256 `4f81c6b189b282067174105815ccf681ca580d75f8d010956927e85a8124e4cd`):

- The analysis is local: a "simple acyclic control flow graph (ACFG)" tracks points-to sets (`pset`) for *Owner* and *Pointer* types.
- §2.5 Note (p. 28): "All defaults are only for convenience to minimize annotation in the common case. Defaults are never central to the analysis method, and so they can use heuristics."
- Default for an unannotated Pointer output `ret` (p. 32). Let `Pin`/`Oin` be the Pointer/Owner inputs, with a `ret` suffix for the subset whose dereference type matches `ret`'s:
  1. if `Pin_ret ∪ Oin_ret` is non-empty, `post(lifetime(ret, Pin_ret ∪ Oin_ret))`;
  2. else weak rvalue Owner inputs of matching type;
  3. else all `Pin ∪ Oin` regardless of type;
  4. else weak rvalue Owners regardless of type;
  5. else `{global}`.
- Example given: `int* f(int x, int* p, string_view sv, string& s, const string& s2)` defaults to `lifetime(ret,{p})`.
- Virtual overrides inherit pre/postconditions.
- The abstract reports that the "current Clang-based implementation is unoptimized and incurs only about 5% overhead in compiling large LLVM translation units" (L3, cited).
- The revision history line on p. 7 says "R1: Version 1.1 (November 2010)", which conflicts with the cover date 2019-11-22. The cover date is taken as authoritative.

Clang at the pinned revision (source, `clang/lib/Sema/SemaAttr.cpp`):

- `inferGslOwnerPointerAttribute` (from line 170) attaches `[[gsl::Owner]]` to a fixed name list of `std` types (`vector`, `basic_string`, `unique_ptr`, `optional`, `flat_map`, …; list at line 171). It attaches `[[gsl::Pointer]]` to `basic_string_view`, `reference_wrapper`, `regex_iterator`, `span`.
- `inferLifetimeBoundAttribute` (line 238) adds implicit `lifetimebound` only for specific builtins (`std::move`, `std::forward`, `std::addressof`, `as_const`, …), propagation through `std::make_unique`, and two `std` constructors (`basic_string_view(const CharT*)`, `span(T(&)[N])`).
- `inferLifetimeCaptureByAttribute` does not infer "if any parameter is explicitly annotated" (line 323).
- `AttrDocs.td` (`LifetimeBoundDocs`, from line 4842) documents opt-in `[[clang::lifetimebound]]` on parameters.

Derived: the production compiler does not implement P1179's general signature defaults in Sema. It uses name-list inference for standard-library entities plus opt-in attributes. This is a narrower default regime than the paper's.

#### 3.3 Swift lifetime dependence

- SE-0446 (status "Implemented (Swift 6.2)") introduces `~Escapable` and states that dependence constraints are "being tracked in a future proposal".
- `docs/ReferenceGuides/LifetimeAnnotation.md` (pinned) defines `@_lifetime(target: [borrow|&|copy] source)`.
- Default rules (§"Default lifetimes", line 59 onward):

| Rule | Condition | Default | Doc statement on limits |
|---|---|---|---|
| Same-type | `~Escapable` result `R`, non-`inout` parameter `a` with `A == R` (incl. implicit `self` of non-mutating methods) | `@_lifetime(copy a)` | resolved at declaration time; the generic context at the call is "not considered" |
| `inout` | every `~Escapable` `inout a` / `mutating self` | `@_lifetime(a: copy a)` | applies "even if an explicit `@_lifetime` attribute already specifies the same `inout` parameter" (line 119); suppress only with `immortal`. Full reassignment syntax "is a side-effect of the implementation rather then a deliberate syntax feature" (line 139) |
| Single parameter | one parameter `a` (or method with no parameters) and no same-type default | `borrow a` if `Escapable`; `&a` if `inout Escapable`; **none** if `~Escapable` | for `~Escapable` sources "copy is the obvious choice … but it is not always correct" |
| Implicit init/setter | all init arguments `~Escapable`; implicit setter | `copy` of each / `self: copy self, copy newValue` | no default if any init argument is `Escapable` (unless sole argument) |
| Function types | closures returning `~Escapable` | `captures` plus `copy` of `~Escapable` parameters | — |

- Implementation order (source, `lib/AST/LifetimeDependence.cpp`): `inferOrDiagnose` (from line 1506) applies the same-type rule *before* the single-parameter rule (line 1518), then the mutating-`self` and `inout` rules.
- "Strict inference only handles a single escapable parameter" (line 1874).
- Lines 1920–1921: "Lazy inference for .swiftinterface backward compatibility and experimentation. Inference cases can be added but not removed."
- `test/Sema/lifetime_depend_infer.swift` contains 68 `DEFAULT:` annotations and 79 `expected-error` lines in 972 lines (execution: `grep -c`).
- Lifetime subtyping: a conforming function may have *fewer* dependencies than the protocol requirement. A `captures` dependence "can be added but not removed".
- Precedent, SE-0103 (Swift 3.0): closure parameters changed from escaping-by-default to non-escaping-by-default, with `@escaping` required and a fix-it. A default polarity was reversed once already, with tooling to migrate.

Derived: Swift is the only examined language whose documentation explains *why* defaults are deliberately incomplete: they are added slowly, and only when unambiguous. It also states the monotonicity constraint that published interfaces impose (defaults can be added but not removed).

#### 3.4 Cross-language comparison

| | Rust elision | C++ lifetime profile (P1179R1) | Swift `@_lifetime` defaults |
|---|---|---|---|
| Default abbreviates | `'a` binding of outputs to the unique input or to `self` | `post(lifetime(ret, S))`, S chosen by type-directed heuristic chain | `copy`/`borrow`/`&` dependence on a chosen source |
| When no default applies | hard error E0106 | falls through to `{global}` | diagnostic (strict) or lazy inference in `.swiftinterface` |
| Surprising constraints | `&self` methods returning data from other params (A1); `dyn` defaults to `'static`; closures differ; `impl Trait` capture changed in edition 2024 | heuristics may bind `ret` to the wrong input set (stated as permissible) | `inout` default still applies under explicit annotation; same-type default ignores call-site generics |
| Stated relation to full form | identical by definition ("shorthand") | none beyond "convenience" | subtyping rules for conformance; no completeness statement |
| Measured coverage | 87% of required `libstd` annotations (RFC 141); 67.2% of output-lifetime signatures fully elided in 2026 std/core/alloc (this report) | not measured | not measured |

### 4. Can a default reject a program that some full annotation accepts?

- **Yes, for every examined default that picks among several valid annotations.** Rust demonstrates it by execution (A1 vs A2).
- Derived argument:
  - A default `D` is a function of the signature only, so it must pick one annotation per signature.
  - If the set of bodies that typecheck under annotation `A1` differs from the set under `A2` for the same signature, any choice of `D(sig)` rejects some body that the other annotation accepts.
  - Only a *principal* annotation (one that accepts every body any annotation accepts) would avoid this. Section 2 records that ownership typings lack principal solutions, and Rust's output-lifetime choice is not principal either: binding to `self` versus to `o` accept incomparable body sets.
- The rejection is *safe*: an over-constrained signature is still sound. The cost falls on comprehensibility, because the error message names lifetimes the programmer never wrote.
- Swift's documentation states the analogous trade-off for `~Escapable` single parameters ("copy … is not always correct"). Rather than default, it declines to infer there.

### 5. Recovering ownership from unannotated C for safe Rust

**Emre et al. 2023** (PACMPL 7, OOPSLA1; abstract only).

- They study translating raw pointers in C2Rust output into safe references via ownership and lifetime inference.
- A "novel evaluation methodology" yields findings "contradicting the conclusions of prior studies".
- Existing methods are "severely limited by a lack of precision in the Rust compiler's safety checker, causing many safe pointer manipulations to be labeled as potentially unsafe".
- Encoding a more precise analysis in a form an unmodified compiler accepts raises translatable pointers "by 75% over the baseline (from 12% to 21% of all pointers)". Derived check: 21/12 = 1.75.
- The aliasing patterns responsible and how operational safety was decided are described in the full text, which was not examined.

**Zhang, David, Yu, Wang 2023 (Crown; CAV; arXiv:2303.10515v1 full text).**

- A flow- and field-sensitive ownership analysis encoded as constraints, with ownership monotonicity, which is "stricter in certain cases than Rust's semantics". Pointers are retyped to `Box`/`Option<Box>`.
- The constraint problem is "proven to be NP-complete". "The execution time of the analysis and the rewrite for the whole benchmark suite is within 60 seconds", on an Apple M1 with 16 GB.
- 20 benchmarks, 154–537,723 LOC.
- Median reduction: 37.3% of raw pointer declarations and 62.1% of raw pointer uses. On brotli (537,723 LOC): 21.4% and 20.9%.
- "All the translated benchmarks compile". Six benchmarks with test suites pass them.
- Excluded: json-c, optipng, tinycc, on which Crown crashes on unions and variadic arguments.
- Unsupported constructs: unions, variadics, function pointers, custom allocators, sub-allocated `malloc` regions, and mutable local borrows ("requires dedicated analysis of lifetimes").
- Translation is "in theory neither sound nor complete".

Derived comparison with §2:

- Research Java inference always finds *some* valid typing (a flat one), so its question is quality.
- C→Rust recovery has no trivial fallback. The fallback is "leave it a raw pointer", and the 12–21% (Emre) and 37–62% median (Crown, different metric and benchmark set) figures measure how often that fallback is avoided.
- Neither line of work proves how many *operationally safe* programs the target discipline rejects. Emre et al. attribute part of the gap specifically to the target checker's imprecision, which is a rejection relative to operational safety.

### 6. Performance and resource footprint (L1–L6)

| Level | Quantity | Value | Source |
|---|---|---|---|
| L1 | manual AliasJava annotation rate | ≈400 lines/h (Hashtable), ≈970 lines/h (Aphyds model); derived from 934 lines/2 h 20 min and 3,550 lines/3 h 40 min | Aldrich et al. 2002 |
| L1 | Rust annotation reduction from elision | 147/169 = 87% of then-required `libstd` annotations | RFC 141 |
| L1 | manual steering of GUT encapsulation inference | ≈300 purity annotations across four programs (≈11.6 kSLOC total) | Dietl et al. 2011 |
| L1 | explicit fn-level output lifetimes still written in 2026 std/core/alloc | 129 of 1,547 output-lifetime signatures (16 redundant) | this report, execution |
| L1 | LLM token/turn budgets for annotation | not measured | — |
| L2 | build time of checkers/compilers | not measured | — |
| L3 | AliasJava inference, 408 JDK classes | `lent` 33 s, `unique` 151 s, alias params ≈30 min | Aldrich et al. 2002 |
| L3 | GUT inference | 3.5–6.2 s gen + 1.0–2.0 s solve (1.8–4.7 kSLOC); 41 s + 66 s (≈74 kSLOC) | Dietl et al. 2011 |
| L3 | Crown | whole 20-program suite within 60 s; abstract: half a million LOC in under 10 s | Zhang et al. 2023 |
| L3 | P1179 Clang prototype | ≈5% compile overhead on large LLVM TUs | P1179R1 abstract |
| L3 | stdlib elision survey | 2.9 s wall for 1,046 files (x86_64 Linux workstation, release build) | this report, execution |
| L3 | Swift lifetime inference cost | not measured | — |
| L4 | runtime cost of inferred annotations | none for Rust/Swift static annotations (erased); not measured for translated C | — |
| L5 | re-checking inferred annotations | not measured; failed for JabRef (AFU crash) | Dietl et al. 2011 |
| L6 | AliasJava solver memory | 2 GB | Aldrich et al. 2002 |
| L6 | GUT inference peak pre-GC memory | ≈160 MB (case studies), 510 MB (JabRef) | Dietl et al. 2011 |
| L6 | Crown/Laertes memory | not measured | — |

### 7. Human comprehensibility and conceptual simplicity (C1, C2)

**C1 (comprehensibility).**

- Inference that is too fine-grained harms comprehension: AliasJava's "dozens if not hundreds" of alias parameters per class.
- Defaults move the comprehension burden to error time. Rust's A1 error and RFC 141's own "cliff" concern ("When a programmer first encounters a situation that requires explicit annotations…") show it.
- P1179 hides defaults behind heuristics that the paper says may be heuristic. A reader cannot predict `ret`'s pset without applying a five-step type-directed chain.
- Swift writes every default as a `/* DEFAULT: … */` comment in tests and documentation. That is the most auditable presentation examined, but the semantics of `inout` defaults under explicit annotations is non-local.
- Distinguishing human from agent ease: an agent can mechanically expand Rust's three rules, but deciding *which* full annotation a human intended (A1 vs A2) is not recoverable from the signature.

**C2 (simplicity).**

- Rust's five default regimes enforce one invariant, "outputs do not outlive their sources", with five mechanisms that differ by syntactic position. The edition-2024 capture change unified `impl Trait` with `fn` elision's "capture what is in scope" behaviour.
- Swift's same-type and single-parameter rules are two answers to one question: which inputs may the result depend on. Its subtyping rule (dependence sets ordered by inclusion) is the uniform abstraction under which defaults become "pick the least set that type-checks". Swift avoids computing that set because it is body-dependent.
- The minimal common model is a *dependence set per output*, with defaults as declaration-local guesses. Inference makes the set body-dependent, which breaks separate compilation of interfaces, hence Swift's "added but not removed".
- These are design observations, not measured results.

### 8. Validation (V1–V4)

- **V1 (specification adequacy, non-vacuity).**
  - GUT inference treats re-checking by the independent GUT checker as the validation of inferred typings. That was done for the four case studies and could not be done for the largest program.
  - Crown validates translations by compiling them and, where available, running upstream test suites (6 benchmarks).
  - Swift's `lifetime_depend_infer.swift` is a golden test of default rules: 68 `DEFAULT:` markers and 79 expected errors.
  - The rustc probe here is a small differential test of defaults against full annotations.
- **V2 (checker/lowering soundness).**
  - AliasJava's annotation system has a type-soundness argument (subject reduction and progress, proofs in a companion report). The inference is not proved to terminate.
  - Dietl et al. 2011 is the only examined system that cross-checks inferred annotations with a separately implemented checker. Both are built on the Checker Framework and on the same GUT formalization, so they are not independent of shared-framework bugs.
- **V3 (concurrency/crash).** Not examined. Ownership for thread safety is cited as motivation by Dietl et al. but not validated there.
- **V4 (human mental models).**
  - The RFC 141 survey is a corpus measurement, not a user study.
  - No examined source measured whether programmers predict elided or default annotations correctly.

## Boundaries

- **Not examined:**
  - full texts of Huang et al. 2012, Ma and Foster 2007, Emre et al. 2023, Emre et al. 2021 ("Translating C to Safer Rust", OOPSLA 2021), and Dietl and Müller 2005 (JOT, `10.5381/jot.2005.4.8.a1`);
  - Juma, Dietl and Tripunitara, "A computational complexity analysis of tunable type inference for Generic Universe Types" (TCS 2020, `10.1016/j.tcs.2020.01.035`), seen only as bibliographic metadata and a search-engine summary reporting NP-hardness with breakable constraints and polynomial restricted cases;
  - Clang's newer intra-procedural lifetime analysis (`clang/lib/Analysis/LifetimeSafety/`, present at the pinned revision);
  - Swift's lifetime dependence evolution proposal (swift-evolution PR 2750, referenced by `LifetimeAnnotation.md`);
  - the C2Rust `c2rust-analyze` ownership analysis;
  - Laertes artifacts;
  - Rust's default object-lifetime-bound RFCs (599/1156) and edition-2024 capture RFC, of which only the compiler behaviour was observed.
- **Unknown:**
  - what fraction of real Java code AliasJava, Uno, or the 2012 framework typed *without* manual annotations at a quality level;
  - which aliasing patterns account for Emre et al.'s rejections;
  - how Swift's defaults affect acceptance rates on real code.
- **Not measured:** Swift and Clang behaviour by execution (no binaries run); P1179 default accuracy; any memory or time figure not cited in §6.
- **Known not to apply:**
  - The 87% (RFC 141) and 67.2% (this report) figures measure different populations and metrics. Neither is an acceptance rate of safe programs.
  - Crown's median reductions are not comparable to Emre et al.'s "% of all pointers": the metrics, benchmark sets, and pointer classes (Crown counts mutable non-array pointers) differ.
- **Attractive but unsupported conclusions:**
  - "Inference makes annotations unnecessary": research inference produced incomprehensible or flattened typings and needed partial annotations to steer it.
  - "Defaults are complete for common code": the A1 case is common in practice, but its frequency was not measured.
  - "The borrow checker rejects 79–88% of safe C pointer uses": Emre et al.'s 12–21% is translatability under specific methods, not a rejection rate of safe uses.
- **Unsupported:**
  - Swift `@_lifetime` outside `-enable-experimental-feature Lifetimes`;
  - PUMPKIN-style automatic repair of annotations (no examined system repairs annotations after code change);
  - `syn` 2.0.119 parsing of nightly-only syntax (113 files skipped).

## Evidence

All evidence was gathered on 2026-11-20 (UTC).

**Repositories.**

- `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/0141-lifetime-elision.md`, lines 12–13, 123, 125–126, 240–241.
- `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`: the commit of the installed `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`. Its `library/{core,alloc,std}/src` are as shipped in the toolchain's `rust-src` component.
- `swiftlang/swift-evolution` @ `f75d0a0456d72c2ca3ae418cc6a9939d32f42779`: `proposals/0446-non-escapable.md` (status header; Introduction), `proposals/0103-make-noescape-default.md`.
- `swiftlang/swift` @ `4b7146ceb4f284a962f7669f3c7780ddb5b643ff`:
  - `docs/ReferenceGuides/LifetimeAnnotation.md` (lines 59–61, 111–139, 189–235, 300ff.);
  - `lib/AST/LifetimeDependence.cpp` (lines 1506–1543, 1859–1918, 1920–1921);
  - `test/Sema/lifetime_depend_infer.swift`.
- `isocpp/CppCoreGuidelines` @ `5baf9fe252d034e8363217efc6e12c2215f2a442`: `docs/Lifetime.pdf` (P1179R1; pp. 1, 7, 28, 32; text extracted with `pdftotext -layout`).
- `llvm/llvm-project` @ `21dba964640e0a1e037caea23f6afd86dd0567e0`: `clang/lib/Sema/SemaAttr.cpp` (lines 170–222, 238–316, 318–323), `clang/include/clang/Basic/AttrDocs.td` (line 4842ff.).
- `opprop/checker-framework-inference` @ `2b6e1d9e4ea1a5e2908fecb1691700021b22d3dd`: `src/checkers/inference/InferenceMain.java` (lines 35–72).
- `opprop/universe` @ `ee75b409f57b0aaff733e0b5a3682dd2768dccc9`: `src/main/java/universe/UniverseInferenceChecker.java` (lines 15–21), `src/main/java/universe/solver/UniverseSolverEngine.java` (lines 9–18), `README.md`.
- `KomaEc/crown` @ `621904cd356b433215d5f55db39ffd71714f44ff`: `README.md` (points to the CAV 2023 paper and an `artifact` branch, not examined).

**Execution** (x86_64 Linux workstation):

- `bash support/rust_defaults/cases.sh`, output in `support/rust_defaults/cases.out`.
- `cargo build --offline --release` in `support/elision_survey` (syn `=2.0.119`, features `full`, `visit`, `parsing`), then `elision_survey <rust-src>/library/core/src <rust-src>/library/alloc/src <rust-src>/library/std/src`, output in `support/elision_survey/survey.out`. Here `<rust-src>` is `$(rustc --print sysroot)/lib/rustlib/src/rust`.
- Parse-failure messages were tallied with `SHOW_PARSE_FAILURES=1`.
- Swift test counts: `grep -c 'DEFAULT:'` and `grep -c 'expected-error'` on the pinned test file.

**Literature.** DOIs were checked against dblp on 2026-11-20. The Crossref API was not reachable from the fetch tool used.

| Work | DOI | Read |
|---|---|---|
| Aldrich, Kostadinov, Chambers, OOPSLA 2002 | 10.1145/582419.582448 | author PDF, full text: §§3.2–3.3, 4, 5.1–5.3 |
| Dietl, Ernst, Müller, ECOOP 2011 | 10.1007/978-3-642-22655-7_16 | author PDF, full text: §§1, 3, 4, 5, Figs. 8–9 |
| Huang, Dietl, Milanova, Ernst, ECOOP 2012 | 10.1007/978-3-642-31057-7_9 | author abstract page |
| Ma and Foster, OOPSLA 2007 | 10.1145/1297027.1297059 | metadata only |
| Emre, Boyland, Parekh, Schroeder, Dewey, Hardekopf, PACMPL 7 (OOPSLA1) 2023 | 10.1145/3586046 | abstract via an indexing site |
| Zhang, David, Yu, Wang, CAV 2023 | 10.1007/978-3-031-37709-9_22 | arXiv:2303.10515v1 full text: §§7–8 |

Standards and proposals without DOIs: Rust RFC 141 (2014); WG21 P1179R1 (2019-11-22); Swift SE-0446 (2024) and SE-0103 (2016).

## Revalidation

1. **Rust defaults.**
   - Rerun `support/rust_defaults/cases.sh` with a new `rustc`. Any ACCEPT/REJECT flip in A1, C1, D1, or E1 means a default changed.
   - Diff RFC 141's rules against the Rust Reference's lifetime-elision chapter if newer normative text is needed.
2. **Stdlib elision share.**
   - Rebuild `support/elision_survey` and run it on the new `rust-src`.
   - Compare the totals (1,040/1,547 ELIDED, 16 EXPLICIT_ELIDABLE) and the parse-failure count. A newer `syn` may parse more files.
3. **Swift.**
   - Diff `docs/ReferenceGuides/LifetimeAnnotation.md` §"Default lifetimes" and `lib/AST/LifetimeDependence.cpp` `inferOrDiagnose` and `lazillyInferNonEscapableResultOnParam` (the "added but not removed" comment).
   - Recount `DEFAULT:` in `test/Sema/lifetime_depend_infer.swift`.
   - Check swift-evolution for an accepted lifetime-dependence proposal that would make the rules normative.
4. **Clang.**
   - Diff `SemaAttr.cpp` `inferGslOwnerPointerAttribute` and `inferLifetimeBoundAttribute`. A move from name lists to signature-based defaults would contradict §3.2's conclusion.
   - Examine `clang/lib/Analysis/LifetimeSafety/` for defaults.
5. **Research inference.** Run `scripts/infer.sh tests/inference/Person.java` in `opprop/universe`, then re-check with `scripts/check.sh` on the annotated output. This exercises the "infer then re-check" validation path that failed on JabRef in 2011.
6. **No cheap check exists** for rejection-relative-to-safety rates. That requires the full texts and artifacts of Emre et al. 2023, which were not examined here.
