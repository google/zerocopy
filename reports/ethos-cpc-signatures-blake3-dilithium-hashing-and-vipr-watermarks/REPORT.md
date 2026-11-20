# Declarative proof-rule signatures in Ethos, sparse exact-rational certificate storage in VIPR-family checkers, and the cost of BLAKE3 plus ML-DSA authentication around real proof replay

## Summary

- **Domain obligations fit in signature text, and the trust moves with them.** The unmodified Ethos binary (cvc5/ethos `b02afbe66a4f796043ed3c5b9790cb6e7f00b9cc`, 10,538 non-blank non-comment C++ lines in `src/`) accepted and rejected three domain predicates written only as Eunoia `program` side conditions: saturating fixed-point addition, bit-field layout disjointness, and a conservative polygon-simplicity test. No checker code was added. Ethos checks that steps follow the supplied rules and nothing about the rules: a signature containing `(declare-rule oops () :conclusion false)` yields `correct` with exit status 0, also under `--require-proof-of-false`.
- **Side-condition interpretation dominates checking time.** Pairwise side conditions cost 4.6-6.3 µs per bit-field pair and 21-35 µs per polygon edge pair; a 1,024-field layout takes 3.3 s and a 512-gon 4.5 s. On cvc5-emitted Cooperating Proof Calculus (CPC) proofs, one normalisation program (`arith_poly_norm`) took 93.6% of a 5.0 s check. Loading the 504 KB CPC signature costs 48 ms before the first proof step, against a 4 ms process floor.
- **Three operational traps in Ethos verdicts.** `correct` does not mean "refutation" unless `--require-proof-of-false` is given (a proof truncated at a command boundary is still `correct`); `incomplete` (a `:sorry` rule was used) exits with status 0; and a non-terminating signature program runs without bound (1.5 GB resident after 10 s).
- **Sparse exact-rational rows are expensive unless retired.** `viprchk` stores each coefficient as a `std::map<int, mpq_class>` node: about 146-151 bytes per small-integer nonzero measured. The certificate's `index` field (last reference) cuts peak resident memory from 560 MiB to 13 MiB on a 4-million-nonzero synthetic certificate, but roughly 0.4 KB per derived row stays resident. Rational growth is real: a 2,000-step halving chain reaches 2,001-bit denominators, and a 50-term harmonic chain already needs 72 bits.
- **Authentication is not the bottleneck.** On one x86-64 core, BLAKE3 hashes at 0.60-0.66 GB/s (portable C) and 3.4-4.1 GB/s (AVX2); ML-DSA-65 reference verification takes 0.143 ms with a 58 KB stack frame and no heap. Hash plus signature verification was 0.2%-6.2% of end-to-end admission time once a real checker (`lrat-check`, Ethos) ran on the same bytes. Any multi-GB/s "checker throughput" figure can only describe the hashing stage.

## Applicability

The report combines three kinds of subject, all identified in `REPORT.json`:

1. **Generic rule-driven checking:** Ethos at the pinned development revision (self-reported version 0.2.5) driven by (a) the CPC Eunoia signature shipped in cvc5 1.4.2 under `proofs/eo/cpc` with proofs emitted by the cvc5 1.4.2 static release binary, and (b) a small domain signature written for this report (reproduced in full under Evidence). cvc5 1.4.2's helper script `contrib/get-ethos-checker` pins a different, older Ethos revision (`08e4aa4…`); the pinned head nevertheless accepted every 1.4.2 proof generated here.
2. **Cutting-plane certificate checkers:** `viprchk.cpp` and the `.vipr` format specification (versions 1.0 and 1.1) in the archived VIPR repository, example certificates from its successor repository, and the VeriPB source tree at its last GitHub revision (2022). VeriPB was read, not run.
3. **Authentication primitives and a clausal baseline:** the BLAKE3 C implementation, the pq-crystals Dilithium `ref/` implementation of FIPS 204 ML-DSA, and `lrat-check` from drat-trim replaying LRAT proofs produced from Kissat DRAT output by `drat-trim -L`.

Scope limits that change how numbers may be reused:

- All timings come from one shared 8-vCPU AMD EPYC 7B12 (Zen 2, AVX2, no AVX-512) virtual machine running other workloads; each figure is the minimum of 3-15 runs; medians were usually 1%-25% higher and up to 67% higher in passes that coincided with other load. They are not portable across microarchitectures. Compilers: GCC 15.2.0 for C, xPack GCC 14.2.0 for C++, `-O3` unless stated.
- SMT inputs, CNF formulas and VIPR certificates used for timing were generated for this report. They are not SMT-LIB, SAT-competition or MIPLIB instances. Results on MIPLIB appear only as figures published upstream.
- Ethos was built by compiling `src/` directly with `-O3 -DNDEBUG -std=gnu++17` (the flags of the upstream CMake Release profile) and linking GMP 6.2.1 statically; CMake itself was not used.
- Findings about the CPC signature apply to cvc5 1.4.2. The CAV 2026 paper describes an earlier snapshot (585 rules); the 1.4.2 tree contains 636 `declare-rule` commands.

## Findings

### 1. What Ethos trusts and what a signature can express

Basis: source + documentation + execution.

Ethos has no built-in proof rules. Its README states: "It checks that each step follows the supplied rules; it does not prove that those rules are sound." A rule is data:

```text
(declare-rule <symbol> (<typed-param>*) <assumption>? <premises>? <arguments>? <reqs>? <conclusion> <attr>*)
<reqs> ::= :requires ((<term> <term>)*)
(program <symbol> (<typed-param>*) :signature (<type>+) <type> ((<term> <term>)*)?)
```

A step succeeds when premises and arguments match the patterns under one substitution and every `:requires` pair evaluates to syntactically equal terms. A `program` is an ordered list of rewrite cases over ground terms; the first matching case fires; an application with no matching case stays unevaluated and makes the enclosing requirement fail. Evaluation of literals is provided by 56 built-in `eo::` operator kinds (`EVAL_*` in `src/kind.h`): Boolean and bitwise connectives, exact integer and rational arithmetic (`eo::add`, `eo::mul`, `eo::qdiv`, `eo::zdiv`, `eo::zmod`, `eo::pow`, `eo::log`), comparisons, string and bit-vector slicing, list operators, `eo::hash`, `eo::typeof`. Arithmetic is arbitrary precision (GMP `mpz`/`mpq` through `src/util/integer.h` and `rational.h`).

| Element | Size at the pinned revision | Role |
| --- | --- | --- |
| `src/` (45 files) | 14,250 lines, 10,538 non-blank non-comment | parser, term table, type checker, evaluator |
| `src/type_checker.cpp` | 2,028 lines | matching, program and literal evaluation |
| `plugins/`, `tools/` | 14,059 lines of C++ | experimental; README: "not part of the checker" |
| release binary built here | 815,520 bytes (`.text` 697,137; `.data` 3,304; `.bss` 1,624) | includes static GMP; libstdc++ dynamic |
| from-scratch build | 16.0 s wall, 8 parallel compile jobs | 22 translation units |

Memory model (source): terms are hash-consed through per-kind tries in `State` (`std::map<Kind, ExprTrie> d_trie`) and reference counted (`uint32_t d_rc` in `ExprValue`). Program evaluation is iterative over a heap-allocated frame vector (`std::vector<EvFrame> estack;` in `TypeChecker::evaluate`), so deep recursion in a signature program cannot overflow the native stack; it consumes heap instead. No thread primitives appear in `src/`.

The extension point for computations that Eunoia cannot express efficiently is C++: `Plugin::hasEvaluation`, `Plugin::evaluate` and `Plugin::evaluateProgram` are consulted inside the evaluator. `NEWS.md` records the direction of travel: "Removes support for oracles and the command `declare-oracle-fun`. Custom extensions are now recommended to be added via the plugin feature, which provides an interface for custom evaluation (Plugin::hasEvaluation)." A plugin is compiled-in trusted code. Derived: a domain whose side condition needs an operation outside the 56 built-ins and too slow as a rewrite program (a cryptographic hash, floating-point transcendental functions, large table lookups) forces either trusted plug-in growth or moving that check outside the rule checker.

### 2. Three domain predicates discharged without checker changes

Basis: execution (unmodified Ethos binary; signature written for this report, so the signature is the toy, the checker is real).

`domain.eo` (98 non-blank lines, 12 programs, 3 rules, 4,943 bytes) defines:

| Rule | Side condition (program) | Meaning of the derived atom |
| --- | --- | --- |
| `satadd_eval` | `clamp lo hi (a+b)` equals the claimed `r`, and `lo <= hi` | `(= (satadd lo hi a b) r)` |
| `layout_check` | every field has `0 <= o`, `w > 0`, `o+w <= total`, and all pairs are disjoint | `(layout_ok total fields)` |
| `polygon_simple` | consecutive edges not collinear; every non-adjacent edge pair strictly separated by an orientation test | `(simple_polygon points)` |

Accepted and rejected inputs behaved as intended: the valid script printed `correct`; a wrong saturation result, two overlapping fields, and a self-intersecting quadrilateral each aborted with a located message of the form

```text
Error: dom_bad_sat.eo:2.108: A step of rule satadd_eval failed to check.
Evaluation failed: (eo::requires 32767 35000 (_ (= (_ (_ (_ (satadd -32768) 32767) 30000) 5000)) 35000))
```

and exit status 134 (the checker calls `abort` through `Lexer::parseError`).

Scaling of the interpreted side conditions (minimum of 5 runs, process start included; floor for this signature is 3.96 ms and 5.1 MiB resident):

| Workload | Proof bytes | Wall time | Peak RSS | Derived unit cost |
| --- | ---: | ---: | ---: | --- |
| layout, 64 fields (2,016 pairs) | 2,875 | 13.7 ms | 5.5 MiB | 4.8 µs per pair |
| layout, 256 fields (32,640 pairs) | 11,587 | 153 ms | 9.3 MiB | 4.6 µs per pair |
| layout, 1,024 fields (523,776 pairs) | 46,915 | 3.29 s | 64 MiB | 6.3 µs per pair |
| polygon, 32 vertices (464 pairs) | 1,320 | 14.5 ms | 5.7 MiB | 23 µs per pair |
| polygon, 128 vertices (8,000 pairs) | 5,464 | 170 ms | 13.7 MiB | 21 µs per pair |
| polygon, 512 vertices (130,304 pairs) | 23,518 | 4.54 s | 132 MiB | 35 µs per pair |
| saturating add, 1,000 steps | 110,802 | 25.5 ms | 7.5 MiB | 21.5 µs per step |
| saturating add, 100,000 steps | 11,773,368 | 2.40 s | 218 MiB | 24 µs per step, 4.9 MB/s, 2.2 KiB retained per step |

Consequences. (a) Expressiveness was not the limit for these three predicates: integer comparison, products and list recursion suffice. (b) Cost is interpretive: tens of microseconds per elementary geometric predicate (a compiled integer orientation test takes nanoseconds, so the gap is an estimated three to four orders of magnitude; no compiled baseline was measured), and quadratic predicates over a few hundred elements leave any millisecond budget. (c) Memory is retained: every named step stays in the symbol table (2.2 KiB per trivial step), so a long proof stream has no bounded live set; nothing in the proof language retires a step.

### 3. A signature is trusted data: unsound rules, holes, divergence, verdict semantics

Basis: execution + documentation.

| Input | Stdout | Exit status |
| --- | --- | ---: |
| rule `oops` with no premises concluding `false`, one step using it | `correct` | 0 |
| same, with `--require-proof-of-false` | `correct` | 0 |
| rule marked `:sorry`, one step using it | `incomplete` | 0 |
| same, with `--require-proof-of-false` | `incomplete` | 0 |
| valid domain script (does not end in `false`), with `--require-proof-of-false` | error "the last proof step did not prove false at assumption level zero" | 134 |
| CPC refutation truncated to its first 1,765 of 3,531 lines | `correct` | 0 |
| same truncated proof, with `--require-proof-of-false` | error as above | 134 |
| CPC proof truncated mid-term | lexer error "Expected SMT-LIBv2 term" | 134 |
| program `spin(x) = spin(x+1)` required by a rule | none; killed after 10 s at 1.5 GB resident | n/a |

The manual states the default: "By default, Ethos does not impose any requirements on what was proven in the proof." An admission wrapper therefore must (1) pass `--require-proof-of-false` or check the proven formula itself, (2) parse stdout, because `incomplete` and `correct` share exit status 0, (3) bind the proof to the original problem with `--reference`, since otherwise `assume` commands are unconstrained, and (4) impose its own time and memory limits, because signature programs carry no fuel. The manual adds a typing caveat that widens the audit surface of a signature: "Terms in program bodies are not statically type checked. Evaluating a program may introduce non-well-typed terms if the program body is malformed."

Signature adequacy is a separate validation problem. Ten single-token mutations of `domain.eo` (flip a comparison, replace `or` by `and`, drop a bound check, and similar) were run against the four-file accept/reject suite of Finding 2: five were killed and five survived, including one that removes the `o+w <= total` bound and one that accepts touching polygon edges. Basis: execution (toy signature, real checker). The upstream response for CPC is machine checking of the rules themselves (Finding 5).

### 4. CPC proofs from cvc5 1.4.2: where checking time goes

Basis: source + execution; proof-library figures are documentation (CAV 2026 paper).

The cvc5 1.4.2 tree's `proofs/eo/cpc` holds 51 files, 14,958 lines and 539,318 bytes: 636 `declare-rule`, 247 `program` definitions, 167 `:requires` clauses, and exactly one `:sorry` rule, `trust`, whose comment reads "This rule is not sound. Any proof involving this rule should be considered incomplete." Without the `expert/` subtree the signature is 35 files and 504,486 bytes.

| Input (generated for this report) | Proof bytes | Steps | cvc5 solve+emit | Ethos wall | Ethos RSS |
| --- | ---: | ---: | ---: | ---: | ---: |
| signature only | 0 | 0 | n/a | 48.3 ms | 12.7 MiB |
| equality diamond chain, 20 links (QF_UF) | 31,154 | 360 | 0.04 s | 62.3 ms | 13.3 MiB |
| equality diamond chain, 100 links | 155,135 | 1,720 | 0.12 s | 80.0 ms | 15.6 MiB |
| pigeonhole 5 into 4 over 0/1 integers (QF_LIA) | 13,447 | 164 | 0.05 s | 61.0 ms | 13.2 MiB |
| pigeonhole 7 into 6 | 20,880 | 230 | 0.06 s | 69.9 ms | 13.7 MiB |
| strict-inequality cycle with offsets 1/3..1/52 (QF_LRA) | 80,655 | 1,066 | 0.08 s | 132.5 ms | 16.2 MiB |
| same with offsets 1/3..1/402 | 651,604 | 8,066 | 0.98 s | 5.05 s | 90.5 MiB |

Four bit-vector inputs intended to exercise bit-blasting (`bvmul` commutativity at 4 and 6 bits, `bvadd` reassociation at 8 and 32 bits) were closed by cvc5's rewriter in 8-12 steps and are not informative.

Observations. (1) Cold start is the signature: 48 ms to parse and index 504 KB, twelve times the 4 ms floor, and paid by every process. (2) Beyond start-up, equality reasoning costs about 18 µs per step (1,720 steps in 32 ms). (3) Arithmetic is dominated by one side-condition program. `ethos --stats` on the 8,066-step proof reported `arith_poly_norm: 806 applications, 5,693,512 µs (93.6%), 7,064 µs each, 2,269,141 of 2,404,306 term constructions`; on the 1,066-step proof the same rule took 41.8% at 676 µs per application. The inputs sum unit fractions, so the normaliser manipulates rationals whose reduced numerator and denominator reach 73/72 bits (50 terms) and 577/575 bits (400 terms). Checking was 5.2 times slower than solving plus proof emission on the larger instance.

Upstream scale (documentation, CAV 2026): CPC had 585 rules in 8,025 lines of Eunoia; over the SMT-LIB benchmarks cvc5 solved within 60 s (153,188, floating-point logics excluded) it produced 913.4 million steps using 427 distinct rules; proofs were generated for 152,382 and checked by Ethos for 151,571 within 600 s; the mean slowdown versus solving alone was 5.11x for generation and 7.11x for generation plus checking, ranging from 2.77x (quantifier-free strings) to 16.28x (quantifier-free bit-vectors). The same paper reports `arith_poly_norm` as 1.5% and `evaluate` as 1.6% of all steps, so side-condition-heavy rules are rare by count yet can dominate time, as measured above.

### 5. How rule signatures are validated upstream

Basis: documentation (CAV 2026 paper; cvc5 1.4.2 `Cpc.eo` header and `docs/proofs/output_cpc.rst`).

| Method | Coverage reported | Defects reported | What it does not establish |
| --- | --- | --- | --- |
| Translation of each rule to an SMT-LIB verification condition (3.5k lines of C++ extending Ethos, 1.3k lines of Eunoia) | conditions generated for 571 of 585 rules; 238 (40.6%) proved by z3 or cvc5 within 60 s | "instrumental in discovering several soundness bugs" | trusts an SMT solver; recursive side conditions mostly time out |
| SyGuS search for counterexamples to the same conditions | n/a | counterexamples to 10 rules of an earlier CPC release, "including to one of the core string proof rules"; 4 confirmed in Isabelle | absence of a counterexample is not proof |
| IsaRare translation of rewrite rules to Isabelle/HOL lemmas | 338 rules verified | 6 faulty rules found and amended | only rules expressible in the rewrite DSL |
| Reconstruction in Lean (`lean-smt`) | 180 rules in arithmetic, uninterpreted functions, quantifiers | none stated | "about 20x" slower than Ethos; validates proofs, not the signature |
| Logos, a Lean-verified checker whose rules are generated from the signature | "the fragment of CPC that is used by safe builds of cvc5"; out-of-scope inputs answer `incomplete` | none stated | cvc5's consistency check "does not build Logos or check its Lean proofs" |

The header of `Cpc.eo` in cvc5 1.4.2 makes signature changes conditional on the Lean development: "any update to this signature must be verified in Logos as well." Reading with Finding 3: unsound rules (ten found by synthesis, six by Isabelle, possibly overlapping) existed in released rule text for a checker that reported `correct` throughout. Moving checks from kernel code to rule text is only a trust reduction when the rule text itself is machine checked against a semantics.

### 6. VIPR: row storage, the `index` retirement field, and rational growth

Basis: normative (format specification) + source + execution.

Format facts. A derived constraint line is `constraint reason index`. Reasons are `asm`, `lin` (suitable linear combination dominating the stated row), `rnd` (Chvátal-Gomory rounding of an all-integer combination), `uns` (unsplit of two branches), `sol`, and in version 1.1 the incomplete forms `lin weak` and `lin incomplete`. Values are "rational numbers expressed as finite decimals or fractions". The retirement hook is the trailing integer: "`index` is -1 or is an index such that no constraint with a larger index refers to this constraint", with the stated purpose "to allow a verifier to discard the corresponding constraint from memory once the verifier has completed verifying constraint with index `index`."

Implementation facts (`code/viprchk.cpp`, 1,685 lines, one translation unit; binary 309,192 bytes with static GMP):

```cpp
class SVectorGMP : public map<int, mpq_class>
vector<Constraint> constraint; // all the constraints, including derived ones
void trash() { _trashed = true; _falsehood = false; _coefficients = nullptr;
               _rhs = 0; _assumptionList.clear(); }
```

Each row owns a red-black-tree node per nonzero holding an `int` key and a GMP rational (two heap-allocated limb arrays). Rows live in one ever-growing vector; `trash()` drops the coefficient vector when the row's declared last reference has been consumed (in `readLinComb`: `if( (constraint[index].getMaxRefIdx() <= currentConstraintIndex) && (constraint[index].getMaxRefIdx() >= 0) ) constraint[index].trash();`) or immediately after derivation when the declared index is not in the future. Assumption sets are `map<int, bool>` copied into every dependent row. A reference to a trashed row is an error ("Accessing trashed constraint"), so a wrong `index` fails closed.

Measured storage (synthetic certificates through the real `viprchk`; rows of small integer coefficients; process floor 4.7 MiB):

| Derived rows x nonzeros per row | Certificate bytes | `index` = -1 everywhere | `index` = last use | Check time |
| --- | ---: | ---: | ---: | ---: |
| 20,000 x 50 (1.0 M nonzeros) | 6.06 MB | 149 MiB | 12.9 MiB | 1.20 s / 0.85 s |
| 40,000 x 50 (2.0 M nonzeros) | 12.1 MB | 292 MiB | 19.5 MiB | 2.10 s / 1.76 s |
| 20,000 x 200 (4.0 M nonzeros) | 24.7 MB | 560 MiB | 13.0 MiB | 5.00 s / 3.72 s |

Derived: 146-151 bytes of resident memory per stored small-integer nonzero; retirement makes peak memory independent of row width but leaves about 390-440 bytes of resident memory per derived row (label string, flags, empty map, vector slot, allocator residue), so memory still grows linearly with certificate length. Throughput is about 5 MB of certificate text per second.

Rational growth (toy derivation shape, real checker): a chain `row_k = 1/2 * row_(k-1) + 1/3 * base` has denominators `3 * 2^k`, exceeding a signed 64-bit integer at k = 62 and 128 bits at k = 126. At 2,000 steps with 20 nonzeros per row, coefficients reach 2,003-bit numerators and 2,001-bit denominators, the certificate is 25.6 MB, and `viprchk` needs 0.41-0.47 s; resident memory is 19.6 MiB without retirement and 5.3 MiB with it (peak two live rows). A checker with fixed-width rationals must therefore either reject such certificates (declaring a normative bit limit the format does not have) or carry multi-limb arithmetic.

Upstream certificates in the two repositories are textbook-sized: `paper_eg3.vipr` has 3 base and 11 derived rows, 5 of them with index -1, peak 8 simultaneously live derived rows, denominators of at most 3 bits; `cg.vipr` peaks at 2 live rows of 4.

Published MIPLIB-scale figures (documentation, `experiments/README.md`; exact SCIP with certificate printing, 3,600 s limit, Xeon E5-2660 v3, 107 instances from MIPLIB 3/2003/2010, COR@L and Mittelmann sets):

| Subset | Instances | Raw size | After `viprttn` | gzip | `viprttn` time | `viprchk` time |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| easy, all | 56 | 214 MB | 72 MB | 22 MB | 25.8 s | 28.9 s |
| easy, certificate hit the 10 GB file limit | 5 | 10,286 MB | 513 MB | 159 MB | 377.5 s | 169.8 s |
| hard, all | 50 | 372 MB | 38 MB | 11 MB | 31.2 s | 15.1 s |

One instance (`nw04`) was excluded "because `viprttn` ran out of memory", and a measured 7% solver overhead is attributed to certificate collection and output. These columns are upstream aggregates, not per-instance throughputs.

### 7. VeriPB: coefficient representation and three retirement mechanisms

Basis: source (not executed).

`veripb/optimized/constraints.hpp` fixes `using CoefType = BigInt;` with `BigInt = mpz_class`, and keeps three stored-constraint representations selected by coefficient magnitude: clauses, `FixedSizeInequality<int32_t>` (`IneqLarge`) and `FixedSizeInequality<BigInt>` (`IneqBig`), classified by `enum class CoeffBound { trivial = 0, one = 1, int32 = 2, int64 = 3, unbounded = 4 }`. Pseudo-Boolean coefficients are integers, so the rational-denominator growth of Finding 6 does not arise; magnitude growth under repeated addition and multiplication still does, hence the arbitrary-precision default. Constraint lifetime is controlled by explicit proof lines rather than a per-row last-use field: `d` and `del` (delete by identifier or by lookup), level marking and wiping (`#`, `w`), and `core` marking. The pinned tree is the 2022 GitHub state, whose README calls it "a rapidly changing proof of concept"; it needs a C++ compiler, GMP, Python headers and pybind11 to build.

### 8. Clausal baseline: LRAT replay

Basis: execution (`lrat-check.c`, 509 lines of C, `.text` 11,532 bytes).

| Formula (generated) | LRAT bytes | Lemma lines | `lrat-check` wall | Throughput | Clauses added / peak live |
| --- | ---: | ---: | ---: | ---: | --- |
| pigeonhole 10 into 9 | 5,149,403 | 36,520 | 123 ms | 42 MB/s | 24,635 / 1,271 |
| random 3-SAT, 250 variables | 6,282,948 | 49,997 | 138 ms | 46 MB/s | 34,732 / 1,977 |
| random 3-SAT, 300 variables | 46,557,143 | 312,798 | 1.09 s | 43 MB/s, 286k lines/s | 212,092 / 3,686 |

Resident memory was 34.0 MiB for every input (initial table allocation dominates). Deletion lines keep the live clause set at 1.7%-12% of all clauses ever added, the clausal analogue of the VIPR `index` field. Producing these proofs cost more than checking them: Kissat 11.9 s plus `drat-trim -L` 8.7 s for the largest formula.

### 9. BLAKE3 and ML-DSA: throughput, latency and static footprint

Basis: source + execution.

BLAKE3 `c/` at version 1.8.7, single thread, `blake3_hasher_init/update/finalize`, best of two passes of seven trials:

| Build | 64 B | 1 KiB | 4 KiB | 64 KiB | 1 MiB | 16 MiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| portable C99 only | 438 MB/s | 662 | 632 | 596 | 618 | 622 |
| + SSE2 assembly | 466 | 728 | 1,718 | 1,716 | 1,676 | 1,640 |
| + SSE4.1 assembly | 487 | 844 | 1,960 | 2,108 | 2,057 | 1,822 |
| full dispatch (AVX2 selected) | 509 | 843 | 2,615 | 4,056 | 3,993 | 3,353 |

In reference-clock cycles per byte at 64 KiB: 3.8 portable, 1.3 SSE2, 1.1 SSE4.1, 0.56 AVX2. Below one 1,024-byte chunk no SIMD path helps: a 64-byte message costs 126-146 ns in every build. Footprint: `blake3.c` + `blake3_dispatch.c` + `blake3_portable.c` compile to 24,388 bytes of `.text`, 4 bytes of `.data`, no `.bss`; adding the four x86 assembly back ends gives 85,659 bytes. State is one 1,912-byte `blake3_hasher` (a 54-level chaining-value stack); the largest frames are 2,016 bytes (`blake3_hasher_init_derive_key_raw`) and 1,520 bytes (`blake3_compress_subtree_wide`); the three core files contain no allocation calls.

ML-DSA verification, pq-crystals `ref/` (the repository README states "Dilithium is standardized as FIPS 204"), 32-byte message, empty context, 3,000 verifications per mode:

| Parameter set | Public key / signature bytes | Verify min / median | p99.9 (quiet pass / loaded pass) | Stack high-water | `verify_internal` frame | Verify-only `.text` |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| mode 2 (ML-DSA-44) | 1,312 / 2,420 | 97.2 / 97.8 µs | 0.27 / 13.0 ms | 36,840 B | 35,040 B | 21,615 B |
| mode 3 (ML-DSA-65) | 1,952 / 3,309 | 142.5 / 146.5 µs | 0.33 / 1.5 ms | 58,376 B | 56,576 B | 19,428 B |
| mode 5 (ML-DSA-87) | 2,592 / 4,627 | 229.0 / 234.0 µs | 0.55 / 0.64 ms | 93,480 B | 91,680 B | 19,455 B |

The verify-only code size is a partial link with `--gc-sections` rooted at the `verify` entry point and includes Keccak. `ref/*.c` contains no heap allocation; all working storage is the stack frame, dominated by the expanded matrix `polyvecl mat[K]` (K x L polynomials of 1,024 bytes). A corrupted signature byte returned -1. The tail columns show the measurement host, not the algorithm: verification handles public inputs only, so its timing variation is not a secrecy concern, and the 13 ms outlier coincided with other workloads.

### 10. End-to-end admission latency

Basis: execution (own 60-line harness; every stage is an unmodified upstream component).

The harness hashes all input files with BLAKE3, verifies an ML-DSA-65 signature over the 32-byte digest, then forks and executes the checker on the same files. Launching an empty process (`/bin/true`) on this host costs 1.8 ms, which bounds any process-per-artifact design from below.

| Artifact | Bytes hashed | Hash, portable / AVX2 | ML-DSA-65 verify | Checker | Total (AVX2) | Hash + signature share, portable / AVX2 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| LRAT, 250 variables (CNF + proof) | 6,299,257 | 10.3 / 2.3 ms | 0.17-0.20 ms | 163 ms | 166 ms | 6.1% / 1.5% |
| LRAT, 300 variables | 46,577,066 | 77.9 / 14.5 ms | 0.16-0.18 ms | 1,176 ms | 1,191 ms | 6.2% / 1.2% |
| CPC equality chain (35 signature files + proof) | 659,621 | 1.13 / 0.35 ms | 0.17-0.21 ms | 93 ms | 93.5 ms | 1.5% / 0.6% |
| CPC rational chain, 50 terms | 585,141 | 0.98 / 0.33 ms | 0.17-0.18 ms | 154 ms | 154 ms | 0.8% / 0.3% |
| domain signature + 10,000 saturating steps | 1,142,745 | 2.26 / 0.39 ms | 0.17-0.22 ms | 247 ms | 247 ms | 0.9% / 0.2% |

Derived ordering of per-byte rates: AVX2 hashing 3-4 GB/s, portable hashing 0.6 GB/s, LRAT replay 43 MB/s, VIPR and trivial Eunoia steps 5 MB/s, CPC arithmetic 0.13 MB/s on the worst instance here. A sub-10 ms admission budget is met by hashing plus signature verification for artifacts up to about 30 MB (AVX2) or 6 MB (portable), and by none of the proof checkers above once process start (1.8-4 ms) and, for Ethos with CPC, signature load (48 ms) are counted. A resident checker with a pre-loaded signature would remove the 48 ms; that configuration was not built.

### 11. Cost, comprehensibility and validation matrix

Basis: derived from Findings 1-10 unless a cell cites documentation.

| Axis | Ethos + Eunoia signature | viprchk / VeriPB | lrat-check | BLAKE3 + ML-DSA |
| --- | --- | --- | --- | --- |
| Authoring effort | CPC: 8,025 lines for 585 rules (about 14 lines per rule; documentation). Domain signature here: 98 lines for 3 rules, plus generators | proof logging lives in the solver; upstream measured 7% solver overhead | solver emits DRAT; LRAT hints by `drat-trim` | none per artifact |
| Tool build | 16 s (8 jobs); cvc5 itself is about 363k lines of C++ (documentation), not built here | viprchk: one file, seconds; VeriPB needs Python and C++ toolchains | under 1 s | under 1 s |
| Elaboration and interactive latency | cvc5 proof emission 5.11x solving (documentation); 48 ms signature load exceeds a 50 ms keystroke budget alone | certificate printing inside the MIP solver | `drat-trim -L` took 0.2-8.7 s here | n/a |
| Execution of the authentication path | n/a | n/a | n/a | 0.56-3.8 cycles/byte; 97-229 µs per verify |
| Check speed | 42k trivial steps/s; 18-620 µs per CPC step | about 5 MB/s | 43-46 MB/s | 0.6-4 GB/s |
| Memory and size | 5 MiB floor, 13 MiB with CPC, unbounded growth; 0.8 MB binary | 146-151 B per nonzero; 0.3 MB binary | 34 MiB flat; 22 KB binary | 1.9 KB state; 36-93 KB stack; 20-25 KB code each |
| Parallelism | single-threaded | single-threaded | single-threaded | BLAKE3 tree mode exists; not used |

Human comprehensibility. A reviewer of a Eunoia rule must hold in mind: pattern matching under one substitution, first-match ordering of program cases, strict evaluation of every operator except `eo::ite`, "stuck" (unevaluated) terms as the failure mode, and the attribute-driven desugaring of n-ary operators. Rule soundness is non-local: `polygon_simple` is four lines, but its meaning lives in nine programs. Diagnostics are legible for the failing requirement (the message prints both sides) and silent about which program case failed to match. The verdict vocabulary is a footgun: `correct` reads as "the claim holds" yet means "every step matched a rule". For VIPR the mental model is smaller (five reason kinds and one lifetime integer), and an incorrect lifetime fails closed.

Conceptual economy. Eunoia reaches arithmetic, bit-vector and geometric side conditions with one mechanism (rewrite programs over literals), so the three domain predicates are ordinary cases rather than kernel special cases. The hidden costs sit in three adapters: the 56 trusted built-in evaluators, the signature text (trusted, unbounded, 0.5 MB for CPC), and the verdict wrapper obligations of Finding 3. For constraint lifetime, three designs enforce the same invariant ("no later step reads a retired row"): VIPR's per-row last-use index, LRAT's deletion lines, and VeriPB's deletion plus levels plus core marking; only the first two are single mechanisms.

Validation coverage observed. Specification adequacy: upstream rule verification (Finding 5) and the 5-of-10 mutant kill rate here. Checker robustness: `NEWS.md` for the next Ethos release lists fixes for "crashes on builtin operators applied to too few arguments" and "a bug where deleting a term could remove other live terms from the term table, so that syntactically equal terms were treated as distinct", evidence that the generic kernel itself is still being debugged; the truncation and tamper cases of Finding 3, a tampered multiplier in `paper_eg3.vipr` (rejected with the computed difference printed, exit 255) and a half-length LRAT proof (exit 1) are the only negative tests run here.

## Boundaries

- **Not examined: MIPLIB-scale VIPR certificates.** No certificate for a MIPLIB instance was available from the pinned repositories, and no exact MIP solver was built. Live-row watermarks, per-row nonzero counts and rational bit lengths on real branch-and-cut derivations are therefore unmeasured; Finding 6 gives per-nonzero storage costs, synthetic growth shapes and upstream aggregate sizes only. The synthetic rows contain no `rnd`, `uns` or `asm` reasons.
- **Not examined: VeriPB execution, `viprttn`, `viprcomp`, `vipr2html`.** VeriPB's coefficient and deletion behaviour is from source reading of a 2022 tree; the actively developed successor is outside the pinned subject.
- **Not examined: CPC proofs for SMT-LIB benchmarks, bit-blasting, strings, quantifiers.** The six SMT inputs were generated here and four more were trivial. The 93.6% share of `arith_poly_norm` is a property of rational-heavy inputs, not of CPC proofs in general; the published step mix puts that rule at 1.5% of steps.
- **Not examined: Logos, lean-smt, IsaRare, the SMT verification-condition translation.** Their coverage figures are quoted from upstream; none was built or run. Whether the 636 rules of cvc5 1.4.2 are all covered by a machine-checked proof is unknown from the evidence here.
- **Not examined: plugin-based or compiled signatures.** The experimental `plugins/` tree (including compilation of signatures to C++ and a Rust checker intended for translation to Lean) was not built, so the achievable speed-up over interpreted side conditions is unknown.
- **Not examined: energy, non-x86 targets, AVX-512, NEON, the AVX2 Dilithium implementation, multi-threaded BLAKE3.** The host has no AVX-512; "full dispatch" selected AVX2.
- **Not examined: systematic malformed-input fuzzing or differential checking between independent checkers.** Negative testing here is a handful of hand-made cases.
- **Known not to apply: side-channel leakage tests for the admission path.** Hashing and signature verification operate on public data only; fixed-versus-random power or timing analysis concerns signing and key generation, which admission does not perform. Weak-memory and crash-consistency exploration likewise has no target in single-threaded, read-only checkers, apart from the truncation behaviour in Finding 3.
- **Known not to apply: physical-plant falsification, hardware-in-the-loop replay and operator studies.** No human-subject evidence on reading Eunoia rules or VIPR certificates was found or produced; the comprehensibility remarks in Finding 11 are analysis, not measurement.
- **Unsupported by Ethos:** resource limits on program evaluation, statically typed program bodies, a verdict tied to a stated goal without `--require-proof-of-false` and `--reference`, and retirement of earlier proof steps.
- **Stronger conclusions the evidence does not support.** (1) "Declarative signatures remove domain code from the trusted base": they relocate it into trusted rule text plus a growing evaluator. (2) "Ethos is too slow for admission": only interpreted quadratic side conditions and rational-heavy normalisation were slow; equality steps cost 18 µs. (3) "Retirement bounds VIPR memory": it bounds coefficient storage, not the row-header array. (4) Any ranking of hash or signature speed on other processors.

## Evidence

Sources (Git paths are relative to the pinned revisions in `REPORT.json`):

- cvc5/ethos `b02afbe66a4f796043ed3c5b9790cb6e7f00b9cc`: `README.md`; `user_manual.md` (sections "Declaring Proof Rules", "Programs", "Computational Operators", "Checker Response", "Command line options"); `NEWS.md`; `src/kind.h`; `src/expr.h` (`d_rc`); `src/state.h` (`d_trie`); `src/type_checker.cpp` (`TypeChecker::evaluate`, `evaluateProgramInternal`); `src/plugin.h`.
- cvc5/cvc5 `282d5e0c84baf49c780704c532f87ba66d8b513d`: `proofs/eo/cpc/**/*.eo`; `proofs/eo/cpc/Cpc.eo` (header, rule `trust`); `docs/proofs/output_cpc.rst`; `contrib/get-ethos-checker`.
- ambros-gleixner/VIPR `f221c3fd2274e8e859e8e24505278d6f7c1bb8ff`: `cert_spec_v1_1.md`; `code/viprchk.cpp` (`SVectorGMP`, `Constraint::trash`, `readLinComb`); `code/paper_eg3.vipr`; `experiments/README.md`.
- scipopt/vipr `99eec197a49b2bd9ad33c1f4c7afabe93caa6511`: `examples/cg.vipr`, `ip.vipr`, `infeasbb.vipr`.
- StephanGocht/VeriPB `01b7b5088c8a67f1611427174501191bc5f5b365`: `README.rst`; `veripb/optimized/constraints.hpp`; `veripb/optimized/BigInt.hpp`; `veripb/rules.py`.
- BLAKE3-team/BLAKE3 `657284b1fa4c4378aa7422b4450dcb5c2c9052fc`: `c/blake3.h`, `c/blake3.c`, `c/blake3_dispatch.c`, `c/blake3_portable.c`, `c/blake3_{sse2,sse41,avx2,avx512}_x86-64_unix.S`.
- pq-crystals/dilithium `d35ba3fe5449bee3e6d43e1f296c3ca818bd36be`: `ref/sign.c` (`crypto_sign_verify_internal`), `ref/params.h`, `ref/Makefile`, `README.md`.
- marijnheule/drat-trim `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`: `lrat-check.c`, `drat-trim.c`. arminbiere/kissat `8af8e56f174b778aef3aa45af9f739b2a5f492c2` (version 4.0.4). alisw/GMP `2bbd52703e5af82509773264bfbd20ff8464804f` (GMP 6.2.1, built with `--enable-cxx --disable-shared`).
- Literature: CAV 2026 paper (author copy read in full; DOI and pagination confirmed against a university publication record); IPCO 2017 paper (publisher landing page); NIST FIPS 204 landing page (published 2024-08-13).
- Tool artifacts: xPack GCC 14.2.0-2 `xpack-gcc-14.2.0-2-linux-x64.tar.gz`, sha256 `d27b09c677cefde24bdaacdde045d35ea1a391fbb5b4525d057e1974af912c4d`; cvc5 1.4.2 static zip, sha256 in `REPORT.json`.

The domain signature used in Findings 2 and 3 (complete; comment lines removed, so 4,088 bytes here against the 4,943-byte, 98-line file that was measured):

```smt
(declare-const Int Type)
(declare-consts <numeral> Int)
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(declare-const satadd (-> Int Int Int Int Int))
(program clamp ((lo Int) (hi Int) (v Int))
  :signature (Int Int Int) Int
  (((clamp lo hi v) (eo::ite (eo::gt lo v) lo (eo::ite (eo::gt v hi) hi v)))))
(declare-rule satadd_eval ((lo Int) (hi Int) (a Int) (b Int) (r Int))
  :args (lo hi a b r)
  :requires (((eo::gt lo hi) false) ((clamp lo hi (eo::add a b)) r))
  :conclusion (= (satadd lo hi a b) r))
(declare-const Field Type)
(declare-const field (-> Int Int Field))
(declare-const FieldList Type)
(declare-const fnil FieldList)
(declare-const fcons (-> Field FieldList FieldList))
(declare-const layout_ok (-> Int FieldList Bool))
(program disjoint1 ((o Int) (w Int) (o2 Int) (w2 Int) (rest FieldList))
  :signature (Int Int FieldList) Bool
  (((disjoint1 o w fnil) true)
   ((disjoint1 o w (fcons (field o2 w2) rest))
      (eo::and (eo::or (eo::not (eo::gt (eo::add o w) o2)) (eo::not (eo::gt (eo::add o2 w2) o)))
               (disjoint1 o w rest)))))
(program layout_chk ((total Int) (o Int) (w Int) (rest FieldList))
  :signature (Int FieldList) Bool
  (((layout_chk total fnil) true)
   ((layout_chk total (fcons (field o w) rest))
      (eo::and (eo::and (eo::not (eo::is_neg o)) (eo::and (eo::gt w 0) (eo::not (eo::gt (eo::add o w) total))))
               (eo::and (disjoint1 o w rest) (layout_chk total rest))))))
(declare-rule layout_check ((total Int) (L FieldList))
  :args (total L)
  :requires (((layout_chk total L) true))
  :conclusion (layout_ok total L))
(declare-const Pt Type)
(declare-const pt (-> Int Int Pt))
(declare-const PtList Type)
(declare-const pnil PtList)
(declare-const pcons (-> Pt PtList PtList))
(declare-const Seg Type)
(declare-const seg (-> Pt Pt Seg))
(declare-const SegList Type)
(declare-const snil SegList)
(declare-const scons (-> Seg SegList SegList))
(declare-const simple_polygon (-> PtList Bool))
(program orient ((px Int) (py Int) (qx Int) (qy Int) (rx Int) (ry Int))
  :signature (Pt Pt Pt) Int
  (((orient (pt px py) (pt qx qy) (pt rx ry))
      (eo::add (eo::mul (eo::add qx (eo::neg px)) (eo::add ry (eo::neg py)))
               (eo::neg (eo::mul (eo::add qy (eo::neg py)) (eo::add rx (eo::neg px))))))))
(program same_side ((a Int) (b Int))
  :signature (Int Int) Bool
  (((same_side a b) (eo::gt (eo::mul a b) 0))))
(program apart ((p1 Pt) (p2 Pt) (p3 Pt) (p4 Pt))
  :signature (Seg Seg) Bool
  (((apart (seg p1 p2) (seg p3 p4))
      (eo::or (same_side (orient p1 p2 p3) (orient p1 p2 p4))
              (same_side (orient p3 p4 p1) (orient p3 p4 p2))))))
(program edges ((first Pt) (p Pt) (q Pt) (rest PtList))
  :signature (Pt PtList) SegList
  (((edges first (pcons p pnil)) (scons (seg p first) snil))
   ((edges first (pcons p (pcons q rest))) (scons (seg p q) (edges first (pcons q rest))))))
(program turn_ok ((p Pt) (q Pt) (r Pt))
  :signature (Seg Seg) Bool
  (((turn_ok (seg p q) (seg q r)) (eo::not (eo::eq (orient p q r) 0)))))
(program apart_all ((e Seg) (x Seg) (rest SegList) (skipLast Bool))
  :signature (Seg SegList Bool) Bool
  (((apart_all e snil skipLast) true)
   ((apart_all e (scons x snil) true) true)
   ((apart_all e (scons x rest) skipLast) (eo::and (apart e x) (apart_all e rest skipLast)))))
(program poly_walk ((e Seg) (n Seg) (rest SegList) (isFirst Bool) (firstE Seg))
  :signature (SegList Bool Seg) Bool
  (((poly_walk (scons e snil) isFirst firstE) (turn_ok e firstE))
   ((poly_walk (scons e (scons n rest)) isFirst firstE)
      (eo::and (eo::and (turn_ok e n) (apart_all e rest isFirst))
               (poly_walk (scons n rest) false firstE)))))
(program first_edge ((e Seg) (rest SegList))
  :signature (SegList) Seg
  (((first_edge (scons e rest)) e)))
(program poly_chk ((p Pt) (rest PtList))
  :signature (PtList) Bool
  (((poly_chk (pcons p rest))
      (eo::define ((E (edges p (pcons p rest)))) (poly_walk E true (first_edge E))))))
(declare-rule polygon_simple ((P PtList))
  :args (P)
  :requires (((poly_chk P) true))
  :conclusion (simple_polygon P))
```

Workload definitions. Layout with N fields: fields `(field 8*i 8)` for i < N in a container of `8*N` bits. Polygon with N vertices: points `(pt i i*i)` for i < N (strictly convex). Saturating add with K steps: step i claims `satadd -32768 32767 (30000-i) (2*i)` equals the clamped sum. Each step has the shape `(step @s (= (satadd -32768 32767 30000 5000) 32767) :rule satadd_eval :args (-32768 32767 30000 5000 32767))`. Rejected cases: result 35000 for the step just shown; fields `(0,8)` and `(7,4)` in 32 bits; points `(0,0) (4,3) (4,0) (0,3)`. Mutants: one textual replacement each in `clamp`, the `satadd_eval` requirement list, `disjoint1`, `layout_chk` (two), `same_side`, `apart`, `turn_ok`, the `poly_walk` start flag, and `orient`.

SMT inputs. Equality diamond with n links: for i < n assert `(or (and (= x_i y_i) (= y_i x_(i+1))) (and (= x_i z_i) (= z_i x_(i+1))))`, then `(not (= x_0 x_n))`. Integer pigeonhole: n+1 pigeons, n holes, variables bounded to [0,1], row sums at least 1, column sums at most 1. Rational chain with n terms: `r_i + 1/(i+3) < r_(i+1)` for i < n and `r_n < r_0`. Proof files are the line `(include ".../proofs/eo/cpc/Cpc.eo")` followed by the output of `cvc5 --dump-proofs file.smt2` without its first two and last lines, as `contrib/get-ethos-checker` does.

VIPR generators. Common header: D variables, none integer, objective equal to base row 0, 8 dense base rows `sum_j (1 + (7*i + 13*j) mod 9) x_j >= i+1`, `RTP range 1 inf`, and a final row `FINAL G 1 OBJ { lin 1 0 1 } -1`. "Flat": derived row k is `1*base[k mod 8] + 1*base[(k+1) mod 8]` with index -1 or its own index. "Chain": row k is `1/2*row[k-1] + 1/3*base[k mod 8]` with index -1 or k+1. An earlier variant with `RTP range -inf inf` and no final row was reported as failed by `viprchk` (exit 255, no message), which is why the final row exists.

Commands (paths shortened; `rss` is a 40-line C launcher that forks, executes and reads `wait4` peak RSS, used because a Python launcher reports a floor of about 12 MiB for any child):

```text
g++ -O3 -DNDEBUG -std=gnu++17 -Isrc -I$GMP/include -c src/*.cpp src/base/*.cpp src/util/*.cpp
g++ -O3 *.o $GMP/lib/libgmpxx.a $GMP/lib/libgmp.a -o ethos
g++ -O2 -DNDEBUG -std=c++17 -I$GMP/include code/viprchk.cpp $GMP/lib/libgmpxx.a $GMP/lib/libgmp.a -o viprchk
gcc -O2 lrat-check.c -o lrat-check ; gcc -O2 drat-trim.c -o drat-trim
kissat -q --no-binary f.cnf f.drat ; drat-trim f.cnf f.drat -L f.lrat ; lrat-check f.cnf f.lrat
gcc -O3 -std=c99 -DBLAKE3_NO_SSE2 -DBLAKE3_NO_SSE41 -DBLAKE3_NO_AVX2 -DBLAKE3_NO_AVX512 bench.c blake3.c blake3_dispatch.c blake3_portable.c
gcc -O3 -std=c99 bench.c blake3.c blake3_dispatch.c blake3_portable.c blake3_{sse2,sse41,avx2,avx512}_x86-64_unix.S
gcc -O3 -fomit-frame-pointer -DDILITHIUM_MODE=3 bench.c sign.c packing.c polyvec.c poly.c ntt.c reduce.c rounding.c fips202.c symmetric-shake.c randombytes.c
ld -r --gc-sections -u pqcrystals_dilithium3_ref_verify -e pqcrystals_dilithium3_ref_verify *.o -o verify_closure.o ; size verify_closure.o
ethos --stats proof.cpc ; ethos --require-proof-of-false proof.cpc ; rss 5 ethos proof.cpc
```

Selected raw outputs:

```text
empty-ish domain signature (domain.eo, 4943 B): runs=15 min=3.96ms median=4.36ms maxrss=5184KiB exit=0
CPC signature cvc5-1.4.2 (504486 B without expert/): runs=15 min=48.26ms median=50.62ms maxrss=13048KiB exit=0
layout N=1024 bytes=46915: runs=5 min=3292.70ms median=3834.74ms maxrss=65744KiB exit=0
polygon N=512 bytes=23518: runs=5 min=4542.26ms median=4744.17ms maxrss=134740KiB exit=0
satadd K=100000 bytes=11773368: runs=5 min=2402.81ms median=2470.95ms maxrss=223388KiB exit=0
lra_chain_400 bytes=651604 steps=8066: runs=5 min=5045.30ms median=5392.28ms maxrss=92624KiB exit=0
flat N=20000 D=200 retire=0 bytes=24749783: runs=3 min=5002.49ms median=5336.32ms maxrss=573552KiB exit=0
flat N=20000 D=200 retire=1 bytes=24798705: runs=3 min=3723.21ms median=4234.04ms maxrss=13344KiB exit=0
chain N=2000 D=20 retire=1 bytes=25608347: runs=3 min=467.84ms median=538.02ms maxrss=5384KiB exit=0
r3_300 cnf=19923 lrat=46557143 lines=312798: runs=5 min=1093.48ms median=1166.83ms maxrss=34924KiB exit=0
c Added clauses = 212092.  Deleted clauses = 212042.  Max live clauses = 3686
Dilithium3 pk=1952 sk=4032 sig=3309 verify ns: min=142520 median=146510 p99=263750 p99.9=329990 stack_high_water=58376 B
LRAT r3_300 (cnf+lrat): bytes=46577066 hash=14.471ms (3219 MB/s) mldsa65_verify=0.164ms(rc=0) checker=1176.18ms total=1190.81ms hash+sig share=1.23%
killed 5 of 10
```

Report synthesis versus source fact: unit costs ("per pair", "per nonzero", "per step") are differences against the measured process floor divided by element counts; they are derived, not printed by any tool. All evidence was acquired on the observation date in `REPORT.json`.

## Revalidation

- **Verdict semantics (Finding 3):** run Ethos on the three-line script `(declare-rule oops () :conclusion false)` / `(step @f false :rule oops)` and on a `:sorry` variant, with and without `--require-proof-of-false`, and read both stdout and the exit status. A change in any of the four outcomes invalidates the wrapper guidance. Then check that `user_manual.md` section "Checker Response" still says no requirement is placed on what was proven.
- **Signature load and step cost (Findings 2, 4):** time `ethos` on a file containing only `(include ".../Cpc.eo")` and on a 10,000-step saturating-add script; compare with 48 ms and 22 µs per step scaled by the host. For the arithmetic hot spot, run `ethos --stats` on the 400-term rational chain and read the `arith_poly_norm` row.
- **Expressiveness boundary (Finding 1):** diff `src/kind.h` for the `EVAL_*` list and `src/plugin.h` for `hasEvaluation`; reappearance of oracles or a fuel or timeout option in `user_manual.md` would change Findings 1 and 3.
- **CPC signature inventory (Finding 4):** `grep -c '^(declare-rule'`, `'^(program'` and `':sorry'` over `proofs/eo/cpc` at the cvc5 revision of interest.
- **VIPR storage (Finding 6):** confirm `class SVectorGMP : public map<int, mpq_class>` and `Constraint::trash` in `viprchk.cpp`; generate the 20,000 x 200 flat certificate with and without last-use indices and compare peak RSS (560 MiB versus 13 MiB here). For another checker, the discriminating test is whether peak RSS depends on row width once indices are tight.
- **Rational growth:** the halving chain needs no checker at all: `3 * 2^k` against the integer width of interest.
- **Authentication share (Findings 9, 10):** rebuild the BLAKE3 benchmark in portable and full-dispatch form and run the ML-DSA verify loop; then compare hash time for the artifact size of interest with the checker's wall time on the same artifact. If the checker is not at least an order of magnitude slower than hashing, the conclusion of Finding 10 needs re-examination for that checker.
- **Not cheaply revalidated:** MIPLIB-scale watermarks and SMT-LIB-scale CPC behaviour require building an exact MIP solver with certificate output and running a benchmark library; the upstream tables quoted here are the only evidence at that scale.
