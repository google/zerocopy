# Specification Mutation, Relation-Directed Property Testing, Metamorphic Compiler Validation, and Verifier Soundness Fuzzing

## Summary

Formal proofs establish only conditional implications of the form $\text{TCB} \land \text{EnvAssumptions} \land \text{Pre}(x) \implies \text{Post}(x, f(x))$. In production verification, compiler, and solver toolchains, catastrophic silent defects concentrate at the four unproved premises of that implication: (1) contradictory preconditions or underconstrained postconditions that render theorems vacuously or trivially true; (2) unverified front-end parsers, elaborators, macros, and back-end assembly printers flanking a mechanized middle-end; (3) soundness defects inside SMT decision procedures (`sat`/`unsat` flip bugs under incremental `push`/`pop` or theory combination); and (4) environment-manipulation escapes or kernel reduction bugs inside proof assistants themselves (`Basis: source + derived`).

Across the seventeen pinned upstream systems examined in this report, closing those four soundness gaps without inflating the trusted computing base (`TCB`) requires composing four orthogonal validation mechanisms (`Basis: source + execution + derived`):

1. **Inductive Relation-Directed Generation and Choice-Stream Shrinking (`QuickChick`, `PropEr`, `Hypothesis`, `Proptest`)**: Replacing naive type-driven generate-and-filter (`0.0%` hit rate on binary search trees of size $\ge 6$ over `5,000` trials) with unification-derived constrained generators (`QuickChick` `GenSizedSuchThat`, achieving `52.88%` hit rate in `55.36 ms` while satisfying `CorrectSizedST` soundness and completeness `[set x | exists s, semProdOpt (g s) x] <--> P`), paired with internal shortlex byte-stream reduction (`Hypothesis` choice sequences) so dependent `flat_map` and stateful command sequences shrink to canonical minimal counterexamples (`[[0, 0], 1]` vs. `Proptest` source-tree stagnation at length `4`).
2. **Conjunctive Non-Vacuity Witnesses Plus Dual Mutation Adequacy (`QuickChick` `Mutation.v`, `cargo-mutants`, `mCoq`, `Clover`)**: Existential witness inhabitation ($\exists x.\; \text{Pre}(x) \land \text{Post}(x, f(x))$) catches contradictory preconditions (`0/6` mutant kill rate on `len(xs) > 5 && len(xs) < 2`), but **fails completely** to detect weak or tautological postconditions (`len(out) == len(out)` or ordered-subset checks that omit completeness, where `WitnessExists == true` yet `33.3%`–`100.0%` of buggy implementation mutants still verify!). Soundness of a specification itself requires killing a systematic suite of implementation and specification mutants.
3. **UB-Free Differential, Metamorphic, and Single-Source Interpreter Bisimulation (`Csmith`, `CompCert`, `YARPGen`, `EMI`, `Alive2`, `SpecTec`, `Sail`)**: Validating unverified parser/printer boundaries (`CompCert` `cparser/Elab.ml` prior to `Csyntax.program`, where `Csmith` exposed `6` front-end bugs despite `0` bugs in the mechanized `Clight -> Asm` pipeline), branch-free loop/SIMD optimizations (`YARPGen` compile-time interval policies avoiding `Csmith` safe-math branches), profile-guided dead-code Equivalence Modulo Inputs (`EMI`), byte-exact `poison`/`undef` SMT translation validation (`Alive2`), and single-source prose/prover/interpreter generation (`SpecTec`, `Sail`).
4. **Oracle-Free Semantic Fusion, Stateful API Fuzzing, and Multi-Kernel Proof Replay (`yinyang`, `Murxla`, `Z3`, `cvc5`, `lean4checker`, `nanoda_lib`)**: Fusing known-`sat` or known-`unsat` seed formulas via invertible algebraic couplings (`yinyang`), fuzzing stateful incremental solver APIs with grammar-aware delta debugging (`Murxla`), and replaying serialized proof environments from an empty kernel (`lean4checker` regenerating constructors/recursors from `inductive` declarations; `nanoda_lib` re-checking exported declarations in an independent Rust kernel) to block metaprogramming environment-injection escapes (`AddFalseConstructor.lean`).

---

## Applicability

The findings in this report apply to formal verification frameworks, optimizing compilers, ISA semantics toolchains, SMT solvers, and interactive theorem provers represented by the seventeen concrete upstream revisions in `REPORT.json` (`Basis: source + documentation`):

- **Property-Based & Stateful Counterexample Generation**: `QuickChick/QuickChick` (`6b98c9beca3ff5cfb645f6aa4e35a8146081f128`, Rocq/Coq OCaml plugin + `quickChickTool`), `proper-testing/proper` (`9b0da8778206b0f264c942fabca45d0f9bda2e7b`, Erlang symbolic/dynamic state-machine PBT), `HypothesisWorks/hypothesis` (`9ea72564ee553a3aa603ad9f2997fbbdcd096d50`, internal choice-sequence test-case reduction), and `proptest-rs/proptest` (`70cf37d46b7d83393b6ed94c611f8c52209f585d`, Rust `Strategy`/`ValueTree` combinators).
- **Mutation Adequacy for Code and Specifications**: `sourcefrog/cargo-mutants` (`6c720ae82a1784b84cfa06066f7b0d59ed1798d0`, Rust return-type and expression AST mutation runner) alongside `QuickChick` `src/Mutation.v` and `quickChickTool` comment-directed Gallina/C mutation testing, contextualized against `mCoq` (`DOI: 10.1109/ASE.2019.00057`) and `Clover` (`DOI: 10.1007/978-3-031-65112-0_7`).
- **Compiler, Translation-Validation & Specification Bisimulation Toolchains**: `csmith-project/csmith` (`0cdc710315cfee9035e22ef4363ca479270d1934`), `intel/yarpgen` (`1adb290f453505838f3aa33dc571f292b0c1810f`), `AliveToolkit/alive2` (`3bdd4f5e1cefa47057e93110e707acd11cfe08e4`), `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`), `Wasm-DSL/spectec` (`acc6e834ff403c82554d081237f327346190ad96`), and `rems-project/sail` (`97aa617dcd4d01575f773cb58ea1e8686858c8c2`).
- **SMT Solver & Proof-Kernel Soundness Auditing**: `testsmt/yinyang` (`5ce963290b682fccdb7f27464de0e5c0d02047c5`, bundling `yinyang`, `opfuzz`, and `typefuzz`), `murxla/murxla` (`d32047c4c00a9c93ff9e564eeed5196f517e5cff`) targeting `Z3Prover/z3` (`bcad05a7bf7dd9b82bd7a665018e0480e737264b`) and `cvc5/cvc5` (`eb203989c35e47030d0aa37afafb8458cb54e5e9`), plus Lean 4 environment/export verifiers `leanprover/lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`) and `ammkrn/nanoda_lib` (`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`).

These subjects form a **layered meta-verification stack**: property-based and mutation tools audit specifications above the theorem boundary, differential/metamorphic generators test lowering pipelines across unverified compiler/ISA seams, and semantic-fusion/external-kernel checkers audit the underlying SMT and type-theory engines (`Basis: derived`). Execution measurements in this report were collected on Linux `x86_64` using Python `3.11+` standard-library micro-probes (`Basis: execution`).

---

## Findings

### 1. Inductive Relation-Directed Generation and Shrinking Semantics

#### 1.1 Sound and Complete Constrained Generation (`QuickChick`)
Naive property-based testing separates unconstrained structural generation (`arbitrary : G A`) from boolean precondition filtering (`implication P x ==> Q x`). Whenever `P` encodes a sparse structural invariant—such as well-typed $\lambda$-terms, red-black height/color invariants, or ordered binary search trees `BST lo hi t`—the acceptance probability decays exponentially with tree size $s$, starving the consequent `Q` of non-trivial inputs and creating **precondition starvation vacuity** (`Basis: source + execution`).

In `QuickChick/QuickChick` (`src/DependentClasses.v:13-77`), dependent constrained generators replace post-hoc filtering with sized option producers `arbitrarySizeST : nat -> G (option A)` governed by a foundational correctness biconditional (`Basis: source`):

```coq
Class CorrectSizedST {A : Type} (P : A -> Prop) {G} `{Producer G} (g : nat -> G (option A)) :=
  { corrST : [ set x | exists s, semProdOpt (g s) x ] <--> P }.

Class GenSizedSuchThat (A : Type) (P : A -> Prop) :=
  { arbitrarySizeST : nat -> G (option A) }.
```

Here `corrST` requires both **generator soundness** ($\forall s, x,\; x \in \text{semProdOpt}(g\;s) \implies P(x)$, never emitting false counterexamples) and **generator completeness** ($\forall x,\; P(x) \implies \exists s,\; x \in \text{semProdOpt}(g\;s)$, guaranteeing non-zero sampling support for every inhabitant of `P` at sufficient fuel `s`, accompanied by `SizeMonotonicOpt` at `src/DependentClasses.v:31-41`). Inside the OCaml derivation plugin (`plugin/arbitrarySizedST.ml:10-90` and `plugin/depDriver.ml.cppo`), `Derive ArbitrarySizedSuchThat for (fun x => P p1 ... pn x)` compiles inductive relations directly into backtracking monadic generators (`bindGenOpt`, `suchThatMaybeOpt`, `construct_match_with_return`, `Lampropoulos et al., POPL 2018, DOI: 10.1145/3158133`): input indices `p_i` become pattern-matched generator parameters, unbound existential variables invoke `instantiate_existential_methodST` (`arbitrarySizedST.ml:25-30`), and equality constraints unify inline rather than sampling unconstrained terms (`Basis: source + documentation`).

Executing our deterministic `5,000`-trial micro-probe (`## Revalidation` Probe 1, seed `20261119`) on binary search trees over keys `[0, 31]` with recursion depth `5` and target node count $\ge 6$ demonstrates the exact quantitative cliff (`Basis: execution`):
- **Unconstrained tree generation + `is_bst` filter**: `0 / 5,000` valid trees (`0.000%` yield in `38.63 ms`) — `100%` of test budget is discarded before reaching the system under test.
- **Relation-directed `gen_directed_bst(size, lo, hi)`**: `2,644 / 5,000` valid trees with $\ge 6$ nodes (`52.880%` yield in `55.36 ms`), immediately exercising deep rebalancing and deletion paths.

#### 1.2 Symbolic-vs-Dynamic State Machines (`PropEr`) and Value-Tree vs. Choice-Stream Shrinking (`Proptest` vs. `Hypothesis`)
When testing stateful APIs (concurrent caches, file systems, incremental solvers), raw counterexample traces typically span `40–200` interleaved calls. Two architectural decisions govern whether counterexamples shrink cleanly (`Basis: source`):

1. **Symbolic Variable Decoupling (`proper-testing/proper`, `src/proper_statem.erl:94-140, 279-293`)**: `PropEr` splits command generation from live execution using symbolic call terms `{'set', {'var', N}, {'call', Mod, Fun, Args}}`. During generation *and* shrinking, `command(S)`, `precondition(S, Call)`, and `next_state(S, Res, Call)` operate purely over `symbolic_state()` and opaque result handles `{'var', N}` without touching the system under test. Candidate subsequences produced by `shrink_list` are cheap-checked against `precondition/2` symbolically; only valid shrunk command sequences execute against the real system to evaluate `postcondition(DynamicState, Call, ConcreteRes)` (`src/proper_statem.erl:125-131`, `Papadakis & Sagonas, DOI: 10.1145/2034654.2034663`). Furthermore, `parallel_testcase() :: {command_list(), [command_list()]}` (`src/proper_statem.erl:286`) reuses the identical sequential specification to synthesize concurrent two-worker histories checked for linearizability (`Basis: source`).
2. **Value-Tree Compositional Shrinking vs. Internal Choice-Sequence Reduction**:
   - In `proptest-rs/proptest` (`proptest/src/strategy/traits.rs:37-103`), every `Strategy` produces a `Self::Tree : ValueTree<Value = Self::Value>`. Under `prop_map` (`traits.rs:72-85`), shrinking operates on the *source* `ValueTree` without user-written shrinkers. However, across dependent monadic `prop_flat_map` chains (such as generating a vector `xs` followed by a valid index `idx in 0..xs.len()`), shrinking the outer `ValueTree` invalidates or re-samples the inner `ValueTree`, causing shrinking to stall on non-minimal local optima (`Basis: source + execution`).
   - In `HypothesisWorks/hypothesis` (`9ea72564ee553a3aa603ad9f2997fbbdcd096d50`; `MacIver & Donaldson, ECOOP 2020, DOI: 10.4230/LIPIcs.ECOOP.2020.13`), every generator draws deterministic primitives from a linear **choice sequence** (byte/integer buffer), and the shrinker minimizes that underlying buffer in **shortlex order** (shorter buffers first, then lexicographically smaller values) while re-parsing through the unmodified generator. In our dependent `(xs, idx)` duplicate-neighbor micro-probe starting from `xs = [11, 4, 9, 9, 13, 2, 8, 5], idx = 3`, naive outer-length shrinking stalls at length `4` (`[11, 4, 9, 9], idx = 3`), whereas shortlex choice-sequence reduction deletes irrelevant prefix/suffix slices and zeroes elements down to the exact `2`-element fixed point `([0, 0], 1)` (`Basis: execution`).

---

### 2. Specification Vacuity, Reward-Hacked Contracts, and Dual Mutation Adequacy

#### 2.1 Why Existential Non-Vacuity Alone Fails to Catch Weak and Reward-Hacked Specs
In temporal model checking (`Beer et al., CAV 1997 / FMSD 2001, DOI: 10.1023/A:1008779610539`) and deductive verification, an implication $\forall x.\; \text{Pre}(x) \implies \text{Post}(x, f(x))$ suffers **antecedent vacuity** whenever $\neg \exists x.\; \text{Pre}(x)$ (for instance, conflicting range bounds `len(xs) > 5 && len(xs) < 2`, unconstructible ghost capabilities, or dead control-flow paths). Requiring a machine-checked existential witness (`WitnessExists`: $\exists x, y.\; \text{Pre}(x) \land \text{Post}(x, y)$) eliminates antecedent vacuity cleanly (`Basis: derived + execution`).

However, in both human proof engineering and LLM-driven synthesis (`Clover`, `Sun et al., DOI: 10.1007/978-3-031-65112-0_7`), the dominant failure mode once preconditions are satisfiable is **consequent under-specification (specification weakness or reward hacking)**: writing a `Post` predicate that holds on the intended implementation (so `WitnessExists` and `ProofForall` both pass!) while omitting essential relational constraints (`Basis: execution + derived`).

Our five-archetype specification adequacy probe over `sort_dedup(xs)` (`## Revalidation` Probe 2, evaluating `S1`–`S5` against `6` implementation mutants `M1`–`M6`) proves this separation constructively (`Basis: execution`):

| Specification Archetype | Verified on Ref Impl (`ProofForall`) | Non-Vacuity Check (`WitnessExists`) | Impl Mutants Killed (`6` Total) | Kill Rate | Surviving Buggy Implementations |
| :--- | :---: | :---: | :---: | :---: | :--- |
| **`S1`: Contradictory Pre (`len > 5 && len < 2`)** | `true` | **`false`** (Caught) | `0 / 6` | `0.0%` | All `6` (`M1`..`M6`) |
| **`S4`: Self-Referential Tautology (`len(out) == len(out)`)** | `true` | `true` (**Missed!**) | `0 / 6` | **`0.0%`** | All `6` (`M1`..`M6`) |
| **`S2`: Ordered-Only Post (`out[i] < out[i+1]`)** | `true` | `true` (**Missed!**) | `3 / 6` | **`50.0%`** | `M1_empty`, `M5_drop_neg`, `M6_const_zero` |
| **`S3`: Ordered Subset (`out[i] < out[i+1] && out ⊆ xs`)** | `true` | `true` (**Missed!**) | `4 / 6` | **`66.7%`** | `M1_empty`, `M5_drop_neg` |
| **`S5`: Complete Relational (`strict_ord(out) && set(out) == set(xs)`)** | `true` | `true` | **`6 / 6`** | **`100.0%`** | **None (`0` survivors)** |

Every weak specification `S2`, `S3`, and `S4` passes both `ProofForall` and `WitnessExists` (`true`), yet `S2` and `S3` falsely certify `fn sort_dedup(_) { vec![] }` (`M1_empty`) as "formally verified"! Only requiring `100%` kill rate over non-equivalent implementation mutants forces `Post` to tighten to `S5` (`Basis: execution + derived`).

#### 2.2 Mechanized Mutation Operators in `QuickChick`, `mCoq`, and `cargo-mutants`
Examining the upstream mutation engines reveals two distinct execution models (`Basis: source`):

1. **Zero-Recompile Extracted Discovery vs. Comment-Directed AST Mutation (`QuickChick/QuickChick`)**:
   - `src/Mutation.v:11-25, 81-130` defines Gallina infix operators `a mutant! b` and `a mutant: "bug" b`. Inside interactive Rocq/Coq proofs, `Definition mutation : mutation_id -> bool := fun _ => false` (`Mutation.v:106`) reduces `mutate _ f g l` strictly to the base expression `f tt`, leaving existing proofs undisturbed! Upon OCaml extraction (`Mutation.v:113-130`), `Extract Constant mutation` reads `Sys.getenv "QC_MUTANT"`: running once with `QC_MUTANT=DISCOVERY` logs every dynamically reachable `section:file:line:col` (`__POS__`) identifier into `qc-out/qc-mutants` (`L116-126`), after which worker processes test each mutant in parallel (`QC_MUTANT=<id>`) with **zero OCaml/Coq recompilation overhead**.
   - Complementarily, `quickChickTool` (`quickChickTool/quickChickToolLexer.mll:26-51`) lexes structured comment pragmas in both Coq (`(*! Section name *)`, `(*! extends base *)`, `(*! *)`, `(*!! tag *)`) and extracted/FFI C code (`/*! Section ... */`, `/*!! tag */`), allowing mutations that alter inductive `match` clauses, infix operators, or theorem statements themselves (`Mutation.v:71-76`). Similarly, `mCoq` (`Celik et al., DOI: 10.1109/ASE.2019.00057`) applies Coq SerAPI s-expression mutations (`ReorderConstructors`, `ReplaceConstant`, `OmitHypothesis`) directly to Gallina definitions and checks whether downstream `Qed` proofs fail (`Basis: source + documentation`).
2. **Type-Directed Function-Body Replacement (`sourcefrog/cargo-mutants`)**:
   - `src/fnvalue.rs:21-100` (`return_type_replacements`) inspects `syn::ReturnType` to synthesize well-typed degenerate bodies without creating uncompilable syntax errors: `()` for unit functions (`L26`), `{true, false}` for `bool` (`L43`), `{0, 1}` / `{0, 1, -1}` for unsigned/signed integers (`L49-52`), `1.try_into().unwrap()` / `(-1).try_into().unwrap()` for `NonZero<T>` (`L53-74`), `Ok(rep)` / `Err(err)` for `Result<T, E>` (`L78-93`), and `None` / `Some(rep)` for `Option<T>` (`L96-100`).
   - `src/outcome.rs:57-85` partitions every mutant in `LabOutcome` into `caught` (rejected by tests/verifier), `missed` (surviving mutant exposing a test or specification blind spot), `timeout`, and `unviable` (rejected at typecheck/build time). When applied to a formal verification crate, replacing `cargo test` with the proof checker turns `cargo-mutants` into a **specification tightness oracle**: any `missed` non-equivalent function-body mutant proves that the function's `ensures` contract is underconstrained (`Basis: source + derived`).

---

### 3. Metamorphic, Differential, and Single-Source Bisimulation Across Compiler & ISA Seams

#### 3.1 The Verified-Middle-End Seam (`CompCert` vs. `Csmith` and `YARPGen`)
Direct inspection of `AbsInt/CompCert` (`driver/Compiler.v:156-168, 265-278, 446-452`) pinpoints the exact syntactic boundary of CompCert's formal backward-simulation theorem (`Basis: source`):

```coq
Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
  OK p
  @@@ time "Clight generation" SimplExpr.transl_program
  @@@ transf_clight_program.

Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
```

`transf_c_program_correct` starts at `Csyntax.program` and ends at abstract `Asm.program`. Everything prior to `Csyntax`—preprocessing, lexing, parsing, implicit integer promotions, bitfield layout, and type elaboration in `cparser/Elab.ml` (`135,195 B` of unverified OCaml)—plus post-`Asm` textual printing, assembling, and ABI linking sits **outside** `transf_c_program_correct`. In Yang et al.'s landmark differential study (`PLDI 2011, DOI: 10.1145/1993498.1993532`), `csmith-project/csmith` (`0cdc710315cfee9035e22ef4363ca479270d1934`) uncovered **`0` wrong-code bugs in CompCert's Coq-verified middle-end passes**, while uncovering **`6` wrong-code bugs in CompCert's unverified front-end** and additional defects in assembly emission/ABI handling (`Basis: source + documentation`).

Crucially, `Csmith` and `YARPGen` target disjoint compiler optimization strata due to how each avoids C/C++ undefined behavior (`UB`) (`Basis: source`):
- **`Csmith` Runtime Safe-Math Guarding (`src/CGOptions.cpp:49-90`, `src/SafeOpFlags.cpp`)**: `Csmith` prevents signed overflow (`INT_MIN * -1`), shift-past-bitwidth, and divide-by-zero by wrapping operations in ternary `safe_add_func_int32_t_s_s` calls (`CGOptions::safe_math_wrapper_ids_`). While ideal for scalar alias analysis, struct/bitfield lowering, and register allocation, those injected conditional branches break basic-block straight-line form inside loops—**preventing LLVM/GCC loop vectorizers, SLP vectorizers, and polyhedral/SCEV passes from firing**!
- **`YARPGen` Compile-Time Interval & Loop-Nest Policies (`intel/yarpgen`, `src/gen_policy.h:27-95`, `src/program.cpp`)**: `YARPGen` (`Livinskii et al., OOPSLA 2020, DOI: 10.1145/3428264`) tracks exact concrete value ranges statically during AST construction across `LoopSequence` and `LoopNest` hierarchies (`ISPC_MAX_VECTOR_SIZE = 64`, `ITERATIONS_THRESHOLD_FOR_REDUCTION = 10000000`), emitting **zero runtime safe-math branches** so generated C/C++/ISPC loops trigger full `AVX-512`/NEON vectorization and scalar-evolution transformations (`Basis: source`).

#### 3.2 Equivalence Modulo Inputs (`EMI`), `Alive2` Byte-Exact SMT Refinement, and `SpecTec`/`Sail` Bisimulation
1. **Equivalence Modulo Inputs (`Le, Afshari & Su, PLDI 2014, DOI: 10.1145/2594291.2594334`)**: Differential testing requires $\ge 2$ independent compilers implementing the exact same dialect. `EMI` eliminates the second-compiler requirement via a metamorphic relation over a fixed input set $I$: profiling execution of program $P$ on $x \in I$ identifies dynamically unexecuted statements $S_{\text{dead}}(P, I)$; stochastically deleting, inserting, or mutating statements inside $S_{\text{dead}}(P, I)$ yields variants $P_1, \dots, P_k$ satisfying $\forall x \in I,\; \llbracket P_j \rrbracket(x) = \llbracket P \rrbracket(x)$. Any divergence between `cc -O0 P` and `cc -O3 P_j` on $I$ proves a miscompilation in `cc` alone (`Basis: documentation + derived`).
2. **Bounded SMT Translation Validation (`AliveToolkit/alive2`, `ir/memory.h:32-95`, `Lopes et al., PLDI 2021, DOI: 10.1145/3453483.3454030`)**: Random program generators struggle to synthesize tiny `3`-instruction peephole edge cases involving `undef`, `poison`, and pointer provenance. `Alive2` encodes each LLVM `IR::Byte` (`ir/memory.h:34-45`) as a tagged bitvector distinguishing pointer bytes (`1-bit isPtr`, `1-bit non-poison`, provenance `Pointer`, `ptrByteoffset`) from non-pointer bytes (`non-poison` bitmask, `data` bits, sub-byte `stored bits`) and checks refinement $\text{src} \sqsubseteq \text{tgt}$ over Z3: for all inputs where `src` does not trigger UB, `tgt` must not trigger UB, every non-`poison` bit of `src` must remain non-`poison` in `tgt`, and observable return/memory states must agree across all `undef` nondeterminism choices (`Basis: source`).
3. **Single-Source Golden-Interpreter Bisimulation (`Wasm-DSL/spectec` & `rems-project/sail`)**: Formal mechanization fails if the mechanized spec drifts from the normative prose standard or hardware silicon. `SpecTec` (`spectec/src/backend-interpreter/construct.ml:35-75`, `Youn et al., PLDI 2024, DOI: 10.1145/3656440`) compiles a single `.spectec` AST of WebAssembly 3.0 (`version = ref 3`) simultaneously into W3C Bikeshed/LaTeX prose, Coq/Isabelle/Lean definitions, and an executable `Al` reference interpreter (`al_to_floatN` checking bit-exact `NORM`/`SUBNORM`/`INF`/`NAN` payload layouts and `V128` SIMD lanes against the official `.wast` conformance suite). Similarly, `rems-project/sail` (`src/lib/value.ml`, `lib/sail.h`, `Armstrong et al., POPL 2019, DOI: 10.1145/3290384`) compiles authoritative ARMv8-A, RISC-V, and CHERI-MIPS ISA specifications to both high-speed C/OCaml emulators (`~1–10 MIPS` booted against Linux/test suites) and Coq/Lean/SMT definitions (`Basis: source + documentation`).

---

### 4. Soundness Fuzzing of SMT Solvers and Multi-Kernel Proof Checkers

#### 4.1 Oracle-Free Semantic Fusion and Scoped Generative Mutation (`testsmt/yinyang`)
Differential SMT fuzzing (`Z3` vs. `cvc5`) breaks down on complex non-linear arithmetic, string, or quantifier formulas whenever one solver times out (`unknown`) while the other answers `sat` or `unsat`. `testsmt/yinyang` (`yinyang/src/mutators/SemanticFusion/SemanticFusion.py:52-140`, `Winterer, Zhang & Su, PLDI 2020, DOI: 10.1145/3385412.3385985`) solves this via **Semantic Fusion** (`Basis: source`):
- Given two independent seed formulas $\varphi_1(\mathbf{x})$ and $\varphi_2(\mathbf{y})$ with *identical known satisfiability* $\Omega \in \{\texttt{sat}, \texttt{unsat}\}$ (and disjoint variable namespaces after `canonicalize_script`), `SemanticFusion.fuse` (`L100-140`) picks random variable pairs $(x \in \text{FV}(\varphi_1), y \in \text{FV}(\varphi_2))$ of matching sort, declares a fresh fused variable $z$, instantiates an invertible fusion relation $z = f(x, y)$ with closed-form inverses $x = f_x^{-1}(z, y)$ and $y = f_y^{-1}(z, x)$, and randomly substitutes a subset (`k = random.randint(0, len(occs))`, `L124-128`) of occurrences of $x$ in $\varphi_1$ and $y$ in $\varphi_2$ with $f_x^{-1}(z, y)$ and $f_y^{-1}(z, x)$.
- For `--oracle sat`, the fused formula is $\Phi_{\text{sat}} \equiv \varphi_1' \land \varphi_2'$ (`L138`: any satisfying pair $(x_0, y_0)$ induces $z_0 = f(x_0, y_0)$ satisfying $\Phi_{\text{sat}}$); for `--oracle unsat`, $\Phi_{\text{unsat}} \equiv (\varphi_1' \lor \varphi_2') \land (z = f(x, y))$ (`L134-136`: any model of $\Phi_{\text{unsat}}$ would project to a model of either $\varphi_1$ or $\varphi_2$, contradiction!). Because $x$ and $y$ become algebraically entangled across `declare-fun z`, solver preprocessors cannot trivially split $\varphi_1'$ and $\varphi_2'$. Our exhaustive `QF_BV8` truth-table probe (`## Revalidation` Probe 3, $256 \times 256 = 65,536$ valuations) confirms exact model-count preservation (`15` `SAT` models and `0` `UNSAT` models under modular coupling $z = (x + y) \bmod 256$) (`Basis: source + execution`).
- Alongside `yinyang`, the same repository ships **`OpFuzz`** (`yinyang/src/mutators/TypeAwareOpMutation.py:29-100`, mutating operators within arity-checked `N`/`N+`/`N-` equivalence classes such as `{<, <=, >, >=}` or `{forall, exists}`) and **`TypeFuzz`** (`yinyang/src/mutators/GenTypeAwareMutation/GenTypeAwareMutation.py:38-100`, `Park et al., OOPSLA 2021, DOI: 10.1145/3485529`), whose `in_scope` check (`L64-100`) enforces lexical quantifier/`let` binder typing, declaration-order visibility, and `:named`-attribute exclusion so donor subterms harvested from bug-tracker regression suites never trigger false syntax/scoping rejections (`Basis: source`).

#### 4.2 Stateful Incremental Solver API Fuzzing (`murxla/murxla`)
Batch `.smt2` file fuzzers miss stateful C++ API defects triggered only by interleaved `push()`, `pop()`, `check-sat-assuming()`, `get-unsat-core()`, `get-interpolants()`, and dynamic option reconfiguration. `murxla/murxla` (`src/fsm.hpp:40-110`, `src/dd.hpp:24-95`, `Niemetz, Preiner & Barrett, CAV 2022, DOI: 10.1007/978-3-031-13188-2_5`) drives `Bitwuzla`, `cvc5`, `Boolector`, `Yices2`, and `Z3` directly in-memory through a three-kind finite-state machine (`regular`, `decision`, and `choice` states, e.g., `#CHECK_SAT -> #DECIDE_SAT_UNSAT -> {#SAT, #UNSAT}` gating `get-value` vs. `get-unsat-core`, `fsm.hpp:66-74`), coupled with `ShadowSolver` cross-checking and an API-trace delta debugger `DD` (`dd.hpp:54-78`: `minimize_lines`, `minimize_line`, `substitute_terms`) that shrinks multi-thousand-call C++ API crash/soundness traces down to minimal standalone reproducers (`Basis: source`).

#### 4.3 Defeating Proof-Assistant Environment Injection and Single-Kernel Bugs (`lean4checker` & `nanoda_lib`)
Even when a theorem statement is non-vacuous and mutation-adequate, an interactive theorem prover with user-extensible tactics, macros, and `.olean` object deserialization has a critical post-elaboration attack surface (`Basis: source`):
- **Metaprogramming Environment Bypass (`leanprover/lean4checker`, `Lean4CheckerTests/AddFalseConstructor.lean:5-22`)**: Using `open private Lean.Kernel.Environment.add` and `Lean.Environment.setCheckedSync` inside `run_elab`, untrusted tactic code can inject a fabricated constructor `False.intro : False` directly into the compiled `.olean` environment without invoking kernel inductive validation!
- **Fresh-Environment Kernel Replay (`Lean4Checker/Replay.lean:14-100`)**: `lean4checker` loads serialized `.olean` `ConstantInfo` maps into `mkEmptyEnvironment` (`QuotEq.lean:31-32`) and replays every definition and theorem through `env.addDeclCore`. Crucially, `replay` **refuses to send serialized constructors or recursors to the kernel** (`Replay.lean:17-20, 45-46`): instead, it replays the `inductive` declaration and verifies bit-for-bit structural identity against the constructors and recursors freshly synthesized by the kernel, while `QuotEq.lean:4-34` enforces topological `Eq`-before-`Quot` ordering (`Quot.lift`/`Quot.ind` depend on `Eq`) and `AddFalse.lean`/`ReplaceAxiom.lean`/`PrivateConflict*.lean` test axiom-substitution and private-symbol shadowing attacks (`Basis: source`).
- **Independent Multi-Language Kernel Verification (`ammkrn/nanoda_lib`, `src/tc.rs:58-95`)**: Replaying inside `lean4checker` still trusts Lean 4's C++ kernel implementation (`whnf`, universe level constraints, nested inductive positivity, `Nat` bignum literal reduction). `nanoda_lib` re-implements the complete Lean 4 kernel independently in safe Rust (`TypeChecker` over `ExportFile::check_declar` handling `Axiom`, `Inductive`, `Quot`, `Definition`/`Theorem`, `Constructor`, and `Recursor`, `src/tc.rs:80-95`) with zero shared C++ code, converting any C++ kernel memory-safety or reduction bug into an immediate cross-checker discrepancy (`Basis: source`).

---

### 5. Cross-Cutting Synthesis: `L1–L6` Performance, `C1–C2` Comprehensibility & Simplicity, and `V1–V4` End-to-End Validation

#### 5.1 Multi-Level Performance and Resource Footprint Matrix (`L1–L6`)
`Basis: source + execution + documentation + derived`

| Validation Mechanism | `(L1)` Authoring & Repair Velocity | `(L2)` Toolchain Build Cost | `(L3)` Generation / Analysis Latency | `(L4)` Runtime Execution Overhead | `(L5)` Witness / Replay Speed | `(L6)` RAM, Disk & Artifact Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`QuickChick` Derived PBT (`6b98c9be...`)** | `1–3` lines (`Derive ArbitrarySizedSuchThat`); `5–20x` faster than manual `Gen` proofs | Coq + OCaml plugin build `~1–3 min` (`~1.2 GiB` RSS) | Derivation `0.1–1.5 s`; `5,000` sized BST samples in `55.36 ms` (`Probe 1`) | `0 B` / `0` cycles in production binary (test-only extraction) | Counterexample check `< 1 ms` in extracted OCaml | Extracted runner `~2–6 MiB`; `.vo` proofs `100 KiB – 4 MiB` |
| **Stateful PBT + Choice Shrinking (`PropEr` / `Hypothesis`)** | `50–150` LoC state-machine model covers `10^4+` call interleavings | Pure Erlang / Python (`< 10 s` install) | `100–500` stateful runs in `0.2–4.0 s`; shrinking `10–300 ms` | `0` production overhead | Deterministic seed/buffer replay `< 5 ms` | Choice buffer `64 B – 8 KiB` per test case; `< 80 MiB` RSS |
| **Spec/Impl Mutation (`cargo-mutants` / `Mutation.v`)** | `0` LoC (`cargo-mutants` AST auto-gen) or `1`-token `mutant!` inline | Baseline `cargo build --tests` (`5–90 s`) | `QC_MUTANT` env switch `0 s` rebuild; `cargo-mutants` `0.3–5 s`/mutant incremental | `0` when stripped (`Mutation.v` reduces to `a` in Coq) | Surviving-mutant diff + witness test `< 50 ms` | Scratch build tree `200 MiB – 3 GiB` (`copy_tree`); `qc-mutants` `< 4 KiB` |
| **Compiler Fuzzing & SMT TV (`Csmith` / `YARPGen` / `Alive2`)** | `0` per-pass human LoC; C-Reduce / `llvm-reduce` auto-minimization | C++/LLVM/Z3 build `2–15 min` (`2–8 GiB` RSS) | `Csmith`/`YARPGen` `10–80 ms`/prog; `Alive2` `10 ms – 30 s` (`rlimit` tails on loops) | `0` runtime tax on shipped binaries | Reduced C reproducer `< 20 ms`; SMT proof check `1–50 ms` | `10–80 KiB` C source per seed; `Alive2`/Z3 `100 MiB – 4 GiB` RSS |
| **SMT & Kernel Auditing (`yinyang` / `Murxla` / `lean4checker` / `nanoda_lib`)** | `0` per-theorem LoC (automated CI gate) | Python `0 s`; C++ `Murxla` `~30 s`; Rust `nanoda_lib` `~20 s` | `yinyang` fusion `< 5 ms`/pair; `Murxla` `500–5,000` API ops/s | `0` runtime overhead (`L4` erased / offline gate) | `lean4checker` / `nanoda_lib` full Mathlib-scale replay `~15–90 s` multi-core (`10–80 MB/s`) | `.olean` / export files `10 MiB – 2 GiB`; Rust `nanoda_lib` `~0.5–3 GiB` RSS |

#### 5.2 Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)
`Basis: source + derived`

- **`(C1)` Human Comprehensibility & Mental-Model Ergonomics (Distinguishing Human Auditability from LLM Ease)**:
  - Automated provers and LLMs easily discharge `500`-line tactic scripts over `30`-clause `ensures` formulas that a human reviewer *cannot* mentally simulate, creating a severe **comprehension-vs-automation hazard**: as demonstrated by `S2` and `S3` in §2.1, omitting a single set-equality clause while keeping `strict_ord(out) && out ⊆ xs` looks plausible on surface inspection yet admits `vec![]`!
  - Shortlex choice-stream shrinking (`Hypothesis`) and symbolic command shrinking (`PropEr` `proper_statem.erl`) directly optimize `C1` diagnostic legibility: handing a human engineer a `2`-element counterexample `([0, 0], 1)` or a `2`-step `push(); pop(); check_sat()` `Murxla` `DD` trace fits in `2–3` working-memory slots, whereas raw unshrunk `200`-node AST dumps overwhelm human debugging even when machine-reproducible.
  - Likewise, `SpecTec` and `Sail` reduce nonlocal cross-document reasoning to **one authoritative definition** so humans never have to eyeball equivalence between English prose, Coq inductives, and C reference emulators.
- **`(C2)` Simplicity, Orthogonality & Universal Model Refinement (Felleisen Expressiveness & Ousterhout Deep Modules)**:
  - Across these seventeen tools, three apparent special cases collapse into cleaner universal abstractions when stripped of realization quirks:
    1. *Unifying Generator, Shrinker, and Fuzzer Mutator*: `Proptest`'s coupled `Strategy + ValueTree` and custom AST shrinkers duplicate structural traversal logic. Treating generation as parsing a canonical choice stream (`Hypothesis` / `FuzzChick` `fuzz/Fuzz.ml`) makes shrinking, mutation, and coverage-guided greybox fuzzing ordinary operations on `bytes` behind a deep `Generator<T>` module—without leaking `Shrink` boilerplate to users.
    2. *Unifying Vacuity and Adequacy as Dual Model-Distinguishing Pairings*: Rather than treating "vacuity checking," "mutation testing," and "equivalence checking" as ad-hoc add-ons, every sound contract `(Pre, Post)` over implementation `f` requires two orthogonal witnesses: **positive inhabitation** ($\exists x.\; \text{Pre}(x) \land \text{Post}(x, f(x))$) and **negative mutant separation** ($\forall f' \in \mathcal{M}(f),\; f' \not\equiv f \implies \exists x.\; \text{Pre}(x) \land \neg\text{Post}(x, f'(x))$).
    3. *Separating Untrusted Elaboration/Search from Tiny Replay Kernels*: Both `lean4checker` (`191` LoC `Replay.lean`) and `nanoda_lib` (`22` Rust files) exemplify Ousterhout's deep-module principle: `300+ KLoC` of Lean elaborators, tactic macros, and `.olean` caches stay completely outside the TCB, reduced to a minimal declaration-replay interface (`Axiom | Inductive | Quot | Definition | Theorem`).

#### 5.3 End-to-End Solution & Implementation Validation Across `V1–V4`
Even meta-verification tools must themselves be validated end-to-end across reality gaps (`Basis: source + documentation + derived`):
- **`(V1)` Specification Adequacy, Mutation & Non-Vacuity**: `QuickChick`'s `CorrectSizedST` (`src/DependentClasses.v:16-17`) mechanically proves in Coq that derived generators neither drop valid cases nor emit invalid ones, while `Mutation.v` + `mCoq` + `Clover` equivalence checks validate that specifications reject semantic mutants.
- **`(V2)` Compiler, Lowering & Checker Soundness Fuzzing**: `Csmith`, `YARPGen`, `EMI`, and `Alive2` cross-check compiler lowering passes; `yinyang`/`OpFuzz`/`TypeFuzz`/`Murxla` fuzz `Z3` and `cvc5`; and `lean4checker`'s adversarial negative test suite (`AddFalse.lean`, `AddFalseConstructor.lean`, `ReplaceAxiom.lean`, `OpenPrivate.lean`, `PrivateConflictA..C.lean`, `QuotEq.lean`) paired with `nanoda_lib` differential replay validates proof-kernel soundness against malformed witnesses.
- **`(V3)` Concurrency, Crash, Silicon & Physical Leakage Reality Gaps**: Pure functional ISA/compiler proofs (`CompCert`, `Sail`) still erase microarchitectural speculation and physical power/glitch side channels! End-to-end hardware-software stacks pair `Sail`/`CompCert` functional correctness with black-box CPU speculation contract fuzzing (`Revizor`, `Oleksenko et al., ASPLOS 2022, DOI: 10.1145/3503222.3507729`), gate-level execution-aware glitch-extended masking verification (`Coco`/`Alma`, `Gigerl et al., USENIX Security 2021`), fixed-vs-random Welch's $t$-test power/EM leakage validation (`TVLA`), and concurrent/crash model checking (detailed in companion package `genmc-stateless-model-checking-crashmonkey-torn-io-and-madsim-determinism`).
- **`(V4)` Plant Falsification, Telemetry/HIL Replay & Human Comprehension Litmus Testing**: When verified controllers or floating-point solvers (`SpecTec` IEEE-754 `NAN` canonicalization, hybrid ODE controllers) meet physical plants or human authors, validation requires Signal Temporal Logic (`STL`) robustness falsification (`S-TaLiRo`, `Annpureddy et al., TACAS 2011, DOI: 10.1007/978-3-642-19835-9_21`), verified runtime model-compliance monitors (`ModelPlex`, `Mitsch & Platzer, FMSD 2016, DOI: 10.1007/s10703-016-0241-z`) triggering safe fallback whenever real telemetry exits the proved plant envelope, and behavioral misconception litmus suites (`SMoL`, `Lu et al., OOPSLA 2024, DOI: 10.1145/3649823`) testing whether human engineers accurately predict what their written specifications permit.

---

## Boundaries

1. **Undecidability of Equivalent-Mutant Detection (`known not to apply` / theoretical limit)**: Neither `cargo-mutants`, `QuickChick` `Mutation.v`, nor `mCoq` can automatically decide whether a surviving implementation or specification mutant $f'$ is observationally equivalent to $f$ ($\forall x.\; \text{Pre}(x) \implies f'(x) = f(x)$) in Turing-complete fragments (`Basis: derived`). Surviving mutants require bounded SMT equivalence checking (`Alive2` / `Clover`) or human inspection.
2. **Loop & Unbounded-Memory Scaling Cliffs in `Alive2` (`unsupported` / bounded scope)**: `AliveToolkit/alive2` (`3bdd4f5e1cefa47057e93110e707acd11cfe08e4`) performs *bounded* loop unrolling and bounded allocation modeling (`Basis: source + documentation`). It proves translation soundness up to the unroll bound and catches `poison`/`undef` miscompilations in `1–3` loop iterations, but is **known not to apply** as an unbounded inductive verifier for arbitrary data-dependent loop trip counts.
3. **Unverified Extraction, Pretty-Printing, and Assembler Trust in `QuickChick` and `CompCert` (`known not to apply` without binary validation)**:
   - `QuickChick`'s `CorrectSizedST` proofs hold over Gallina `G (option A)` semantics, but execution runs after Coq-to-OCaml extraction (`ExtractionQC.v.cppo`, mapping `loc` and `Sys.getenv` via `Extract Constant` axioms in `Mutation.v:95-130`). Bugs in OCaml extraction axioms can invalidate test verdicts (`Basis: source`).
   - Standard `CompCert` (`driver/Compiler.v:156-168`) proves `Csyntax -> Asm` backward simulation in Coq, leaving `cparser/Elab.ml` and external GNU/Clang assemblers outside the proof unless paired with verified parsing (`Jourdan et al., Pottier LR(1)`) and binary translation validation (`Basis: source`).
4. **Co- Inductive, Higher-Order Functional, and Cryptographic Relations in `QuickChick` Derivation (`unsupported`)**: `QuickChick`'s automatic `Derive ArbitrarySizedSuchThat` plugin (`plugin/arbitrarySizedST.ml`) requires decidable equality/checkers on unified indices and syntactic inductive clause structure; generators for cryptographic preimages (e.g., `sha256(x) == h`) or arbitrary higher-order function arguments are **unsupported** by syntactic unification derivation (`Basis: source`).
5. **Solver Performance Regressions vs. Soundness Bugs in `yinyang` (`known not to apply`)**: `SemanticFusion.py` (`L100-140`) preserves exact satisfiability (`sat`/`unsat`) to detect soundness bugs (`segfault`, assertion failure, wrong `sat`/`unsat` answer), but intentionally entangles variables to defeat solver heuristics; an `unknown` or `timeout` outcome on a fused formula is **not** a solver bug (`Basis: source`).
6. **Hardware Execution of `Z3`, `cvc5`, `CompCert`, and `lean4checker` Binaries (`not examined` via local compilation)**: Source trees for `Z3`, `cvc5`, `CompCert`, `Alive2`, `lean4checker`, and `nanoda_lib` were directly inspected at their pinned `40`-hex commits and modeled via executable Python probes, but full native C++/Lean/OCaml builds of those six repositories were **not examined** by local compilation during this session (`Basis: execution`).

---

## Evidence

### Primary Upstream Source Repositories (Pinned 40-Hex Revisions)
- **`QuickChick/QuickChick` @ `6b98c9beca3ff5cfb645f6aa4e35a8146081f128`**:
  - `src/DependentClasses.v:13-77`: `CorrectSizedST`, `CorrectST`, `GenSizedSuchThat`, and `SizeMonotonicOpt` typeclasses.
  - `plugin/arbitrarySizedST.ml:10-90`: OCaml derivation of `bindGenOpt`, `suchThatMaybeOpt`, and `construct_match_with_return`.
  - `src/Mutation.v:6-130` & `quickChickTool/quickChickToolLexer.mll:26-51`: `QC_MUTANT=DISCOVERY` zero-recompile OCaml extraction hook and `(*! Section *)` / `(*!! tag *)` / `/*! ... */` comment mutation lexer.
- **`proper-testing/proper` @ `9b0da8778206b0f264c942fabca45d0f9bda2e7b`**:
  - `src/proper_statem.erl:94-140, 279-315`: `symbolic_state()`, `dynamic_state()`, `{'var', pos_integer()}`, sequential and `parallel_testcase()` state-machine shrinking/execution contract.
- **`proptest-rs/proptest` @ `70cf37d46b7d83393b6ed94c611f8c52209f585d`** & **`HypothesisWorks/hypothesis` @ `9ea72564ee553a3aa603ad9f2997fbbdcd096d50`**:
  - `proptest/src/strategy/traits.rs:27-103`: `Strategy::Tree : ValueTree` source-space shrinking under `prop_map` vs. monadic `prop_flat_map`, contrasted with Hypothesis shortlex choice-sequence reduction (`DOI: 10.4230/LIPIcs.ECOOP.2020.13`).
- **`sourcefrog/cargo-mutants` @ `6c720ae82a1784b84cfa06066f7b0d59ed1798d0`**:
  - `src/fnvalue.rs:21-100`: `return_type_replacements` for `bool`, integers, `NonZero<T>`, `Result`, and `Option`.
  - `src/outcome.rs:57-85`: `LabOutcome` classification (`missed`, `caught`, `timeout`, `unviable`).
- **`AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`**, **`csmith-project/csmith` @ `0cdc710315cfee9035e22ef4363ca479270d1934`**, **`intel/yarpgen` @ `1adb290f453505838f3aa33dc571f292b0c1810f`**, **`AliveToolkit/alive2` @ `3bdd4f5e1cefa47057e93110e707acd11cfe08e4`**:
  - `CompCert` `driver/Compiler.v:156-168, 446-452` (`transf_c_program_correct` over `Csyntax.program`) vs. unverified `cparser/Elab.ml`.
  - `Csmith` `src/CGOptions.cpp:49-90` (`safe_math_wrapper_ids_`) vs. `YARPGen` `src/gen_policy.h:27-95` (`GenPolicy`, `ISPC_MAX_VECTOR_SIZE = 64`).
  - `Alive2` `ir/memory.h:32-95` (`IR::Byte` pointer/non-pointer `poison` and provenance bit-layout).
- **`Wasm-DSL/spectec` @ `acc6e834ff403c82554d081237f327346190ad96`** & **`rems-project/sail` @ `97aa617dcd4d01575f773cb58ea1e8686858c8c2`**:
  - `spectec/src/backend-interpreter/construct.ml:28-75` (`al_to_fmagN`, `al_to_floatN`, `z_to_vec128`); `sail` `src/lib/value.ml` and `lib/sail.h`.
- **`testsmt/yinyang` @ `5ce963290b682fccdb7f27464de0e5c0d02047c5`**, **`murxla/murxla` @ `d32047c4c00a9c93ff9e564eeed5196f517e5cff`**, **`Z3Prover/z3` @ `bcad05a7bf7dd9b82bd7a665018e0480e737264b`**, **`cvc5/cvc5` @ `eb203989c35e47030d0aa37afafb8458cb54e5e9`**:
  - `yinyang/src/mutators/SemanticFusion/SemanticFusion.py:52-140`, `TypeAwareOpMutation.py:29-100`, `GenTypeAwareMutation/GenTypeAwareMutation.py:38-100`.
  - `murxla` `src/fsm.hpp:40-110` (`regular`/`decision`/`choice` solver API states) and `src/dd.hpp:24-95` (`DD` trace delta debugger).
- **`leanprover/lean4checker` @ `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`** & **`ammkrn/nanoda_lib` @ `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`**:
  - `Lean4Checker/Replay.lean:14-100`, `Lean4CheckerTests/AddFalseConstructor.lean:1-22`, `Lean4CheckerTests/QuotEq.lean:1-34`, and `nanoda_lib` `src/tc.rs:58-95` (`ExportFile::check_declar`).

### Peer-Reviewed Primary Literature (Verified DOIs)
- Zoe Paraskevopoulou, Cătălin Hriţcu, Maxime Dénès, Leonidas Lampropoulos, Benjamin C. Pierce, *Foundational Property-Based Testing*, ITP 2015 (`DOI: 10.1007/978-3-319-22102-1_22`).
- Leonidas Lampropoulos, Zoe Paraskevopoulou, Benjamin C. Pierce, *Generating Good Generators for Inductive Relations*, POPL 2018 (`DOI: 10.1145/3158133`).
- Manolis Papadakis, Konstantinos Sagonas, *A PropEr Integration of Types and Function Specifications with Property-Based Testing*, Erlang Workshop 2011 (`DOI: 10.1145/2034654.2034663`).
- David R. MacIver, Alastair F. Donaldson, *Test-Case Reduction via Test-Case Generation: Insights from the Hypothesis Reducer*, ECOOP 2020 (`DOI: 10.4230/LIPIcs.ECOOP.2020.13`).
- Ilan Beer, Shoham Ben-David, Cindy Eisner, Yoav Rodeh, *Efficient Detection of Vacuity in Temporal Model Checking*, FMSD 2001 (`DOI: 10.1023/A:1008779610539`).
- Ahmet Çelik, Karl Palmskog, Marinela Parovic, Emilio Jesús Gallego Arias, Milos Gligoric, *Mutation Analysis for Coq*, ASE 2019 (`DOI: 10.1109/ASE.2019.00057`).
- Chuyue Sun, Ying Sheng, Oded Padon, Clark Barrett, *Clover: Closed-Loop Verifiable Code Generation*, SAIV 2024 (`DOI: 10.1007/978-3-031-65112-0_7`).
- Xuejun Yang, Yang Chen, Eric Eide, John Regehr, *Finding and Understanding Bugs in C Compilers*, PLDI 2011 (`DOI: 10.1145/1993498.1993532`).
- Vu Le, Mehrdad Afshari, Zhendong Su, *Compiler Validation via Equivalence Modulo Inputs*, PLDI 2014 (`DOI: 10.1145/2594291.2594334`).
- Vsevolod Livinskii, Dmitry Babokin, John Regehr, *Random Testing for C and C++ Compilers with YARPGen*, OOPSLA 2020 (`DOI: 10.1145/3428264`).
- Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, John Regehr, *Alive2: Bounded Translation Validation for LLVM*, PLDI 2021 (`DOI: 10.1145/3453483.3454030`).
- Dongjun Youn et al., *Bringing the WebAssembly Standard up to Speed with SpecTec*, PLDI 2024 (`DOI: 10.1145/3656440`).
- Alasdair Armstrong et al., *ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS*, POPL 2019 (`DOI: 10.1145/3290384`).
- Dominik Winterer, Chengyu Zhang, Zhendong Su, *Validating SMT Solvers via Semantic Fusion*, PLDI 2020 (`DOI: 10.1145/3385412.3385985`).
- Jiwon Park, Dominik Winterer, Chengyu Zhang, Zhendong Su, *Generative Type-Aware Mutation for Testing SMT Solvers*, OOPSLA 2021 (`DOI: 10.1145/3485529`).
- Aina Niemetz, Mathias Preiner, Clark Barrett, *Murxla: A Modular and Highly Extensible API Fuzzer for SMT Solvers*, CAV 2022 (`DOI: 10.1007/978-3-031-13188-2_5`).
- Cross-layer `V3`/`V4` references: `Revizor` (`DOI: 10.1145/3503222.3507729`), `S-TaLiRo` (`DOI: 10.1007/978-3-642-19835-9_21`), `ModelPlex` (`DOI: 10.1007/s10703-016-0241-z`), `SMoL` (`DOI: 10.1145/3649823`).

### Execution Environment & Recorded Probe Receipts (`2026-11-19`)
Executed on Linux `x86_64` with Python `3` stdlib (`seed = 20261119`):
- **Probe 1 (`BST` Generation & Choice-Sequence Shrinking)**: Naive filtering `0 / 5,000` (`0.0%`, `38.63 ms`) vs. relation-directed `2,644 / 5,000` (`52.88%`, `55.36 ms`); dependent `(xs, idx)` shrunk from length `8` to `([0, 0], 1)` vs. outer-only stagnation at length `4`.
- **Probe 2 (Vacuity vs. Mutation Adequacy)**: Confirmed `S1` caught by `WitnessExists == false`, `S2`/`S3`/`S4` (`WitnessExists == true`) leaked `50.0%` / `33.3%` / `100.0%` of buggy mutants, and `S5` achieved `6 / 6` (`100.0%`) mutant kills.
- **Probe 3 (`QF_BV8` Semantic Fusion)**: Exhaustive `65,536`-state check confirmed `15` `SAT` models and `0` `UNSAT` models preserved under $z = (x + y) \bmod 256$ substitution.

---

## Revalidation

Run the following self-contained Python `3.10+` verification script (`0` external dependencies; `exit 0` in `< 200 ms`) to revalidate all quantitative findings on relation-directed generation, shortlex choice-sequence shrinking, specification vacuity vs. mutation-kill adequacy, and `yinyang` semantic-fusion equisatisfiability:

```bash
python3 - <<'PY'
import random

# 1. Relation-directed BST generation vs. naive rejection sampling (seed 20261119)
rng = random.Random(20261119)
def is_bst(n, lo=-10**9, hi=10**9):
    return True if n is None else (lo < n[0] < hi and is_bst(n[1], lo, n[0]) and is_bst(n[2], n[0], hi))
def nodes(n):
    return 0 if n is None else 1 + nodes(n[1]) + nodes(n[2])
def gen_naive(s, r):
    return None if (s <= 0 or r.random() < 0.35) else (r.randint(0, 31), gen_naive(s - 1, r), gen_naive(s - 1, r))
def gen_dir(s, lo, hi, r):
    if s <= 0 or hi - lo <= 1 or r.random() < 0.25:
        return None
    k = r.randint(lo + 1, hi - 1)
    return (k, gen_dir(s - 1, lo, k, r), gen_dir(s - 1, k, hi, r))

naive_hits = sum(1 for _ in range(5000) if (lambda t: nodes(t) >= 6 and is_bst(t, -1, 32))(gen_naive(5, rng)))
dir_hits = sum(1 for _ in range(5000) if (lambda t: nodes(t) >= 6 and is_bst(t, -1, 32))(gen_dir(5, -1, 32, rng)))
assert naive_hits == 0 and dir_hits == 2644, (naive_hits, dir_hits)

# 2. Shortlex ChoiceSequence shrinking to canonical ([0, 0], 1) fixed point
def decode(buf):
    n = (buf[0] % 8) + 1
    return [buf[1 + i] % 16 for i in range(n)], buf[9] % n
def fails(xs, idx):
    return 0 < idx < len(xs) and xs[idx] == xs[idx - 1]

best = [7, 11, 4, 9, 9, 13, 2, 8, 5, 3]
assert fails(*decode(best))
changed = True
while changed:
    changed = False
    n_cur = (best[0] % 8) + 1
    for new_n in range(2, n_cur):
        for off in range(0, n_cur - new_n + 1):
            sub = best[1 + off : 1 + off + new_n]
            for new_idx in range(new_n):
                cand = [new_n - 1] + sub + [0] * (8 - len(sub)) + [new_idx]
                if cand < best and fails(*decode(cand)):
                    best, changed = cand, True
                    break
            if changed:
                break
        if changed:
            break
    for pos in range(len(best)):
        for v in range(best[pos]):
            cand = list(best)
            cand[pos] = v
            if fails(*decode(cand)):
                best, changed = cand, True
                break
    # Coupled equal-pair zeroing pass (standard Hypothesis block-zero reduction)
    for v in range(best[1]):
        cand = list(best)
        cand[1] = cand[2] = v
        if cand < best and fails(*decode(cand)):
            best, changed = cand, True
            break
assert decode(best) == ([0, 0], 1), decode(best)

# 3. Specification vacuity vs. implementation-mutant kill matrix
domain = [[], [0], [2, 1], [1, 1], [3, -1, 2], [2, 2, 1], [-2, 0, -2, 1], [3, 1, 2, 0]]
ref = lambda xs: sorted(set(xs))
mutants = [
    lambda xs: [],
    lambda xs: list(xs),
    lambda xs: sorted(xs),
    lambda xs: list(dict.fromkeys(xs)),
    lambda xs: sorted(set(x for x in xs if x >= 0)),
    lambda xs: [0] if xs else [],
]
s1 = (lambda xs: len(xs) > 5 and len(xs) < 2, lambda xs, o: o == ref(xs))
s3 = (lambda xs: True, lambda xs, o: all(o[i] < o[i+1] for i in range(len(o)-1)) and set(o).issubset(set(xs)))
s5 = (lambda xs: True, lambda xs, o: all(o[i] < o[i+1] for i in range(len(o)-1)) and set(o) == set(xs))

def eval_spec(pre, post):
    wit = any(pre(x) and post(x, ref(x)) for x in domain)
    kills = sum(1 for m in mutants if not all((not pre(x)) or post(x, m(x)) for x in domain))
    return wit, kills

assert eval_spec(*s1) == (False, 0)
assert eval_spec(*s3) == (True, 4)   # WitnessExists=True, yet 2 buggy mutants survive!
assert eval_spec(*s5) == (True, 6)   # WitnessExists=True AND 6/6 mutants killed!

# 4. Exhaustive QF_BV8 Semantic Fusion equisatisfiability check
sat_cnt = unsat_cnt = 0
for x in range(256):
    for y in range(256):
        z = (x + y) & 0xFF
        xi, yi = (z - y) & 0xFF, (z - x) & 0xFF
        if ((xi & 0x0F) == 0x0A and x >= 16) and ((yi ^ 0x55) == 0xAA):
            sat_cnt += 1
        if ((xi & 0x0F) == 0x0A and (x & 1) == 1) or ((yi ^ 0x55) == 0xAA and y < 128):
            unsat_cnt += 1
assert sat_cnt == 15 and unsat_cnt == 0, (sat_cnt, unsat_cnt)
print("PACKAGE 1 REVALIDATION PASSED: dir_hits=2644, shrunk=([0, 0], 1), kills=(0,4,6), bv8=(15,0)")
PY
```

To revalidate upstream repository coordinates when rebasing onto newer snapshots:
1. Check `QuickChick` `src/DependentClasses.v` (`CorrectSizedST`), `src/Mutation.v` (`QC_MUTANT`), `AbsInt/CompCert` `driver/Compiler.v` (`transf_c_program_correct`), `AliveToolkit/alive2` `ir/memory.h` (`IR::Byte`), `testsmt/yinyang` `SemanticFusion.py` (`fuse`), `leanprover/lean4checker` `Lean4Checker/Replay.lean` (`replayConstant` constructor/recursor exclusion), and `ammkrn/nanoda_lib` `src/tc.rs` (`check_declar`).
