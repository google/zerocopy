# Superoptimization, SMT Solver Fuzzing, and CPU RTL / Microarchitectural Contract Testing

## Summary

Automated verification and synthesizing optimization pipelines depend on a vertical stack of largely unverified oracles: compiler refinement encoders (`STOKE`, `Souper`, `Minotaur`, `Alive2`), underlying SMT/SAT solvers (`Z3`, `cvc5`, `CaDiCaL`), RTL processor implementations (`CVA6`, `Rocket`, `BOOM`, `VexRiscv`, `PicoRV32`), and physical microarchitectural silicon (`x86-64`, `ARM64`). Direct source inspection across these pinned upstream systems and executable semantic micro-probes establish five load-bearing invariants:

1. **Superoptimizer soundness fails at quantifier polarity, `poison`/NaN modeling, and memory omission, not merely at search heuristics:** `STOKE` uses Metropolis-Hastings MCMC over x86-64 assembly with short-circuited concrete test-case evaluation followed by bounded or data-driven symbolic equivalence checking (`DdecValidator`). `Souper` and `Minotaur` shift synthesis to LLVM SSA IR validated by `Alive2` refinement, where subtle SMT encoding bugs dominate soundness: leaving source `undef` or NaN-payload nondeterminism variables free (existential) instead of universally quantified lets Z3 fabricate invalid constant syntheses, while unconditional `pre_src == pre_tgt` precondition folding breaks FP synthesis. In `minotaur-toolkit/minotaur` (`f764ac4eb2c5`), memory refinement in `AliveEngine::find_model` is currently commented out, and reserved-constant synthesis greedily biases toward `poison` lanes despite a stale comment claiming non-poison preference.
2. **Differential and metamorphic SMT fuzzing exposes refutation-soundness bugs that require independent proof checking to close:** `YinYang` (`SemanticFusion`) fuses pairs of SAT formulas via conjunction without explicit fusion constraints (relying on invertible substitutions $x \mapsto f_x^{-1}(y, z)$), whereas UNSAT fusion uses disjunction and *requires* conjoining $z = f(x, y)$ (omitting the constraint turns UNSAT into SAT). `TypeFuzz`/`OpFuzz` achieves high bug discovery through arity-gated bidirectional and unidirectional operator mutations. Closing the resulting SMT trust gap requires emitting checkable proof certificates: `Z3`'s internal `proof_checker` shares Z3's `th_rewriter` and defers `side_conditions`, whereas `cvc5` emits Alethe proofs checkable by `Carcara` (caveat: `lia_generic` is unchecked without elaboration, and `--allowed-rules` masks skipped rules as `valid` rather than `holey`), and `CaDiCaL` emits binary/ASCII LRAT proofs verified down to machine code by HOL4/CakeML `cake_lpr`.
3. **Asymmetric ISA pre-simulation breaks the early-crash barrier in pre-silicon CPU RTL fuzzing:** `Cascade` resolves placeholder control-flow and memory-address registers against Spike first and then rewrites them so data values govern subsequent control flow and memory addresses across up to $10^5$ instructions. Any RTL bug that alters architectural state cascades into non-termination (detected by Verilator/Modelsim cycle-budget timeout `MAX_CYCLES_PER_INSTR = 30`, `SETUP_CYCLES = 1000`) or into a fenced final register-dump mismatch, bypassing per-instruction lockstep co-simulation overhead while uncovering 37 new bugs across 5 RISC-V cores.
4. **Black-box silicon contract fuzzing tests relational non-interference rather than functional ISA equivalence:** `Revizor` tests $\forall i_1, i_2.\ \text{CTrace}(p, i_1) = \text{CTrace}(p, i_2) \implies \text{HTrace}(p, i_1) \equiv \text{HTrace}(p, i_2)$ by grouping inputs into contract equivalence classes and checking hardware-trace divergence on real silicon via a kernel-module executor. Inspection of `microsoft/sca-fuzzer` (`cc9fa2e53d92`) reveals two concrete operational caveats: the unknown-value speculation backend (`_VspecBaseSpeculator`) raises `NotImplementedError` as unmaintained, and `SetAnalyser.htraces_are_equivalent` contains an upstream outlier-filtering bug (`x >= threshold` instead of `counter[x] >= threshold`), causing spurious contract violations under `analyser_subsets_is_violation = True`.
5. **No single technique eliminates the vertical TCB; defense-in-depth must compose them:** Superoptimizers should emit translation-validation queries discharged by proof-producing solvers checked by small, independent checkers (`Carcara` with zero `--allowed-rules` and elaborated `lia_generic`, or `cake_lpr` for bit-blasted SAT/BV), while silicon assumptions must be bounded by pre-silicon RTL fuzzing (`Cascade`) and post-silicon leakage-contract testing (`Revizor`).

## Applicability

This report synthesizes and cross-checks twelve durable upstream software artifacts and their accompanying peer-reviewed specifications pinned in `REPORT.json`, observed on `2026-11-19`:

- **Compiler superoptimization & refinement validation:** `StanfordPL/stoke` (`98d8a0f028f2`), `google/souper` (`963d4df436f3`), `minotaur-toolkit/minotaur` (`f764ac4eb2c5`, OOPSLA 2024 / `arXiv:2306.00229v3`), and `AliveToolkit/alive2` (`3bdd4f5e1cef`, PLDI 2021). Findings apply to x86-64 assembly superoptimization (`STOKE`) and LLVM SSA scalar/SIMD IR superoptimization (`Souper`, `Minotaur`) using SMT-based refinement checking.
- **SMT/SAT oracle fuzzing and proof checking:** `testsmt/yinyang` (`5ce963290b68`, PLDI 2020 & OOPSLA 2020), `Z3Prover/z3` (`c73b745cef36`), `cvc5/cvc5` (`7507ed17e261`), `ufmg-smite/carcara` (`193b1b015d29`, TACAS 2023), `arminbiere/cadical` (`6b3d70b9ce00`), and `tanyongkiam/cake_lpr` (`033aad53d173`, TACAS 2021, built from HOL4 `9783a49979c9` and CakeML `665f9b21712a`). Findings apply to SMT-LIB 2 solvers (`QF_BV`, `QF_LIA`, `QF_NRA`, `QF_S`, `QF_FP`, quantified logics) and CDCL SAT refutation checking.
- **CPU RTL and silicon microarchitectural contract fuzzing:** `cascade-artifacts-designs/cascade-meta` (`3565fba7ea0c`) with `comsec-group/cascade-artifacts` (`5f6b7c62b021`, USENIX Security 2024) targeting RISC-V RV32/RV64 RTL designs in Verilator/Modelsim against Spike, and `microsoft/sca-fuzzer` (`cc9fa2e53d92`, ASPLOS 2022) targeting x86-64 and ARM64 physical CPUs via Linux kernel-module execution against Unicorn/DynamoRIO contract emulators.

Relationships among subjects: `Minotaur` and `Souper` depend directly on `Alive2` (and transitively `Z3`) as their semantic oracle; `YinYang`/`TypeFuzz` fuzz `Z3` and `cvc5`; `Carcara` checks `cvc5`'s Alethe proofs while `cake_lpr` checks `CaDiCaL`'s LRAT/LPR proofs; `Cascade` and `Revizor` validate orthogonal layers below the compiler (RTL ISA fidelity vs. black-box silicon microarchitectural leakage contracts). Findings specific to individual source revisions (such as Minotaur's commented-out memory refinement or Revizor's `SetAnalyser` bug) are explicitly pinned to the inspected commit SHAs and must be revalidated before projecting onto other revisions.

## Findings

### 1. Cross-Layer Verification-Oracle Architecture and Trust-Boundary Matrix

Basis: source + documentation + derived

Every automated verification or superoptimization toolchain trusts lower layers to faithfully preserve semantics. The table below maps each examined system's input representation, search/generation strategy, oracle predicate, TCB boundary, and primary soundness failure mode.

| System | Layer & Target IR | Search / Generation Mechanism | Oracle / Equivalence Predicate | Trusted Computing Base (TCB) | Primary Soundness / Completeness Failure Mode |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **STOKE** (`StanfordPL/stoke`) | x86-64 assembly (`Cfg`) | Metropolis-Hastings MCMC over 9 weighted rewrite moves | Concrete sandbox testcases + `BoundedValidator` / `DdecValidator` SMT check | Hand-authored x86-64 `symstate` handlers + Z3/cvc4 | Unmodeled ISA corner cases, missing loop cutpoints/invariants, bounded unroll incompleteness |
| **Souper** (`google/souper`) | LLVM scalar SSA integer DAG (`souper::Inst`) | CEGIS enumerative + constant synthesis with dataflow pruning (`KnownBits`, `DemandedBits`) | Alive2/KLEE SMT refinement with dataflow `assume` and `DemandedBits` masking | `AliveDriver` IR translation + Alive2 semantics + Z3 | Dataflow-fact over-approximation, undef/poison mismatch if LLVM pass drops `freeze` |
| **Minotaur** (`minotaur-toolkit/minotaur`) | LLVM integer + FP + x86 SIMD IR slices | Loop-bounded slice extraction + enumerative synthesis + `llvm-mca` cost model | Alive2 $\exists \vec{c}.\ \forall \vec{x}.\ \text{refines}_{\text{relaxed\_nan}}$ + `compareFunctions` | Alive2 IR/x86-intrinsic semantics + Z3 + `llvm-mca` | Quantifier-polarity bugs on `nondet`/`undef`, commented-out memory refinement, NaN payload mismatch |
| **YinYang / TypeFuzz** (`testsmt/yinyang`) | SMT-LIB 2 formulas | Semantic fusion of same-verdict seeds (`SemanticFusion`) or type-preserving op mutation (`TypeAwareOpMutation`) | Known-verdict metamorphic oracle (`sat`/`unsat`) or cross-solver differential oracle | Fusion template invertibility / parser AST round-trip | Non-surjective or partial inverse templates, missing fusion constraints on UNSAT mode, sort clashes |
| **cvc5 + Carcara** (`cvc5`, `ufmg-smite/carcara`) | SMT-LIB 2 + Alethe proof scripts | CDCL(T) solver emitting Alethe proof tree | Independent Rust proof checker + optional elaborator (`carcara check`) | Carcara checker (~Rust) + any `--allowed-rules` + external `lia_generic` elaborator | Silent trust holes via `--allowed-rules` (reports `valid`), unchecked `lia_generic`, parser mismatch |
| **CaDiCaL + `cake_lpr`** (`arminbiere/cadical`, `tanyongkiam/cake_lpr`) | DIMACS CNF + binary/ASCII LRAT/LPR | CDCL + inprocessing with explicit clause-ID propagation chains | Linear-time RUP/RAT/PR hint-guided proof check | HOL4 proof kernel + CakeML verified compiler + small C FFI wrapper (`basis_ffi.c`) | CNF encoding / bit-blasting bugs upstream of DIMACS; heap exhaustion on huge proofs |
| **Cascade** (`cascade-artifacts-designs/cascade-meta`) | RISC-V RV32/RV64 ELF binaries on RTL | Asymmetric ISA pre-simulation entangling data and control flow via Spike resolution | Verilator/Modelsim termination (`stop request`) + fenced final register dump vs. Spike | Spike ISA model + Verilator/Modelsim RTL simulation | Bugs that neither trigger non-termination nor survive to final register dump (masked/overwritten state) |
| **Revizor** (`microsoft/sca-fuzzer`) | x86-64 / ARM64 machine code on real silicon | Random/taint-guided code + input-pair generation | Relational contract non-interference: $\text{CTrace}(i_1)=\text{CTrace}(i_2) \Rightarrow \text{HTrace}(i_1)\equiv\text{HTrace}(i_2)$ | Unicorn/DynamoRIO contract emulator + Linux kernel measurement module (`executor_km`) | Measurement noise vs. outlier filter bugs (`SetAnalyser`), incomplete speculation clauses, hidden side channels outside L1D cache |

---

### 2. Stochastic and Synthesizing Superoptimizers: STOKE, Souper, and Minotaur

#### 2.1 STOKE: Metropolis-Hastings MCMC Search, Cost Short-Circuiting, and Symbolic Equivalence

Basis: source + documentation

STOKE (`StanfordPL/stoke` @ `98d8a0f028f2`) formulates x86-64 superoptimization as Markov Chain Monte Carlo sampling from a Boltzmann-like target distribution $p(R) \propto \exp(-\beta \cdot \text{cost}(R))$ over candidate instruction sequences $R$ (`Schkufza, Sharma, Aiken, ASPLOS 2013`, DOI `10.1145/2451116.2451150`).

In `src/search/search.cc` (L41–125), each iteration proposes a move via a weighted selector over nine syntactic program transformations declared in `src/transform/all_transforms.h` (L16–25): `AddNops`, `Delete`, `GlobalSwap`, `Instruction`, `LocalSwap`, `Opcode`, `OpcodeWidth`, `Operand`, and `Rotate`. Rather than computing $\exp(-\beta(\text{new\_cost} - \text{current\_cost}))$ after full cost evaluation, `Search::run` draws $p \sim \text{Uniform}(0, 1]$ and computes the maximum acceptable cost threshold *before* invoking the cost function (`src/search/search.cc` L116–124):

```cpp
const auto p = prob_(gen_);
const auto max = state.current_cost - (log(p) / beta_);
const auto new_res = fxn(state.current, max);
const auto is_correct = new_res.first;
const auto new_cost = new_res.second;
if (new_cost > max) {
  (*transform_).undo(state.current, ti);
}
```

Because $\text{new\_cost} \le \text{current\_cost} - \frac{\ln p}{\beta} \iff p \le \exp(-\beta(\text{new\_cost} - \text{current\_cost}))$, this algebraic rearrangement is exact Metropolis-Hastings acceptance while enabling aggressive early termination inside `CorrectnessCost::operator()` (`src/cost/correctness.cc` L73–95): once accumulated bit-error distance across concrete sandbox test cases reaches `max`, remaining test cases are skipped immediately.

Correctness during search is strictly empirical (bit-level Hamming/ULP error across live-out GPRs, SSE registers, and the six status flags `CF, PF, AF, ZF, SF, OF` in `src/cost/correctness.cc` L54–70). Formal equivalence is discharged only post-search via two validators:
- **`BoundedValidator`** (`src/validator/bounded.cc` L36–64): enumerates finite CFG path pairs $(P, Q)$ up to a loop-unroll bound, constructs `StateEqualityInvariant` preconditions over `def_ins` and postconditions over `live_outs` (plus `MemoryEqualityInvariant` when `heap_out_ || stack_out_`), and invokes `ObligationChecker` over STOKE's symbolic x86-64 semantics (`src/symstate/`). On failure it extracts a concrete counterexample (`checker_get_target_ceg()`), which can be fed back into the testcase set.
- **`DdecValidator`** (`src/validator/ddec.cc`, `src/validator/cutpoints.cc`; `Sharma et al., OOPSLA 2013`, DOI `10.1145/2509136.2509509`): generalizes beyond bounded unrolling by discovering aligned loop cutpoints from concrete execution traces and synthesizing inductive relational invariants (conjunctions/disjunctions of register equalities, inequalities, flags, sign bits, and memory equality) checked by SMT across cutpoint-to-cutpoint straight-line paths.

For floating-point optimization (`Schkufza, Sharma, Aiken, PLDI 2014`, DOI `10.1145/2594291.2594305`), STOKE deliberately relaxes bit-exactness to tunable ULP error bounds over concrete inputs, trading formal soundness for speedups on math kernels where IEEE-754 exact equivalence blocks algebraic reassociation.

#### 2.2 Souper: Scalar LLVM SSA Extraction, Dataflow Facts, and Alive2 Refinement

Basis: source + documentation

Souper (`google/souper` @ `963d4df436f3`; `Sasnauskas et al., arXiv:1711.04422`) operates on LLVM integer SSA dataflow graphs rather than machine assembly, synthesizing peephole replacements via CEGIS (`lib/Infer/EnumerativeSynthesis.cpp`, `lib/Infer/ConstantSynthesis.cpp`) pruned by abstract interpretation (`lib/Infer/AbstractInterpreter.cpp`, `lib/Infer/Pruning.cpp`).

Crucially, Souper preserves *context-sensitive* LLVM dataflow facts that local peepholes miss. In `lib/Infer/AliveDriver.cpp` (L689–724), `AliveDriver` lowers each `souper::Inst` into an `Alive2` IR function and explicitly injects two semantic weakenings of the LHS:
1. **`translateDataflowFacts`** (L689–705): queries `DummyExprBuilder::getDataflowConditions(I)` (encoding LLVM path conditions, `KnownBits` zero/one masks, `PowerTwo`, `NonZero`, `Negative`, `NonNegative`, `SignBits`, and `Range` metadata) and emits `Builder.assume(ExprCache[DataFlowConstraints])` into the Alive2 function.
2. **`translateDemandedBits`** (L708–724): masks both LHS and RHS outputs with `IR::BinOp::And` against `LHS->DemandedBits` whenever `!DemandedBits.isAllOnes()`, permitting the synthesizer to ignore don't-care output bits.

Because `Souper`'s IR covers scalar integer operations (`Add`/`Sub`/`Mul`/`Shl` with `NSW`/`NUW`, `LShr`/`AShr`/`UDiv`/`SDiv` with `Exact`, saturating arithmetic `SAddSat`–`USubSat`, overflow intrinsics, funnel shifts `FShl`/`FShr`, `CtPop`, `Ctlz`, `Cttz`, `BSwap`, `BitReverse`, in `lib/Infer/AliveDriver.cpp` L615–686), it omits vector shuffles, floating-point operations, and memory side effects.

#### 2.3 Minotaur: SIMD Slicing, `llvm-mca` Costing, and Subtle SMT Refinement Traps

Basis: source + execution + documentation

Minotaur (`minotaur-toolkit/minotaur` @ `f764ac4eb2c5`; `Liu, Mada, Regehr, OOPSLA 2024`, DOI `10.1145/3689766`, `arXiv:2306.00229v3`) extends synthesizing superoptimization to LLVM integer and floating-point SIMD IR and x86-64 vector intrinsics (achieving 7.3% average / 13% max speedup on GMP and 1.5% average / 4.5% max speedup on SPEC CPU 2017 on Intel Cascade Lake).

Source inspection of Minotaur's four core modules reveals critical architectural invariants and sharp soundness seams:

1. **Loop-Bounded SSA Slicing (`lib/slice.cpp` L96–155):** `Slice::extractExpr(Value &v)` extracts a standalone LLVM `Function` ("cut") rooted at instruction `v`. If `v` resides inside a loop (`Loop *loopv = LI.getLoopFor(vbb)`), Minotaur requires `loopv->isLoopSimplifyForm()` (L113) and refuses to harvest instructions across loop boundaries (`if (loopi != loopv)`, L149–150); values defined outside the slice become unconstrained symbolic function arguments.
2. **External `llvm-mca` Cost Model With Approximate Fallback (`lib/cost.cpp` L27–115):** `get_machine_cost(Function *F)` serializes the candidate LLVM function to a temporary file and executes `GET_COST_COMMAND` (wrapping `llc` + `llvm-mca`) with a 30-second timeout (L97). If `llvm-mca` fails or times out, it falls back silently to `get_approx_cost(F)` (L113), meaning microarchitectural cost rankings can degrade to static IR heuristics under toolchain mismatch.
3. **Refinement Encoding, Quantifier Polarity, and NaN Payload Relaxation (`lib/alive-interface.cpp` L32–360):** Minotaur validates and synthesizes constants (`%_reservedc*`) using `Alive2` (`AliveToolkit/alive2` @ `3bdd4f5e1cef`, PLDI 2021, DOI `10.1145/3453483.3454030`). Direct inspection of `AliveEngine::find_model` exposes five subtle soundness mechanics:
   - **LLVM Refinement Judgment:** For a candidate rewrite $\text{src} \leadsto \text{tgt}$ with inputs $\vec{x}$ and reserved constants $\vec{c}$, Alive2 requires:
     $$\exists \vec{c}.\ \forall \vec{x}, \vec{q}_{\text{src}}, \vec{u}_{\text{src}}.\ \bigl(\text{pre}_{\text{tgt}} \land (\text{pre}_{\text{src}} \implies (\text{np}_{\text{src}} \implies \text{np}_{\text{tgt}}) \land (\text{np}_{\text{src}} \land \text{np}_{\text{tgt}} \implies \text{val}_{\text{src}} \approx \text{val}_{\text{tgt}}))\bigr)$$
     Real function inputs are constrained non-poison via `input_nonpoison_cnstr` (L180–196) so the solver cannot "cheat" by picking poison inputs, whereas reserved constants `%_reservedc*` may synthesize to poison.
   - **Precondition Folding Bug Trap (`lib/alive-interface.cpp` L139–152):** Simplifying $\text{pre}_{\text{tgt}} \land (\text{pre}_{\text{src}} \implies \text{refines})$ to $\text{pre}_{\text{tgt}} \land \text{refines}$ is sound *only* when $\text{pre}_{\text{src}}$ and $\text{pre}_{\text{tgt}}$ are structurally identical (`pre_src.eq(pre_tgt)`). The source explicitly notes two past bugs: folding unconditionally weakens the antecedent and accepts invalid FP candidates (e.g., `tests/fp/case11.syn.ll`), and using C++ `operator==` on `smt::expr` constructs an SMT equality AST instead of returning a host `bool`.
   - **Quantifier Polarity on Source Nondeterminism (`lib/alive-interface.cpp` L230–266):** All Alive2 source quantified variables (`src_state.getQuantVars()`), target call quantified variables (`tgt_state.getFnQuantVars()`), and source nondeterminism variables (`src_state.getNondetVars()`) *except* `maxminnondet*` tie-breaking variables are inserted into `qvars` (universally quantified). Leaving source nondeterminism/undef variables as free top-level existentials lets Z3 pick an adversarial witness that collapses non-constant functions to a bogus constant. Note an internal code/comment tension: L206–208 comments that NaN choice variables are omitted from `qvars`, while L257–264 adds all `src_state.getNondetVars()` except `maxminnondet*`.
   - **Conditional NaN Payload Relaxation (`refines_relaxed_nan`, L32–86):** Because Alive2's `FloatType::fromFloat` emits nondeterministic NaN payload variables (`#NaN*`, `choice*`, `#preferred_qnan`), strict bit-equality rejects valid FP optimizations. `refines_relaxed_nan` inspects `e.vars()` and relaxes equality to `(src_nan && tgt_nan) || (src.value == tgt.value)` *only* when at least one side contains a nondeterministic NaN variable, preserving exact NaN payload bits for explicit SNaN bit-manipulation tests (such as `half` `insertelement` of `0x7C01`).
   - **Poison-Lane Bias and Commented-Out Memory Refinement (`lib/alive-interface.cpp` L276–360):** Lines 276–283 contain a commented-out block for `src_mem.refined(tgt_mem, false)` (`// TODO: add memory back here`), meaning `find_model` constant synthesis does not enforce memory refinement directly (Minotaur relies on a final full-function `AliveEngine::compareFunctions` check at L115–121). Furthermore, lines 319–360 implement a greedy post-SAT loop (`synthesis_prefer_poison`) that pushes `!np` (or per-lane `0` bits for vector `non_poison` bitvectors) onto the Z3 solver to maximize poison lanes in `%_reservedc*` constants (for example, don't-care lanes in `shufflevector` masks)—directly contradicting an outdated comment at L285–288 claiming non-poison preference.

#### 2.4 Executable Micro-Probe 1A: 4-Bit `poison` Refinement Asymmetry and Quantifier-Polarity Collapse

Basis: execution

To verify both LLVM `nsw` poison-refinement directionality and the quantifier-polarity soundness hazard documented in `minotaur/lib/alive-interface.cpp` L230–264, a standalone exhaustive `i4` (4-bit two's-complement, 16-state) checker was executed (`python3`, exact enumeration over all 16 inputs):

- `add nsw i4 x, x` $\leadsto$ `shl nsw i4 x, 1` and reverse: **valid** (0/16 counterexamples; both poison identically on $x \in \{4,5,6,7,-8,-7,-6,-5\}$).
- `mul nsw i4 x, 2` $\leadsto$ `shl nsw i4 x, 1`: **valid** (0/16 counterexamples).
- `add nsw i4 x, x` $\leadsto$ `add i4 x, x` (dropping `nsw`): **valid** (0/16 counterexamples; target is defined wherever source is non-poison).
- `add i4 x, x` $\leadsto$ `add nsw i4 x, x` (introducing `nsw`): **invalid** (8/16 counterexamples; first counterexample $x = 4$, where `src = (8, non_poison=True)` and `tgt = (8, non_poison=False)`).
- **Quantifier-polarity test** on $\text{src}(x, u) = (u = 0 \mathbin{?} 0 : (x + 1) \bmod 16)$ against constant target $\text{tgt}(c) = c$:
  - Buggy encoding $\exists c \in [0,15],\, u \in \{0,1\}.\ \forall x.\ \text{src}(x, u) = c$: **SAT** with model `(c=0, u=0)`—unsoundly collapsing a non-constant expression to `ret i4 0`.
  - Sound encoding $\exists c \in [0,15].\ \forall x \in [0,15],\, u \in \{0,1\}.\ \text{src}(x, u) = c$: **UNSAT** (`[]`), rejecting the invalid constant synthesis.

---

### 3. Fuzzing the SMT Oracles Themselves: Semantic Fusion, Type-Aware Mutation, and Independent Proof Checking

Superoptimizers and bounded verifiers treat Z3 and cvc5 as ground truth. However, solver soundness bugs—specifically *refutation-soundness bugs* (returning `unsat` on a satisfiable verification condition, silently certifying an invalid optimization or buggy program)—regularly occur in theory combination, nonlinear arithmetic, bit-vectors, strings, and quantifier instantiation.

#### 3.1 YinYang: Semantic Fusion Algebraic Invariants

Basis: source + execution + documentation

`YinYang` (`testsmt/yinyang` @ `5ce963290b68`; `Winterer, Zhang, Su, PLDI 2020`, DOI `10.1145/3385412.3385985`) solves the SMT test-oracle problem without requiring a second solver by fusing two seed formulas $\phi_1(\vec{x})$ and $\phi_2(\vec{y})$ that have the *same* known satisfiability verdict (`sat` or `unsat`) into a coupled formula whose verdict is algebraically preserved.

Direct inspection of `yinyang/src/mutators/SemanticFusion/SemanticFusion.py` (L52–169) and `VariableFusion.py` (L117–180) establishes the exact transformation:

1. **Variable renaming & sort-clash guard (`SemanticFusion.py` L63, L143–156):** Variables are disjointly prefixed (`scr1_`, `scr2_`). If both scripts declare user-defined sorts with colliding names (`sort_clash`), mutation aborts immediately because sorts are not alpha-renamed.
2. **Invertible fusion templates (`SemanticFusion.py` L104–133):** For selected variable pairs $(x, y)$ of matching sorts, a template defines a fresh fusion variable $z$, a forward fusion relation $z = f(x, y)$ (with random constants drawn from `[-1000, 1000]` for `Int`/`Real`, length `0..20` lowercase ASCII for `String`, or full-width random bitvectors in `VariableFusion.py` L117–152), and inverse terms $f_x^{-1}(y, z)$ and $f_y^{-1}(x, z)$ satisfying $f_x^{-1}(y, f(x, y)) = x$ and $f_y^{-1}(x, f(x, y)) = y$. A random subset of $k \in [0, |\text{occ}(x)|]$ occurrences of $x$ in $\phi_1$ is replaced by $f_x^{-1}(y, z)$ (and symmetrically for $y$ in $\phi_2$).
3. **Asymmetric Oracle Combination (`SemanticFusion.py` L134–140):**
   - **UNSAT oracle (`self.oracle == "unsat"`):** emits $(\phi_1' \lor \phi_2') \land \bigwedge_i \text{constr}_i$, calling `disjunction(formula1, formula2)` followed by `add_fusion_constraints(formula, fusion_constr)`. The explicit constraint $z = f(x, y)$ is *mandatory*: under $z = f(x, y)$, every substituted term $f_x^{-1}(y, z)$ evaluates to $x$, so $\phi_1' \equiv \phi_1$ and $\phi_2' \equiv \phi_2$, ensuring $\phi_1' \lor \phi_2'$ remains UNSAT.
   - **SAT oracle (`self.oracle == "sat"`):** emits $\phi_1' \land \phi_2'$ via `conjunction(formula1, formula2)` **without** calling `add_fusion_constraints`. Because any satisfying assignment $(x^*, y^*)$ of $\phi_1 \land \phi_2$ extends to $(x^*, y^*, z^* = f(x^*, y^*))$, setting $z = z^*$ makes $f_x^{-1}(y^*, z^*) = x^*$ and $f_y^{-1}(x^*, z^*) = y^*$ simultaneously for all substituted and unsubstituted occurrences, so the conjunction remains SAT *even without explicitly asserting $z = f(x, y)$* (which in fact relaxes the formula, making SAT strictly preserved).

**Executable Micro-Probe 1B** (`BV4`, exhaustive over all $16^3 = 4096$ assignments of $(x, y, z)$) confirmed every edge of this contract:
- Bijective XOR fusion $f(x, y) = x \oplus y$ on UNSAT pair $(\phi_1: x + 1 = x,\, \phi_2: y \oplus 1 = y)$ with partial 1-of-2 occurrence substitution: **UNSAT** (`SAT=False`) with `z == x ^ y`, but **broken** (`SAT=True`) if `add_fusion_constraints` is omitted.
- Same bijective XOR fusion on SAT pair $(\psi_1: x + 3 = 7,\, \psi_2: y \oplus 5 = 12)$ without `fusion_constr`: preserves SAT under both full substitution (16 models) and partial substitution (exact witness `(x=4, y=9, z=13)`).
- Non-surjective inverse $f(x, y) = (2x + y) \bmod 16$ with broken half-width inverse `((z - y) & 15) >> 1` on SAT witness $x = 12$ (MSB set): **broken** (`SAT_count=0`), falsely turning a SAT seed into UNSAT and causing false-positive soundness bug reports against correct solvers.

#### 3.2 Type-Aware Operator Mutation (`TypeFuzz` / `OpFuzz`)

Basis: source + documentation

In `yinyang/src/mutators/TypeAwareOpMutation.py` (L29–123; `Winterer, Zhang, Su, OOPSLA 2020`, DOI `10.1145/3428261`), `TypeAwareOpMutation` replaces operators and quantifiers inside existing well-typed SMT-LIB 2 formulas using signature-preserving operator equivalence classes parsed from a config file:
- **Bidirectional classes** (`op1, op2, ...`, L57–58): any operator or quantifier in the class may mutate into any distinct member (e.g., `=`, `distinct`; `<`, `<=`, `>`, `>=`; `forall`, `exists`; `bvadd`, `bvsub`, `bvmul`, `bvxor`).
- **Unidirectional rules** (`op_from -> op_to1, op_to2`, L51–55): permit type-valid weakenings/conversions that are not symmetric.
- **Arity gating (`arities_mismatch`, L60–73):** enforces exact (`N`), minimum (`N+`), or maximum (`N-`) subterm arity before rewriting.
- **Solver-compatibility rollback (L115–120):** when `cvc5_compat` is active, mutations producing cvc5-rejected constructs (such as mutating `=` to `distinct` over `RegLan` regular-expression definitions) are rolled back immediately via `cvc5_unsupported(self.formula)`.

Because operator mutation does not preserve satisfiability, `TypeFuzz`/`OpFuzz` relies on *differential testing* across solvers (`Z3` vs. `cvc5`) or across distinct solver flag configurations (`OptionGenerator.py`), catching soundness bugs whenever one configuration returns `sat` and another returns `unsat` on the identical mutated benchmark.

#### 3.3 Closing the Oracle Gap: Z3 Internal Proofs vs. cvc5 + Carcara (Alethe) vs. CaDiCaL + `cake_lpr` (LRAT)

Basis: source + documentation

Fuzzing finds solver bugs probabilistically but cannot certify any single `unsat` verdict. Reducing the verification TCB requires checking solver-produced refutation proofs independently. Source inspection across three production proof stacks highlights a stark TCB-vs.-expressiveness trade-off:

| Stack | Proof Format | Independent Checker? | TCB Size & Verified Status | Known Soundness / Trust Gaps |
| :--- | :--- | :--- | :--- | :--- |
| **Z3** (`Z3Prover/z3` @ `c73b745cef36`) | Proprietary natural-deduction proof AST (`proof_checker.cpp`) | No — internal to Z3 | Shares Z3 `ast_manager`, `th_rewriter`, `arith_decl_plugin` | `proof_checker::check` (`src/ast/proofs/proof_checker.cpp` L103–136) relies on Z3's own `th_rewriter` and outputs unchecked `side_conditions` for coarse theory lemmas; `check1_spc` is compiled out (`#if 0`). |
| **cvc5 + Carcara** (`cvc5/cvc5` @ `7507ed17e261`, `ufmg-smite/carcara` @ `193b1b015d29`) | **Alethe** (`alethe_proof_rule.h`, `Schurr et al., PxTP 2021`, DOI `10.4204/EPTCS.336.6`) | Yes — standalone Rust checker (`Carcara`, TACAS 2023, DOI `10.1007/978-3-031-30823-9_19`) | Unverified Rust codebase (parallel top-level step checking, shared read-only term pool) | (1) `lia_generic` is NP-hard and **not checked** directly (`docs/src/checking.md` L36–41) unless elaborated externally; (2) `--allowed-rules` skips rules **while still reporting `valid`** rather than `holey` (L22–34); (3) non-elaborated proofs allow implicit equality reordering and omitted resolution pivots (`src/checker/mod.rs` L85–92). |
| **CaDiCaL + `cake_lpr`** (`arminbiere/cadical` @ `6b3d70b9ce00`, `tanyongkiam/cake_lpr` @ `033aad53d173`) | **LRAT / LPR** (`Cruz-Filipe et al., CADE 2017`, DOI `10.1007/978-3-319-63046-5_14`) | Yes — machine-code verified checker (`Tan, Heule, Myreen, TACAS 2021`, DOI `10.1007/978-3-030-72013-1_12`) | HOL4 proof kernel + CakeML verified compiler (`HOL4 9783a499`, `CakeML 665f9b21`) + small C FFI wrapper (`basis_ffi.c`) | Covers propositional CNF (and bit-blasted `QF_BV`) only; does not cover SMT theory reasoning (`LIA`, `Arrays`, `FP`, `Strings`) or the CNF/bit-blasting translator itself. |

Concrete source details essential for safe deployment:
- **`cvc5` Alethe Context Anchors (`src/proof/alethe/alethe_proof_rule.h` L33–81):** Alethe steps have the form $\Gamma \triangleright i.\, F$, where context $\Gamma$ carries variable bindings and substitutions introduced by `anchor` subproofs (`ANCHOR_SUBPROOF`, `ANCHOR_BIND`, `ANCHOR_SKO_FORALL`, `ANCHOR_SKO_EX`, `ANCHOR_ONEPOINT`). Skolemization binds choice terms $x \mapsto (\text{choice}\ (x)\ F_1)$ directly in the context without introducing fresh global Skolem axioms.
- **`Carcara` Strictness Configuration (`src/checker/mod.rs` L84–110, `docs/src/checking.md` L14–49):** Security-critical pipelines invoking `carcara check` MUST pass `--elaborated` (rejecting implicit equality reordering in `assume`/`refl` and requiring explicit pivots in `resolution`/`th_resolution`), MUST NOT pass `--allowed-rules` or `--ignore-unknown-rules`, and MUST reject `holey` exit states as untrusted.
- **`CaDiCaL` Binary LRAT Wire Format (`src/lrattracer.cpp` L40–115):** Each added clause emits `'a'` followed by LEB128-encoded clause ID `2 * |id| + (id < 0)`, literal list `2 * |lit| + (lit < 0)` terminated by `0`, and explicit antecedent clause-ID propagation chain terminated by `0`; deletions emit `'d'` followed by deleted IDs. Because explicit propagation hints eliminate unit-propagation search during verification, `cake_lpr` verifies large UNSAT proofs in linear time (`s VERIFIED UNSAT`), supporting both binary LRAT/LPR (since March 2024) and two-level parallelized transformation proofs (`README.md` L22, L46–50). Note a July 2026 CLI breaking change in `cake_lpr` (`README.md` L18): heap/stack limits must be passed via `--CML_HEAP_SIZE=<n>` / `--CML_STACK_SIZE=<n>` (default 4096 MiB each), as the `CML_HEAP_SIZE`/`CML_STACK_SIZE` environment variables are no longer read.

---

### 4. Pre-Silicon CPU RTL Fuzzing: Cascade Asymmetric ISA Pre-Simulation and Termination Cascades

Basis: source + documentation

Even when a compiler and SMT solver are bug-free, RTL hardware designs frequently violate their ISA specifications—especially across privilege transitions, FPU state enablement (`mstatus.FS`), CSR side effects, exceptions, and deep out-of-order pipeline interactions. Conventional RTL fuzzers (such as RFUZZ or DifuzzRTL) either fail to generate valid long instruction streams (crashing on illegal addresses or traps within tens of instructions) or pay severe runtime overhead running per-instruction lockstep co-simulation against a golden ISA model.

`Cascade` (`cascade-artifacts-designs/cascade-meta` @ `3565fba7ea0c`, `comsec-group/cascade-artifacts` @ `5f6b7c62b021`; `Solt, Ceesay-Seitz, Razavi, USENIX Security 2024`) resolves both bottlenecks through **asymmetric ISA pre-simulation** and the **termination cascade-effect**:

1. **Two-Stage Asymmetric Construction (`fuzzer/cascade/basicblock.py` L31–160):**
   - *Stage A (Skeleton Generation with Placeholders):* `gen_basicblocks` resets `fuzzerstate`, emits an initial basic block at `SPIKE_STARTADDR`, allocates non-overlapping memory regions (`memview`) for a random data block, store locations, a reserved final block, a reserved context-setter block, and a sequence of randomized basic blocks up to `nmax_bbs`, `LIMIT_MEM_SATURATION_RATIO`, or max instruction count (L35–78). Instructions that compute dynamic control-flow targets (`JALR`), memory addresses (`Load`/`Store`), or privilege/exception transitions are emitted with symbolic placeholder producers/consumers (`PlaceholderConsumerInstr`), while registers are tracked via a finite-state machine (`IntRegIndivState`: `FREE`, `CONSUMED`, etc.).
   - *Stage B (Spike Pre-Simulation & Entanglement):* The skeleton program is executed once on the fast Spike ISA simulator to observe the exact architectural register values produced by preceding random arithmetic/CSR/FP instructions. Cascade then patches the placeholder immediate offsets (`producer_id_to_tgtaddr`, L97) so that `JALR` jump targets, branch predicates, and load/store addresses are *algebraically computed from the live runtime register values* (`base_reg XOR expected_val + target_addr`), entangling data flow and control flow across the entire program (up to 100,000 instructions).
   - *Address Blacklisting & Spike Debug Workaround (`basicblock.py` L87–92, L124–132):* Cascade blacklists loads from addresses whose instruction bytes change between Spike resolution and RTL execution (`blacklist_changing_instructions`, `blacklist_final_block`, `blacklist_context_setter`). Notably, source comments at L124–132 document a concrete cross-tool seam: back-to-back `CONSUMED` placeholder-consumer chains (`JALR`/Load/Store reading a freshly written consumer `rd`) break Spike's debug-mode resolution on upstream `CVA6`, so Cascade injects two `nop` bubbles solely when that exact back-to-back dependency materializes.
2. **Termination Cascade and Fenced End-of-Run Oracle (`finalblock.py` L20–101, `fuzzsim.py` L25–220):**
   - Because later control-flow targets and memory addresses depend on earlier architectural results, *any* RTL bug that corrupts a register, CSR, exception vector, or memory value typically causes a subsequent computed `JALR` or branch to jump into invalid/looping code, preventing the CPU from ever reaching the final block (**termination cascade**).
   - If the RTL simulation *does* reach `finalblock`, the final block executes `fence`, stores every architectural integer register `x1..xN` to `regdump_addr` (`sd` on RV64 / `sw` on RV32) separated by per-register `fence` instructions (L53–56, preventing speculative store reordering), enables the FPU via `csrrw x0, mstatus, FPU_ENDIS_REGISTER_ID` if in Machine mode (`PrivilegeStateEnum.MACHINE`, L64–67), dumps floating-point registers `f0..fM` to `regdump_addr + 8`, and writes to `stopsig_addr` (triggering `'Found a stop request.'`).
   - `runtest_simulator` (`fuzzsim.py` L154–220) runs Verilator or Modelsim with cycle budget `num_instrs * MAX_CYCLES_PER_INSTR + SETUP_CYCLES` (`MAX_CYCLES_PER_INSTR = 30`, `SETUP_CYCLES = 1000`, tuned to prevent false timeouts on BOOM for `<20`-instruction programs, L25–26). A bug is flagged on either (a) timeout / missing stop request, or (b) final register mismatch against Spike on any `FREE`/`CONSUMED` integer register or dumped FP register.
3. **Automated Program Reduction (`fuzzer/cascade/debug/debugreduce.py`):** Because triggering programs can exceed $10^4$ instructions, Cascade automatically binary-searches and truncates basic blocks (re-synthesizing a prefix + context-setter + final block) to isolate a minimal reproducing instruction sequence.
4. **Empirical Yield (`comsec-group/cascade-artifacts`, USENIX Security 2024):** Across 5 RISC-V CPUs (`PicoRV32`, `Kronos`, `VexRiscv`, `CVA6`, `Rocket`/`BOOM`, enumerated in `design_repos.json`), Cascade achieved 28.2×–97× higher coverage than prior CPU fuzzers and uncovered 37 new bugs (28–29 CVEs), including privilege-escalation, FPU/CSR corruption, and microarchitectural pipeline-flush bugs invisible to short random tests.

---

### 5. Black-Box Silicon Leakage-Contract Fuzzing: Revizor and Hardware-Software Contracts

Basis: source + execution + documentation

RTL fuzzing verifies *architectural* ISA equivalence and requires white-box Verilog/Chisel source. Commercial x86-64 and ARM64 processors are black-box silicon whose primary verification failures are *microarchitectural side-channel leaks* (Spectre v1/v4, Meltdown, MDS, Retbleed, LVI, Zenbleed, Data Memory-Dependent Prefetchers) that preserve architectural ISA semantics while violating constant-time security assumptions.

#### 5.1 Relational Hardware-Software Contracts

Basis: normative + documentation + source

Following the Hardware-Software Contract framework (`Guarnieri, Köpf, Reineke, Vila, IEEE S&P 2021`, DOI `10.1109/SP40000.2021.00030`) and its black-box testing instantiation in `Revizor` (`microsoft/sca-fuzzer` @ `cc9fa2e53d92`; `Oleksenko, Fetzer, Köpf, Silberstein, ASPLOS 2022`, DOI `10.1145/3503222.3507729`), a contract $\mathcal{C} = (\text{Obs}, \text{Exec})$ maps a program $p$ and initial architectural state/input $i$ to a deterministic **contract trace** $\text{CTrace}_{\mathcal{C}}(p, i)$:
- **Observation clause (`contract_observation_clause`):** defines what software expects to leak—e.g., `ct` (program counter and memory access addresses, matching constant-time programming), `arch` (loaded values as well), or `ct-ni` (Actor Non-Interference across victim/attacker domains, `docs/howto/choose-contract.md` L65–75).
- **Execution clause (`contract_execution_clause`):** defines which transient paths the contract *permits* to produce observations—e.g., `seq` (strictly sequential, zero-knowledge baseline `CT-SEQ`), `cond` (conditional branch misprediction / Spectre v1, `X86CondSpeculator`), `bpas` (store-to-load forwarding bypass / Spectre v4), or `deh` (delayed exception handling in out-of-order pipelines, `UnicornDEH`).

A physical CPU **satisfies** contract $\mathcal{C}$ on program $p$ iff for all input pairs $(i_1, i_2)$:
$$\text{CTrace}_{\mathcal{C}}(p, i_1) = \text{CTrace}_{\mathcal{C}}(p, i_2) \implies \text{HTrace}(p, i_1) \equiv \text{HTrace}(p, i_2)$$
where $\text{HTrace}(p, i)$ is the measured microarchitectural observation (e.g., 64-line L1D Prime+Probe cache-set bitmap collected by `rvzr/executor_km/` inside Ring 0 / EL1 over repeated samples).

#### 5.2 Speculative Contract Emulators and Equivalence-Class Analysis

Basis: source + execution

Inspection of `microsoft/sca-fuzzer` (`cc9fa2e53d92`) documents the exact operational semantics and two load-bearing implementation caveats:

1. **Unicorn Speculation Checkpointing (`rvzr/model_unicorn/speculators_basic.py`, `speculators_fault.py`):**
   - `X86CondSpeculator` (`speculators_basic.py` L53–180) hooks every x86-64 instruction (skipping undefined instructions with `size > 15`), decodes all 1-byte (`0x70..0x7F`, `0xE0..0xE3`) and 2-byte (`0x0F 0x80..0x8F`) conditional jumps against live `EFLAGS`/`RCX`, checkpoints architectural state up to a maximum nesting depth, and forces speculative execution down the *mispredicted* branch before rolling back to the architectural path.
   - `UnicornDEH` (`speculators_fault.py` L95–120) models delayed exception handling on faulting errnos `{6, 10, 12, 13, 21}` by tracking data-dependency sets (`_dependencies`) so non-dependent younger instructions execute transiently while dependent instructions are suppressed until exception retirement.
   - **Deprecated Unknown-Value Speculation (`speculators_vs.py` L54–107):** `_VspecBaseSpeculator` (implementing the VSOps algorithm for Meltdown/MDS value-speculation leakage over arbitrary unknown values) unconditionally raises `NotImplementedError("This class and its subclasses are no longer maintained.")` in `__init__` at L105, and notes broken `_load_input` interfaces (`FIXME`, L110–112). Users targeting exception-data leaks must not assume `vs` speculators function on current `main`.
2. **Equivalence-Class Analyser (`rvzr/analyser.py` L67–250) and Upstream `SetAnalyser` Bug:**
   - `EquivalenceAnalyserCommon.filter_violations` (L85–149) discards empty/corrupted `HTrace` entries, buckets inputs by identical `CTrace` (`ContractEqClass`), drops singleton classes (`len < 2`), partitions each effective class into `HardwareEqClass` clusters using `self.htraces_are_equivalent`, and reports a `Violation` iff `len(hw_classes) >= 2`.
   - `MergedBitmapAnalyser` (L152–200) computes `threshold = CONF.analyser_outliers_threshold * sample_size`, counts trace frequencies with `Counter(raw)`, filters out noisy samples where `counter[x] < threshold` (L184–185), bitwise-ORs surviving 64-bit cache bitmaps, and compares equality (or subset inclusion `((b0 & ~b1) == 0) || ((b1 & ~b0) == 0)` when `CONF.analyser_subsets_is_violation` is `False`).
   - **Upstream Bug in `SetAnalyser` (`rvzr/analyser.py` L209–224):** Lines 214–215 write:
     ```python
     filtered1 = [x for x in htrace1.get_raw_traces() if x >= threshold]
     filtered2 = [x for x in htrace2.get_raw_traces() if x >= threshold]
     ```
     Unlike `MergedBitmapAnalyser`, `SetAnalyser` omits `Counter(raw)` and compares the *raw 64-bit cache-line bitmap integer* `x` directly against `threshold` instead of comparing its occurrence count `counter[x] >= threshold`.
   - **Executable Micro-Probe 1C** verified the impact on two inputs with identical `CTrace`, `sample_size = 100`, `analyser_outliers_threshold = 0.1` (`threshold = 10.0`), where input 1 yields 100 clean traces (`1 << 10 = 1024`) and input 2 yields 99 clean traces plus 1 noisy interrupt outlier (`(1 << 10) | (1 << 20)`):
     - `MergedBitmapAnalyser` (`subsets_is_violation=True`): `equiv=True` (correctly filters the 1% outlier; zero false positive).
     - Upstream `SetAnalyser` (`subsets_is_violation=True`): `equiv=False` (**spurious contract violation**, because the outlier bitmap integer `1049600 >= 10.0` bypasses frequency filtering).
     - Upstream `SetAnalyser` (`subsets_is_violation=False`): `equiv=True` (the bug is accidentally masked only because `{1024}` is a subset of `{1024, 1049600}`).
   - Statistical alternatives (`MWUAnalyser` Mann-Whitney U test at L226–248 and `ChiSquaredAnalyser` at L250+) avoid bitmap thresholding but are explicitly marked experimental (`warning("analyser", ...)` at L235–236).
3. **Iterative Root-Cause Discovery Workflow (`docs/howto/choose-contract.md` L9–92):** Campaigns begin with `CT-SEQ` (strictest zero-knowledge baseline). Once a known leakage source (e.g., Spectre v1 conditional branches) triggers violations, operators either add offending opcodes to `instruction_blocklist_append` (preserving `CT-SEQ`'s low emulation cost) or weaken the execution clause to `CT-COND` / `CT-DEH` to search for orthogonal, previously unknown speculation mechanisms.

---

### 6. End-to-End Compositional Verification Implications

Basis: derived

Inspecting all four verification layers together reveals a structural asymmetry across the computing stack:

1. **Formal proofs do not bridge unvalidated oracle transitions:** A superoptimized LLVM pass (`Souper`/`Minotaur`) verified by `Alive2` + `Z3` remains vulnerable to (a) `Alive2` IR-to-SMT encoding bugs (such as Minotaur's quantifier-polarity and precondition-folding pitfalls), (b) Z3 refutation-soundness bugs of the class `YinYang`/`TypeFuzz` routinely uncover, and (c) backend lowering/microarchitecture mismatches below LLVM IR.
2. **Concrete hardening recipe for compiler and verification toolchains:**
   - Discharge critical bit-vector/propositional equivalence queries through `cvc5` + `Carcara --elaborated` (rejecting `holey` and prohibiting `--allowed-rules`) or bit-blast to `CaDiCaL` LRAT checked by `cake_lpr`, eliminating solver refutation-soundness bugs from the TCB.
   - When writing synthesis queries over languages with `undef`, `poison`, or NaN payload nondeterminism, universally quantify *all* source nondeterminism variables and validate synthesized candidates with an independent full-function translation validator (`compareFunctions` with memory refinement enabled) rather than trusting the synthesis query alone.
   - Treat ISA models (`Spike`, `Unicorn`) as two-sided boundaries: test RTL implementations against the ISA model via deep entangled program generation (`Cascade`), and test physical silicon against relational leakage contracts (`Revizor` with `MergedBitmapAnalyser` or corrected frequency-filtered `SetAnalyser`) rather than assuming architectural correctness implies side-channel safety.

## Boundaries

- **Known not to apply:**
  - `Souper` (`google/souper` @ `963d4df436f3`) does not apply to floating-point arithmetic, vector shuffles, or memory-mutating instructions; those require `Minotaur` or separate memory-aware validators.
  - `YinYang` `SemanticFusion` UNSAT mode does not preserve unsatisfiability if `fusion_constr` is omitted or if fusion templates lack exact surjectivity/invertibility over the target SMT theory (confirmed by Probe 1B).
  - `Carcara` `valid` verdicts do not guarantee zero unchecked steps if `--allowed-rules` is passed (`docs/src/checking.md` L22–30), and `Carcara` does not check `lia_generic` steps without external elaboration (`docs/src/checking.md` L36–41).
  - `cake_lpr` applies strictly to propositional CNF/LRAT/LPR refutations and transformation proofs; it does not check higher-level SMT theory steps (`LIA`, `Arrays`, `FP`, `Strings`) or the soundness of a frontend bit-blaster.
  - `Cascade`'s termination-cascade oracle applies to pre-silicon RTL simulation with architectural Spike comparison; it does not detect purely microarchitectural side-channel leaks that leave final architectural registers and termination behavior intact.
  - `Revizor` applies to relational microarchitectural leakage against a specified contract and measurement channel (e.g., L1D cache); passing `Revizor` does not prove absence of leaks on unmeasured channels (port contention, power/DVFS, unmodeled DMP triggers) or untested instruction combinations.
- **Unsupported:**
  - Unknown-value speculation (`_VspecBaseSpeculator` / VSOps in `microsoft/sca-fuzzer` @ `cc9fa2e53d92`, `rvzr/model_unicorn/speculators_vs.py` L105) is explicitly unsupported (`NotImplementedError`) on the inspected revision.
  - `Minotaur`'s `AliveEngine::find_model` (`lib/alive-interface.cpp` L276–283) currently omits memory refinement during constant synthesis (`// TODO: add memory back here`), and `Slice::extractExpr` (`lib/slice.cpp` L113–150) refuses non-loop-simplified loops and cross-loop slices.
  - `Cascade`'s `finalblock` (`fuzzer/cascade/finalblock.py` L30–32) asserts `regdump_addr < 0x80000000` and `stopsig_addr < 0x80000000` (sign-extension for upper-half addresses is unimplemented).
- **Not examined:**
  - Live execution of `STOKE`, `Souper`, `Minotaur`, `Cascade` (Verilator/Modelsim RTL simulation), `Revizor` (`executor_km` bare-metal Ring-0 kernel module), or `Carcara`/`cake_lpr` binaries on benchmark suites was not performed in this observation; execution evidence consists of self-contained semantic and analyser micro-probes (Probes 1A–1C).
  - `STOKE`'s full x86-64 `src/validator/handlers/` table (exact instruction coverage and known unmodeled AVX-512/system instructions) was not exhaustively audited.
  - `Revizor`'s ARM64 backend (`rvzr/arch/arm64/`, `rvzr/executor_km/arm64/`) and Data Memory-Dependent Prefetcher (DMP) extensions beyond the inspected core analyser and Unicorn x86 speculators were not audited in detail.
  - Alternative SMT proof formats (`LFSC`, `CPC` / Eunoia in cvc5, Lean `lean-smt` reconstruction) and SAT proof formats (`FRAT`, `VeriPB` pseudo-Boolean proofs in `CaDiCaL`) were not examined in depth.
- **Unknown:**
  - Whether upstream `microsoft/sca-fuzzer` treats `SetAnalyser` (`rvzr/analyser.py` L214 `x >= threshold`) as dead/legacy code superseded by `MergedBitmapAnalyser` or an unreported defect; its presence on `main` without a deprecation warning remains a latent false-positive trap for users selecting `SetAnalyser`.
  - Whether `minotaur-toolkit/minotaur` L206–208 vs. L257–264 and L285–288 vs. L319–360 represent completed refactors with stale comments or partially reverted heuristics; empirical regression testing across Minotaur's full `tests/fp/` suite was not run.

## Evidence

### Primary Git Source Citations (Observed 2026-11-19)

- **`StanfordPL/stoke` @ `98d8a0f028f2daf2052bfe607dbc32ec8d55ba9e`:**
  - `src/search/search.cc` L41–125: `Search::run`, `beta_`, `max = state.current_cost - (log(p) / beta_)`, undo on `new_cost > max`.
  - `src/transform/all_transforms.h` L16–25: 9 syntactic transform headers (`add_nops`, `delete`, `global_swap`, `instruction`, `local_swap`, `opcode`, `opcode_width`, `operand`, `rotate`, plus `weighted`).
  - `src/cost/correctness.cc` L54–95: GPR, SSE, and EFLAGS (`cf, pf, af, zf, of, sf`) correctness evaluation and `max` short-circuiting.
  - `src/validator/bounded.cc` L36–64: `BoundedValidator::verify_pair`, `StateEqualityInvariant`, `MemoryEqualityInvariant`, counterexample extraction.
  - `src/validator/ddec.cc` L1–80: `DdecValidator`, cutpoint invariants (`ConjunctionInvariant`, `DisjunctionInvariant`, `EqualityInvariant`, `FlagInvariant`, `MemoryEqualityInvariant`, `SignInvariant`).
- **`google/souper` @ `963d4df436f3dc0b039cc0e47ada0577a26f5c4e`:**
  - `lib/Infer/AliveDriver.cpp` L615–730: `souper::Inst` opcode translation (`NSW`/`NUW`/`Exact`, saturating, overflow, funnel shifts, bit-counting), `translateDataflowFacts` (`Builder.assume`), and `translateDemandedBits` (`IR::BinOp::And` mask).
- **`minotaur-toolkit/minotaur` @ `f764ac4eb2c5b7644390c6a0c35087f4ff01427c`:**
  - `lib/alive-interface.cpp` L32–86 (`refines_relaxed_nan` conditional NaN payload relaxation), L115–121 (`AliveEngine::compareFunctions`), L139–152 (`pre_src.eq(pre_tgt)` structural precondition check), L163–202 (non-poison input constraint excluding `%_reservedc*`), L206–268 (quantifier-polarity handling of `getQuantVars`, `getNondetVars` excluding `maxminnondet*`, `getFnQuantVars`), L276–283 (commented-out memory refinement), L285–360 (greedy `synthesis_prefer_poison` post-SAT loop vs. stale L285 comment).
  - `lib/slice.cpp` L96–155: `Slice::extractExpr`, `isLoopSimplifyForm()` gate, loop-boundary cutoff (`loopi != loopv`).
  - `lib/cost.cpp` L27–115: `get_machine_cost` invoking `GET_COST_COMMAND` (`llvm-mca`) with 30s timeout and `get_approx_cost` fallback.
- **`AliveToolkit/alive2` @ `3bdd4f5e1cefa47057e93110e707acd11cfe08e4`:**
  - `tools/transform.cpp`, `ir/instr.cpp`, `ir/x86_intrinsics.cpp`, `smt/smt.cpp`: LLVM IR refinement semantics consumed by `Souper` and `Minotaur`.
- **`testsmt/yinyang` @ `5ce963290b682fccdb7f27464de0e5c0d02047c5`:**
  - `yinyang/src/mutators/SemanticFusion/SemanticFusion.py` L52–169: `SemanticFusion.fuse`, random partial occurrence substitution (`random.randint(0, len(occs))`), `unsat` -> `disjunction` + `add_fusion_constraints`, `sat` -> `conjunction` without `add_fusion_constraints`, `sort_clash` abort.
  - `yinyang/src/mutators/SemanticFusion/VariableFusion.py` L117–152: random template constant domains.
  - `yinyang/src/mutators/TypeAwareOpMutation.py` L29–123: bidirectional/unidirectional config parsing, `arities_mismatch` (`N`, `N+`, `N-`), `cvc5_compat` rollback via `cvc5_unsupported`.
- **`Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1`:**
  - `src/ast/proofs/proof_checker.cpp` L11–16, L103–140: internal `proof_checker::check`, dependency on `th_rewriter`, `side_conditions` output vector, `#if 0` around `check1_spc`.
- **`cvc5/cvc5` @ `7507ed17e261ba2dbc5f2d0b298c23dfff9c89cc`:**
  - `src/proof/alethe/alethe_proof_rule.h` L27–100: `enum class AletheRule`, context-carrying anchor subproofs (`ANCHOR_SUBPROOF`, `ANCHOR_BIND`, `ANCHOR_SKO_FORALL`, `ANCHOR_SKO_EX`, `ANCHOR_ONEPOINT`).
- **`ufmg-smite/carcara` @ `193b1b015d295518b270630bf57d2e66c2d25489`:**
  - `src/checker/mod.rs` L84–110: `Config` fields (`elaborated`, `ignore_unknown_rules`, `rup_resolution`, `allowed_rules`, `rule_checkers`).
  - `docs/src/checking.md` L14–49: `valid`/`invalid`/`holey` outcomes, `--allowed-rules` non-holey behavior, `lia_generic` non-checking, parallel checking architecture.
- **`arminbiere/cadical` @ `6b3d70b9ce00ecbce3f829bab76d185f0e92618c`:**
  - `src/lrattracer.cpp` L40–115: `put_binary_lit`, `put_binary_id`, `LratTracer::lrat_add_clause` binary/ASCII LRAT record formatting.
- **`tanyongkiam/cake_lpr` @ `033aad53d1733bd4b8ca41cf6f1b5fb5d84f8de2`:**
  - `README.md` L6–105: HOL4 `9783a49979c9` / CakeML `665f9b21712a` build provenance, binary LRAT/LPR support, two-level transformation checking, `--CML_HEAP_SIZE`/`--CML_STACK_SIZE` CLI flags (default 4096 MiB).
- **`cascade-artifacts-designs/cascade-meta` @ `3565fba7ea0c0dc08a6e428afd0a6513bede5c85` & `comsec-group/cascade-artifacts` @ `5f6b7c62b0210a116b61b09e4fff05cb46495040`:**
  - `fuzzer/cascade/basicblock.py` L31–160: `gen_basicblocks`, `gen_basicblock`, blacklisting (`L88–92`), `producer_id_to_tgtaddr` (`L97`), back-to-back `CONSUMED` consumer `nop`-bubble workaround (`L124–132`).
  - `fuzzer/cascade/finalblock.py` L20–101: fenced `sd`/`sw` and `fsd`/`fsw` register dumps, Machine-mode FPU activation (`mstatus`), `stopsig_addr` write.
  - `fuzzer/cascade/fuzzsim.py` L25–220: `MAX_CYCLES_PER_INSTR = 30`, `SETUP_CYCLES = 1000`, `runsim_verilator`, `runsim_modelsim`, `runtest_simulator` stop-request and `FREE`/`CONSUMED` register checking.
  - `comsec-group/cascade-artifacts`: `Readme.md`, `design_repos.json` (CVA6, Rocket, BOOM, PicoRV32, Kronos, VexRiscv targets).
- **`microsoft/sca-fuzzer` @ `cc9fa2e53d92c496586689f44d6ea1740d95bd1d`:**
  - `rvzr/analyser.py` L67–250: `EquivalenceAnalyserCommon.filter_violations`, `MergedBitmapAnalyser` (`counter[x] >= threshold`, L184–185), `SetAnalyser` (`x >= threshold` bug, L214–215), `MWUAnalyser` (L226–248).
  - `rvzr/model_unicorn/speculators_basic.py` L53–180: `X86CondSpeculator` conditional jump decoding (`0x70..0x7F`, `0xE0..0xE3`, `0x0F 0x80..0x8F`).
  - `rvzr/model_unicorn/speculators_fault.py` L31–120: `FaultSpeculator`, `SequentialAssistSpeculator`, `UnicornDEH` (errnos `{6, 10, 12, 13, 21}`).
  - `rvzr/model_unicorn/speculators_vs.py` L54–120: `_VspecBaseSpeculator` raising `NotImplementedError` (L105).
  - `docs/howto/choose-contract.md` L9–92: `CT-SEQ`, `CT-COND`, `CT-DEH`, `CT-NI`, and instruction-blocklisting workflow.

### Primary Peer-Reviewed Literature Citations

- Schkufza, Sharma, Aiken (ASPLOS 2013): *Stochastic Superoptimization*, DOI `10.1145/2451116.2451150`.
- Sharma, Schkufza, Churchill, Aiken (OOPSLA 2013): *Data-Driven Equivalence Checking*, DOI `10.1145/2509136.2509509`.
- Schkufza, Sharma, Aiken (PLDI 2014): *Stochastic Optimization of Floating-Point Programs with Tunable Precision*, DOI `10.1145/2594291.2594305`.
- Sasnauskas et al. (2017/2018): *Souper: A Synthesizing Superoptimizer*, `arXiv:1711.04422v2`.
- Lopes, Lee, Hur, Liu, Regehr (PLDI 2021): *Alive2: Bounded Translation Validation for LLVM*, DOI `10.1145/3453483.3454030`.
- Liu, Mada, Regehr (OOPSLA 2024): *Minotaur: A SIMD-Oriented Synthesizing Superoptimizer*, DOI `10.1145/3689766`, `arXiv:2306.00229v3`.
- Winterer, Zhang, Su (PLDI 2020): *Validating SMT Solvers via Semantic Fusion*, DOI `10.1145/3385412.3385985`.
- Winterer, Zhang, Su (OOPSLA 2020): *On the Unusual Effectiveness of Type-Aware Operator Mutations for Testing SMT Solvers*, DOI `10.1145/3428261`.
- Schurr, Fleury, Barbosa, Fontaine (PxTP 2021): *Alethe: Towards a Generic SMT Proof Format*, EPTCS 336, DOI `10.4204/EPTCS.336.6`, `arXiv:2107.02354`.
- Andreotti, Barrios, Barbosa (TACAS 2023): *Carcara: An Efficient Proof Checker and Elaborator for SMT Proofs in the Alethe Format*, DOI `10.1007/978-3-031-30823-9_19`.
- Cruz-Filipe, Heule, Hunt, Kaufmann, Schneider-Kamp (CADE 2017): *Efficient Certified RAT Verification*, DOI `10.1007/978-3-319-63046-5_14`.
- Tan, Heule, Myreen (TACAS 2021): *cake_lpr: Verified Propagation Redundancy Checking in CakeML*, DOI `10.1007/978-3-030-72013-1_12`.
- Solt, Ceesay-Seitz, Razavi (USENIX Security 2024): *Cascade: CPU Fuzzing via Intricate Program Generation*.
- Guarnieri, Köpf, Reineke, Vila (IEEE S&P 2021): *Hardware-Software Contracts for Secure Speculation*, DOI `10.1109/SP40000.2021.00030`.
- Oleksenko, Fetzer, Köpf, Silberstein (ASPLOS 2022): *Revizor: Testing Black-Box CPUs against Speculation Contracts*, DOI `10.1145/3503222.3507729`.

### Reproducible Execution Probes (Observed 2026-11-19, Python 3.13.15)

- **Probe 1A (Exhaustive 4-bit `nsw` poison refinement & quantifier polarity):** Exhaustive enumeration over `i4` verified `add_nsw(x,x) <-> shl_nsw(x,1)` (0 counterexamples), `add_wrap(x,x) -> add_nsw(x,x)` failing on 8/16 inputs (`first=[(4, 4, (8, True), (8, False)), ...]`), and quantifier-polarity failure on `src(x,u) = (u==0 ? 0 : (x+1)&15)` where `exists c, u. forall x` yields bogus model `[(0, 0)]` while `exists c. forall x, u` correctly yields `[]` (UNSAT).
- **Probe 1B (Exhaustive `BV4` YinYang Semantic Fusion invariants):** Exhaustive enumeration over $16^3$ triples verified XOR fusion on UNSAT pair produces `SAT=False` with `z == x ^ y` and `SAT=True` without it; SAT pair without `fusion_constr` preserves SAT (`SAT_count=16` full, `SAT_count=1` partial `(4,9,13)`); non-surjective inverse `((z - y) & 15) >> 1` yields `SAT_count=0`, dropping witness `x=12`.
- **Probe 1C (Revizor `SetAnalyser` vs. `MergedBitmapAnalyser` outlier filter):** On `raw1 = [1<<10]*100`, `raw2 = [1<<10]*99 + [(1<<10)|(1<<20)]`, `threshold = 10.0`, `subsets_is_violation = True`: `MergedBitmapAnalyser` returned `equiv=True`, while upstream `SetAnalyser` (`x >= threshold`) returned `equiv=False` (false-positive contract violation).

## Revalidation

To cheaply revalidate whether the specific findings and caveats in this report still hold on newer upstream revisions:

1. **Minotaur memory refinement and quantifier polarity:** Diff `minotaur-toolkit/minotaur` `lib/alive-interface.cpp` against `f764ac4eb2c5` around `find_model` (L139–360): verify whether `src_mem.refined(tgt_mem, false)` remains commented out, whether `maxminnondet*` remains excluded from `qvars`, and whether `synthesis_prefer_poison` remains active.
2. **Revizor `SetAnalyser` bug and VSOps status:** Inspect `microsoft/sca-fuzzer` `rvzr/analyser.py` around `SetAnalyser.htraces_are_equivalent` (check whether `if x >= threshold` has been fixed to `Counter(raw)` frequency filtering `if counter[x] >= threshold`) and check `rvzr/model_unicorn/speculators_vs.py` for the `NotImplementedError` guard in `_VspecBaseSpeculator.__init__`.
3. **Carcara proof-checking trust boundary:** Inspect `ufmg-smite/carcara` `docs/src/checking.md` and `src/checker/mod.rs` to check whether `lia_generic` has gained native checking (e.g., Farkas/cutting-plane verification) and whether `--allowed-rules` still reports `valid` instead of `holey`.
4. **CaDiCaL LRAT and `cake_lpr` successor:** Check `tanyongkiam/cake_lpr` `README.md` (which notes the 1 Nov 2026 release as its final planned update prior to a successor checker) and verify `arminbiere/cadical` `src/lrattracer.cpp` wire encoding compatibility.
5. **Cascade simulation oracle parameters:** Diff `cascade-artifacts-designs/cascade-meta` `fuzzer/cascade/fuzzsim.py` and `basicblock.py` for changes to `MAX_CYCLES_PER_INSTR`, `SETUP_CYCLES`, or the back-to-back `CONSUMED` consumer `nop`-bubble workaround.
