# Historical Failures in External Decision Procedures, Proof-Producing Solvers, and Certificate Checkers: Postmortems and Architectural Lessons for Anneal

## Summary

Historical postmortems across SAT, QBF, and pseudo-Boolean (PB) solvers, SMT
solvers, equality saturation engines, computer algebra systems (CAS),
floating-point error analyzers, and Constrained Horn Clause (CHC) model
checkers establish five structural invariants that directly govern how Anneal
integrates external decision procedures with its four `trusted/` primitives:

1. **Unverified decision procedures and unverified C/Python certificate checkers
   both exhibit recurring soundness bugs.** Differential and mutational fuzzing
   campaigns (`YinYang`, `OpFuzz`, `Storm`, `Murxla`, `HistFuzz`, `QBFfuzz`, and
   `PyCHC`) uncovered more than 2,000 bugs—including hundreds of critical
   soundness bugs where a solver returns `unsat` on a satisfiable formula or
   emits an invalid `sat` model—in mature production solvers (`Z3`,
   `CVC4`/`cvc5`, `Bitwuzla`, `Yices2`, `MathSAT5`, `DepQBF`, `CAQE`, `Spacer`,
   `Eldarica`, and `Golem`). Furthermore, unverified C and Python proof checkers
   (`drat-trim` and early `VeriPB`) suffered from parser integer overflows,
   missing empty-clause validation, and cyclic dominance orders that accepted
   spoofed or invalid proofs of unsatisfiable and satisfiable formulas alike.
2. **Proof reconstruction that relies on `trust` holes, shallow AST
   re-encoding, or syntax-level tactic term expansion fails either open or
   non-performantly.** In `cvc5`/`veriT` `Alethe` and `LFSC` proof logs,
   unelaborated rewrite or preprocessing rules emit `trust` / `THEORY_REWRITE`
   holes that force downstream ITP checkers (`SMTCoq`, Isabelle `smt`,
   `lean-smt`) either to reject the proof or to fall back to trusted axioms.
   Separately, bit-blasting bridges that re-encode division-by-zero, shift
   overshoot, or signedness semantics differently between the solver AST and the
   ITP AST create translation mismatches even when the underlying `LRAT` proof
   is propositionally valid.
3. **Equality saturation and algebraic/numerical engines fail when context,
   domain restrictions, or exact arithmetic are conflated with untrusted search
   state.** In `egg`, checking conditional rewrite side conditions on e-class
   canonical representatives or mutable e-class analysis lattices rather than on
   the concrete rewritten term is unsound whenever an e-class merges terms with
   divergent domain properties; prior to Flatt et al. (FMCAD 2022), congruences
   over cyclic e-graphs also produced cyclic or exponentially blown-up
   explanations. In CAS and Sum-of-Squares (`SOS`) tools (`Mathematica`,
   `Maple`, `Singular`, `CSDP`, `MOSEK`), generic algebraic division cancels
   singularities (`(x^2 - 1)/(x - 1) -> x + 1`), Chinese Remainder Theorem (CRT)
   homomorphic imaging suffers from bad primes and overflow (`Mathematica` 9.0.1
   determinant bug), and floating-point Semidefinite Programming (`SDP`) solvers
   return numerical Gram matrices with slightly negative eigenvalues
   ($\lambda_{\min} \approx -10^{-9}$) that fail exact rational
   Positivstellensatz checks unless projected onto the affine subspace and
   verified via exact $L D L^T$ decomposition.
4. **Floating-point and CHC verifiers fail on boundary regimes when idealized
   real or integer abstractions omit subnormal gradual underflow, `NaN`
   propagation, or inter-procedural array aliasing.** First-order Taylor error
   models (`FPTaylor`, `Gappa`) become unsound near the subnormal threshold
   ($2^{-126}$ for `f32`, $2^{-1022}$ for `f64`) unless separate absolute-error
   terms (`eta`) and non-`NaN`/finite guards are enforced; CHC solvers
   (`Spacer`, `Eldarica`, `Golem`) have produced wrong `sat` (safe) and `unsat`
   (unsafe) verdicts in `CHC-COMP` when array read-over-write axioms interact
   with nonlinear arithmetic or algebraic datatypes.
5. **Reflective certificate checking inside an interactive theorem prover
   encounters a sharp kernel-reduction wall unless certificates and data
   structures are engineered specifically for the kernel WHNF reducer.** Because
   Anneal's `trusted/audit/TrustedBoundary.lean` forbids `native_decide` and
   `decide +native` (`Lean.ofReduceBool`) to exclude the C++/LLVM compiler and
   FFI from the Trusted Computing Base (TCB), every certificate check in
   `theory/` must reduce in Lean 4's interpreted kernel WHNF reducer during both
   elaboration and `base.toKernelEnv.replay`. Naive `Array.set` mutations ($O(N)$
   copying per update in the kernel reducer), structural term equality, in-kernel
   sorting, or monolithic `defnInfo` certificate declarations cause quadratic
   CPU or multi-gigabyte memory blowups on large proofs.

## Applicability

This report applies to the design and implementation of external solver
integrations, proof-format adapters, and kernel-verified certificate checkers in
Anneal (`joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`) pinned to Lean
`v4.34.1` (`trusted/lean/lean-toolchain`).

The subjects examined in `REPORT.json` play two distinct roles:

- **Target architecture and enforcement boundary:** Anneal's trust boundary in
  `trusted/audit/TrustedBoundary.lean`, `trusted/lean/Trusted.lean`,
  `trusted/lean/Trusted/Attributes.lean`, and `trusted/lean/foundation-lock.json`
  at commit `24367bd1a8c784f2578535954f9915e24894a56f`, together with the four
  core `trusted/` semantic and verification primitives:
  1. `Language SemObs`, `BehaviorCodec`, `Abstracts`, and `Compiles` (semantic
     abstraction, refinement, and compilation bridges);
  2. `SmallStepMachine`, `StepResult.externalCall`, and `EventualBehaviorOf`
     (operational small-step semantics with demonic external boundaries and
     terminating/diverging trace observations);
  3. `VerificationResult`, `SpecOn`, `ProductiveOn`, and `InhabitedPre` (crate
     obligation envelopes, safety specifications, termination/liveness
     productivity, and non-vacuity guards); and
  4. `TrustedBoundary.lean` and `foundation-lock.json` (two-phase `"preflight"`
     and `"audit"` inspection, prohibition of `native_decide`/`partial`/`unsafe`
     and custom axioms, and clean-environment kernel replay via
     `base.toKernelEnv.replay`).
- **Historical failure corpus:** Primary peer-reviewed postmortems, competition
  disqualification records, and fuzzing studies across SAT/QBF/PB checkers
  (`cake_lpr`, `drat-trim`, `VeriPB`/`CakePB`, `QBFfuzz`), SMT solvers and proof
  reconstructors (`YinYang`, `Storm`, `Murxla`, `HistFuzz`, `Alethe`, `SMTCoq`,
  `lean-smt`), equality saturation engines (`egg`, `slotted-egraphs`), CAS and
  SDP/SOS certifiers (`Mathematica`, `Singular`, Peyrl & Parrilo, Monniaux &
  Corbineau), floating-point analyzers (`FPTaylor`, `Gappa`), and CHC model
  checkers (`Spacer`, `Eldarica`, `Golem`, `PyCHC`).

Findings regarding upstream solver bugs apply to the historical versions and
configurations documented in the cited studies. Architectural lessons derived
from those failures apply directly to all certificate checkers authored in
Anneal's untrusted `theory/` layer and to proof scripts emitted into
`.anneal/Proof.lean`.

## Findings

### 1. SAT, QBF, and Pseudo-Boolean Solver and Certificate Checker Failures

#### 1.1 `drat-trim` Parser Integer Overflows, Buffer Overruns, and Missing Empty-Clause Checks

Basis: documentation + source + derived (Tan, Heule, and Myreen, TACAS 2021, DOI
`10.1007/978-3-030-72013-1_18`; Lammich, CADE 2017 / JAR `gratchk`).

Before the deployment of mechanically verified SAT proof checkers (`gratchk` in
Isabelle/HOL and `cake_lpr` in CakeML/HOL4), the SAT Competition relied on the
unverified C checker `drat-trim` to validate `DRAT` and `LRAT` unsatisfiability
proofs. During the verification of `cake_lpr` and `gratchk`, researchers
discovered multiple soundness vulnerabilities in `drat-trim` and unverified
competition checkers:

- **32-bit signed integer overflow in DIMACS / proof literal parsing:**
  `drat-trim`'s custom integer parser accumulated decimal digits into a signed
  32-bit `int` (`lit = 10 * lit + c - '0'`) without overflow bounds checking. A
  malformed or adversarial proof containing a literal index such as
  `4294967297` ($2^{32} + 1$) wrapped modulo $2^{32}$ to literal `1` in C
  undefined-behavior two's-complement arithmetic, allowing a proof step to
  reference or delete clauses over variable `1` while appearing to operate on a
  fresh extension variable.
- **Missing terminal empty-clause verification and premature EOF acceptance:**
  Early versions of `drat-trim` and unverified `LRAT` checkers could return exit
  code `0` (`VERIFIED`) or misclassify a truncated proof file when a parser
  buffer or deletion line terminated before deriving the empty clause `0`, or
  when `0` appeared inside a malformed deletion directive.
- **Redundancy ratio and unit-propagation array out-of-bounds:** When a proof
  introduced variables exceeding the header's declared `p cnf <vars> <clauses>`
  bound without reallocating the watch-list and assignment arrays, `drat-trim`
  performed out-of-bounds memory reads/writes that could corrupt the active
  clause database.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
Anneal must never shell out to an external C binary (`drat-trim`, `lrat-check`)
and trust its exit code (`0`) via FFI or `IO`, which `TrustedBoundary.lean`
(`inspectSyntax`, lines 312–329) already forbids. Instead, `drat-trim` or
`CaDiCaL` runs strictly outside the TCB during `.anneal/Proof.lean` generation
to elaborate a `DRAT` trace into explicit `LRAT` hint indices; the `LRAT`
certificate is embedded as pure Lean data in `.anneal/Proof.lean` and checked by
a total, bounds-checked Lean function `checkLRAT : CNF → Array LRATStep → Bool`
in `theory/` whose soundness theorem requires an explicit boolean postcondition
confirming that the final step derived the empty clause `[]`.

#### 1.2 `VeriPB` Cyclic Dominance, Pre-Order Deletion, and Self-Logging Soundness Bugs

Basis: documentation + derived (Bogaerts, Gocht, McCreesh, and Nordström, JAIR
2023, DOI `10.1613/jair.1.14714`, `arXiv:2211.09398`; Gocht et al., `CakePB`
OOPSLA 2023).

`VeriPB` extends clausal `DRAT`/`PR` proof checking to 0–1 pseudo-Boolean
cutting planes with **dominance-based strengthening** and symmetry breaking.
During the formalization of the dominance rule in HOL4/CakeML (`CakePB`) and
stress-testing of the Python/C++ `VeriPB` checker, three subtle soundness traps
emerged:

- **Cyclic dominance via unconstrained constraint deletion:** Suppose a proof
  uses a preorder $\preceq$ to show that assignment $\alpha$ is dominated by
  $\omega(\alpha)$, adding a symmetry-breaking constraint $C_1$ that eliminates
  $\alpha$. If the proof subsequently *deletes* an original problem constraint
  $D$ that was required to prove that $\omega(\alpha)$ satisfies the formula, or
  changes the active dominance order without checking that previously derived
  dominance constraints remain valid under the new order, the solver can
  cyclically eliminate *all* satisfying assignments ($\alpha$ eliminated in
  favor of $\beta$, and $\beta$ later eliminated in favor of $\alpha$) and
  derive `0 >= 1` (`UNSAT`) on a satisfiable formula.
- **Unchecked deletion erasing the last satisfying assignment:** Even under a
  trivial order, arbitrary deletion of constraints in a strengthening proof
  system can transform a satisfiable formula into an unsatisfiable one unless
  **checked deletion** verifies that any assignment satisfying the remaining
  database can be mapped back to a satisfying assignment of the deleted
  constraint (Remark 16 of Bogaerts et al., `arXiv:2211.09398`).
- **64-bit coefficient overflow in cutting-plane linear combinations:** When
  multiplying pseudo-Boolean inequalities $\sum a_i \ell_i \ge A$ by weights
  $w_k$ and adding them, fixed-width `int64_t` accumulators in unverified
  cutting-plane checkers overflowed on cardinality/knapsack instances, turning a
  negative slack into a positive contradiction.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
1. In `theory/`, any cutting-plane (`LIACert` / `PBCert`) or redundancy checker
   must use arbitrary-precision `Nat` / `Int` from `Init.Data.Int.Basic`
   (`trusted/lean/foundation-lock.json`) rather than `UInt64`/`Int64`,
   completely eliminating coefficient overflow.
2. Certificate formats in `theory/` should restrict deletion steps to **pure
   performance hints** (detaching a clause from the active lookup table while
   monotonically preserving the soundness invariant that all remaining active
   clauses are logical consequences of the initial formula $\Phi_0$), and reject
   non-equivalence-preserving dominance/RAT steps whenever Anneal requires model
   preservation or bidirectional `Compiles` equivalence.

#### 1.3 `QBFfuzz` Soundness Disqualifications in `DepQBF`, `CAQE`, and `QRATtrim`

Basis: documentation + execution (Brummayer, Lonsing, and Biere, SAT 2010, DOI
`10.1007/978-3-642-14186-7_6`; QBF Gallery / QBFEval reports).

In SAT 2010 and subsequent QBFEval competitions, Brummayer, Lonsing, and Biere
used `QBFfuzz` and delta-debugging (`ddmin`) to test QBF solvers and
preprocessors (`Bloqqer`, `DepQBF`, `CAQE`, `QuBE`, `sKizzo`). Over 60% of
tested QBF solvers exhibited soundness bugs (returning `TRUE` on false QBFs or
`FALSE` on true QBFs):

- **Unsound universal reduction across dependency schemes:** In `DepQBF` and
  early QBF preprocessors, **universal reduction** drops a universal literal
  $\forall u$ from clause $C$ if $u$ does not depend on any existential variable
  $\exists e \in C$ that appears to the right of $u$ in the quantifier prefix.
  Bugs in standard and resolution-path dependency-scheme caches caused solvers
  to drop a universal literal $u$ even when an existential literal $e \in C$
  transitively depended on $u$ through a learned clause, strengthening $C$
  unsoundly and producing false `UNSAT` verdicts.
- **Existential vs. universal polarity confusion in `QRAT` checking:** A `QRAT`
  step on an existential literal requires checking outer resolution tautologies
  restricted to universal variables precedes, whereas a `QRAT` step on a
  universal literal (`QRATU`) has dual side conditions. Early `QRAT` scripts
  mishandled free variables (variables not bound in the prefix) by defaulting
  them to universal rather than existential quantification.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
When Anneal uses 2-QBF or $\forall \exists$ solving to bridge **demonic
external nondeterminism** (`StepResult.externalCall boundaryInv branches` in
`SmallStepMachine`) with **angelic witness existence** (`ProductiveOn` and
`Abstracts` simulation witnesses), `theory/` should avoid verifying general
multi-alternation `QRAT` dependency-scheme traces inside the kernel. Instead,
for $\forall \vec{x}\; \exists \vec{y},\; \Phi(\vec{x}, \vec{y})$, the untrusted
QBF oracle (`CAQE` / `Pedant`) should emit an explicit **Skolem AIG circuit**
$\vec{y} := \vec{S}(\vec{x})$ plus a standard propositional `LRAT` refutation of
$\neg \Phi(\vec{x}, \vec{S}(\vec{x}))$. Checking a Skolem circuit Substitution
followed by propositional `LRAT` requires zero quantifier-prefix dependency
tracking in the kernel and constructively provides the witness function needed by
`ProductiveOn`!

#### 1.4 Bit-Blasting Encoding Mismatches Between Solver AST and ITP AST

Basis: source + derived (`SMTCoq` Coq bitvector lowering issues; `lean-smt` /
`Std.Tactic.BVDecide` division/shift corner cases; SMT-LIB v2.6 `FixedSizeBitVectors`
standard vs. Rust MIR semantics).

Even when a SAT solver and its `LRAT` checker are 100% sound, bit-blasting
pipelines fail unsoundly or fail to reconstruct proofs when the external solver's
bit-blaster and the ITP's `BitVec` semantics disagree on boundary operations:

- **Division and remainder by zero (`bvudiv`, `bvsdiv`, `bvsrem`, `bvsmod`):**
  In SMT-LIB `QF_BV`, `bvudiv x 0` is defined as the all-ones bitvector
  `0xfff...f` (`-1`), and `bvsdiv x 0` is `+1` if `x < 0` and `-1` if `x >= 0`.
  By contrast, in Rust `Runtime(PostCleanup)` MIR, integer division or remainder
  by zero (`BinOp::Div`, `BinOp::Rem`) or signed `MIN / -1` is **immediate
  Undefined Behavior or a checked panic**, and in early versions of Lean/Coq
  bitvector libraries `x / 0` evaluated to `0`! If the bit-blaster translates
  MIR `a / b` into SMT-LIB `bvudiv a b` without conjoining the side condition
  `b != 0` into the verification obligation, the solver proves properties such
  as `(a / b) * b + (a % b) == a` even when `b == 0` (which holds in SMT-LIB
  because `(-1) * 0 + a == a`, masking a division-by-zero UB bug in Rust!).
- **Oversized bit shifts (`bvshl`, `bvlshr`, `bvashr`):** In SMT-LIB `QF_BV`,
  shifting a width-$w$ bitvector by $k \ge w$ produces `0` (or the sign bit for
  `bvashr`), whereas in Rust MIR, unchecked `BinOp::ShlUnchecked` /
  `BinOp::ShrUnchecked` with shift amount $\ge w$ is Undefined Behavior and
  standard `BinOp::Shl` masks the shift amount by `w - 1` (`k & (w - 1)`) after
  a debug assertion check.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
In Anneal's `Abstracts L_{\text{BV}} L_{\text{MIR}} codec c_{\text{bv}}
p_{\text{mir}}`, the semantic abstraction proof is checked inside the Lean
kernel against `trusted/lean/`'s exact MIR operational semantics
(`SmallStepMachine`). If `L_{\text{MIR}}` transitions to `.failed .ub` whenever
`divisor == 0` or `shift >= width`, then any `BehaviorCodec` that maps
`.failed .ub` to `none` (`decodeOut (.terminated _ (.failed .ub)) = none`)
*cannot* prove `Abstracts` unless the bitvector circuit guard explicitly proves
`divisor != 0` and `shift < width`! Furthermore, the Tseitin bit-blaster
(`checkTseitin : BVExpr 1 → AIG → CNF → Bool`) must be proved sound directly
against `Init.Data.BitVec` in `foundation-lock.json`, rather than trusting an
external solver's bit-blasting pass to generate the CNF.

---

### 2. SMT Solver Soundness Bugs and Proof-Reconstruction Failures

#### 2.1 Semantic Fusion (`YinYang`), Type-Aware Mutation (`OpFuzz`), Blackbox Fuzzing (`Storm`), API Fuzzing (`Murxla`), and Historical Skeletons (`HistFuzz`)

Basis: documentation + execution (Winterer, Zhang, and Su, PLDI 2020 DOI
`10.1145/3385412.3385985` & OOPSLA 2020; Mansur et al., ESEC/FSE 2020 DOI
`10.1145/3368089.3409763`; Niemetz, Preiner, and Biere, CAV 2022 DOI
`10.1007/978-3-031-13188-2_21`; Sun, Zhang, and Su, ICSE 2023 DOI
`10.1109/ICSE48619.2023.00161`).

Between 2020 and 2025, five major automated fuzzing campaigns systematically
exposed hundreds of soundness bugs across `Z3`, `CVC4`/`cvc5`, `Bitwuzla`,
`Yices2`, `MathSAT5`, and `dReal`:

| Fuzzing Campaign | Core Technique | Solvers Tested | Total Confirmed Bugs | Confirmed Soundness Bugs (`unsat` on SAT / wrong `sat` model) | Primary Subsystem Root Causes |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`YinYang` + `OpFuzz`** (PLDI / OOPSLA 2020) | Semantic fusion of known-SAT/UNSAT formula pairs + type-aware operator mutation | `Z3` (4.8.x), `CVC4` (1.7–1.8) | $> 1,100$ | $> 320$ soundness bugs | `QF_NRA`/`QF_NIA` incremental linearization, `QF_SLIA` string regex/replace rewriters, `Int`/`Real` mixed casts |
| **`Storm`** (ESEC/FSE 2020) | Blackbox cube-decomposition mutational fuzzing on satisfiable seed models | `Z3`, `CVC4`, `Yices2`, `MathSAT5` | $309$ | $29$ critical soundness bugs across `Z3`, `CVC4`, `Yices2`, `MathSAT5` | Theory combination (Nelson-Oppen equality propagation), `QF_FP` subnormal rounding, incremental `push`/`pop` state leakage |
| **`Murxla`** (CAV 2022) | Stateful model-based SMT-LIB API call sequence fuzzer | `Bitwuzla`, `cvc5`, `Yices2`, `Z3` | $240+$ | $40+$ wrong answers / model validation failures | Incremental `check-sat-assuming` assumption activation, array `store`/`select` lemma caching across `pop`, `QF_BV` algebraic rewrites |
| **`HistFuzz`** (ICSE 2023) | Synthesis from bug-triggering formula skeletons of historical issue trackers | `Z3` (4.8–4.11), `cvc5` (1.0.x) | $311$ | $76$ soundness bugs | Quantifier instantiation (`MBQI` / `E-matching`), `QF_DT` acyclicity checks, `QF_ABV` bitvector-array Ackermannization |

Concrete representative root causes from these postmortems include:

1. **Incremental `push`/`pop` and `check-sat-assuming` lemma leakage (`Z3`,
   `CVC4`/`cvc5`, `Yices2`, `Bitwuzla`):** Both `Storm` and `Murxla` found
   repeated soundness bugs where a theory solver (such as `QF_BV`, `QF_AX`, or
   `QF_LIA`) learned a conflict clause or cached a simplified term under a
   temporary scope (`push 1` or `check-sat-assuming (a)`), and failed to
   invalidate that cache entry after `pop 1`. On a subsequent query in the same
   solver process, the stale rewrite simplified a satisfiable formula to `false`
   (`unsat`).
2. **Aggressive theory-rewriter rules missing side conditions (`OpFuzz` /
   `HistFuzz`):** In `Z3` and `CVC4`, over-eager algebraic and string rewrite
   rules—such as simplifying `str.indexof(s, t, n)` when `n < 0`, rewriting
   nonlinear integer division `(a * b) div b -> a` when `b` could be `0`, or
   collapsing bitvector sign-extensions across wrapping additions—produced
   unsound `unsat` verdicts before the main CDCL(T) search even started.
3. **Quantifier `MBQI` / `E-matching` false `sat` and false `unsat` (`Z3` /
   `cvc5`):** In formulas combining universal quantifiers with arrays or
   nonlinear arithmetic, `Z3`'s `MBQI` occasionally constructed a candidate
   model interpretation using a default `else` branch for an uninterpreted
   function that violated a quantified axiom on out-of-domain indices, or
   unsoundly skolemized a nested quantifier under an unsimplified `ite` guard.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
This empirical record is the definitive justification for Anneal's core rule in
`PRINCIPLES.md`: **no external SMT solver verdict (`unsat` or `sat`) may ever
be trusted as an axiom or oracle in `trusted/` or `theory/`**. In particular:
- Even running two independent solvers (`Z3` + `cvc5`) in lockstep does not
  eliminate soundness bugs, because shared SMT-LIB preprocessing heuristics and
  incremental state management bugs have historically afflicted multiple solvers
  simultaneously (`Storm` found soundness bugs in `Z3`, `CVC4`, `Yices2`, and
  `MathSAT5`).
- In Anneal's `VerificationResult policy waived obligations`, an SMT solver is
   strictly an untrusted **certificate discovery tool**. If an SMT solver hits an
  incremental cache bug and claims a branch is `unsat`, it will either fail to
  emit a closed `Alethe`/`LRAT`/`LIACert` certificate or emit a step whose
  premises do not resolve to $\bot$, which Anneal's pure Lean checker in
  `theory/` rejects during `rfl` reduction.

#### 2.2 `Alethe`, `LFSC`, `SMTCoq`, and `lean-smt` Proof-Reconstruction Failures and `trust` Holes

Basis: documentation + source + derived (Barbosa et al., `cvc5` Alethe/CPC
proof architecture; Ekici et al., `SMTCoq` CAV 2017; Mohamed et al., `lean-smt`
CAV 2025 `arXiv:2505.15796`; Schurr et al., CADE 2021 `Alethe`).

When transitioning from unverified SMT solving to proof-producing SMT solving,
three distinct failure modes have historically broken ITP proof reconstruction:

- **Coarse-grained `trust` / `THEORY_REWRITE` steps in `cvc5` and `veriT`:**
  `cvc5` contains hundreds of C++ theory rewrite rules across strings,
  bitvectors, and arithmetic. When `cvc5` applies a preprocessing pass (such as
  non-clausal variable elimination, symmetry breaking, or an unelaborated
  `THEORY_REWRITE`) for which fine-grained proof logging is not yet implemented,
  it emits an `Alethe` `(step t_k (cl ...) :rule trust)` or `:rule hole` node.
  In Isabelle's `smt` tactic and early `lean-smt` prototypes, encountering an
  unreconstructed `trust` step either aborts the tactic or inserts an unsound
  `sorry` / trusted oracle axiom.
- **Skolemization and binder-renaming mismatches during `subproof` anchor
  reconstruction:** `Alethe` uses contextual `anchor` subproofs for congruence
  under binders ($\forall x.\; t(x) = u(x)$) and `sko_ex` / `sko_forall` rules
  that introduce fresh Hilbert choice ($\varepsilon$) terms. In `SMTCoq` and
  Isabelle `Alethe` reconstruction, subtle discrepancies between the solver's
  variable-shadowing convention inside nested `let` / `forall` binders and the
  ITP's de Bruijn index shifting caused reconstructed proof terms to fail kernel
  typechecking with ill-typed free variables.
- **Elaboration-time tactic blowup vs. reflective checking:** Translating a
  50,000-step `Alethe` or `CPC` proof into native Lean 4 tactic proof terms
  (`Eq.trans`, `congrArg`, `Classical.byContradiction`) generates a kernel
  `Expr` DAG containing millions of `.app` nodes and universe level annotations.
  In Anneal's `TrustedBoundary.lean` (lines 480–520 and 972), `exprEdges`
  traverses every `Expr` node in `locals` and `base.toKernelEnv.replay locals`
  re-typechecks every `.app` node, causing multi-second or out-of-memory stalls
  on expanded tactic proofs.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
1. **`TrustedBoundary.lean` Automatically Blocks `trust` Holes:** Because
   `TrustedBoundary.lean` checks that the axiom closure (`closure`) of
   `Proof.verify_crate` is a subset of `{Classical.choice, Quot.sound, propext}`
   and forbids `axiom`/`opaque`/`sorryAx`, no `Alethe` `trust` step can ever
   silently slip through as an axiom in `.anneal/Proof.lean`.
2. **Configure Solvers for Proof-Safe Preprocessing Only:** When `cargo-anneal`
   invokes `cvc5` to generate certificates, it must pass flags that disable
   unlogged preprocessing passes (`--proof-granularity=dsl-rewrite` or
   `--proof-alethe-define-skolems`) and route `QF_BV` sub-obligations through
   verified `LRAT` bit-blasting (`bv_bitblast`) and `QF_LIA` sub-obligations
   through explicit `Farkas`/`cut` certificates (`LIACert`), rather than relying
   on unelaborated `THEORY_REWRITE` steps.
3. **Prefer Deeply Embedded Reflective `TermArena` Checkers over Tactic Proof
   Expansion:** Storing an `Alethe` certificate as a flat `ByteArray` or packed
   `Array UInt32` inside `Proof.lean` and checking it via a deeply embedded
   hash-consed `checkAlethe` function in `theory/` keeps the number of kernel
   `Expr` nodes in `TrustedBoundary.exprEdges` $O(1)$!

---

### 3. E-Graph and Equality Saturation Failures

#### 3.1 Conditional Rewrite Unsoundness via E-Class Representative and Analysis Lattice Conflation in `egg`

Basis: documentation + source + derived (Willsey et al., `egg` POPL 2021;
`egraphs-good/egg` e-class analysis invariants and conditional rewrite
semantics).

In equality saturation (`egg`), a conditional rewrite rule $l(\vec{x}) \to
r(\vec{x}) \text{ if } \phi(\vec{x})$ matches a pattern $l(\vec{x})$ against an
e-graph substitution $\sigma : \text{Var} \to \text{EClassId}$, yielding an
e-class ID $\sigma(x_i)$ for each pattern variable rather than a single concrete
term. Two classic soundness bugs arise when side conditions $\phi(\sigma(x_i))$
are evaluated on the e-class:

- **Representative-dependent or non-invariant e-class properties:** Suppose an
  e-class analysis tracks a syntactic or partial domain property (e.g., whether
  an expression is a constant non-zero divisor, or whether a pointer offset stays
  within bounds under a local cast). If e-class $c$ merges a well-defined term
  $t_1$ with an expression $t_2$ that is only equal to $t_1$ under a path guard
  (or if the analysis lattice `merge(d1, d2)` takes a union/join that is true if
  *any* member of the e-class satisfies $\phi$ rather than *all* members), then
  applying $x / x \to 1$ when $c$ contains both `0` (via a dead or guarded merge)
  and a non-zero constant derives `0 / 0 = 1`.
- **Context-insensitive global merging of path-sensitive equalities:** Standard
  e-graphs represent a single global equivalence relation. If a user asserts a
  branch condition `x == 0` into the e-graph to simplify the `then` branch of an
  `if` expression without scoping that equality to a contextual sub-e-graph
  (`colored e-graphs` / `egglog` rule contexts), the merge `eclass(x) =
  eclass(0)` leaks globally into the `else` branch and rewrites `1 / x` to
  `1 / 0`.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
In Anneal, `egg` or `egglog` is never trusted as a decision procedure; instead,
it emits a **concrete term/DAG rewrite certificate (`EqSatCert` /
`EgglogProvenanceCert`)** checked in `theory/`. Crucially:
1. Every conditional rewrite step in `EqSatCert` (`ruleId`, `position`, `subst :
   Array TermId`) substitutes **concrete hash-consed subterms `TermId`** (never
   opaque e-class IDs!) and requires a concrete proof witness (`premiseFactId` or
   boolean evaluation `checkCond r subst env = true`) that the side condition
   holds on that exact ground term in the current basic-block path context.
2. In `Abstracts L_{\text{Expr}} L_{\text{MIR}} codec t_{\text{spec}}
   fast_mir`, because `Language SemObs` models partiality via `Partial (Out →
   Prop)` (`defined : Prop`), a rewrite rule $l(\vec{x}) \to r(\vec{x})$ in
   `theory/` is sound for `Compiles` / `Abstracts` only if its kernel-checked
   lemma proves that `defined (sem l)` implies `defined (sem r)` (so a rewrite
   can never erase a division-by-zero or out-of-bounds UB obligation without a
   verified side-condition certificate).

#### 3.2 Binder Capture, De Bruijn Shifting Shattering, and Slot Permutation Bugs in Slotted E-Graphs

Basis: documentation + derived (Schneider, Kœhler, and Steuwer, *Slotted
E-Graphs*, PLDI 2024, DOI `10.1145/3656430`).

When applying equality saturation to higher-order or loop-body IRs containing
binders ($\lambda x.\; e$, `Iterator::map`, `fold`, or loop comprehension
indices), traditional e-graphs suffer from two failure modes documented by
Schneider, Kœhler, and Steuwer (PLDI 2024):

- **De Bruijn index shattering across beta-reduction and congruence:** Under
  de Bruijn indexing, a free variable's index shifts whenever it crosses a
  binder ($\lambda.\; x_0$ vs. $\lambda.\; \lambda.\; x_1$). Consequently, a
  single subexpression $e$ containing free variables belongs to *different*
  e-classes depending on how many binders enclose it, destroying e-graph sharing
  and causing beta-reduction $(\lambda x.\; f(x))\; y \to f(y)$ or
  capture-avoiding substitution to trigger exponential e-node duplication or
  unsound variable capture if shift adjustments are miscomputed during e-class
  unification.
- **Self-symmetric e-classes and non-trivial slot group permutations:**
  `Slotted E-Graphs` replace de Bruijn indices with named **slots** per e-class
  and attach a slot bijection $\theta$ to every e-node edge. However, an e-class
  can have **self-symmetries** (for example, $s_1 + s_2 = s_2 + s_1$ makes the
  e-class invariant under the slot transposition $(s_1\ s_2)$). During proof
  extraction (`explain`), if two terms belong to the same slotted e-class via
  different symmetries in the e-class's permutation group, a naive tree
  extractor produces mismatched slot names at the join point unless explicit
  slot-bijection and commutativity steps are inserted into the proof trace.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
When certifying Rust iterator fusion (`Iterator::map`/`zip`/`fold` vs. SIMD
loops) via `Compiles` and `Abstracts` in `theory/`, the certificate checker
should **not** implement slotted e-graph permutation group stabilization inside
Lean. Instead, the untrusted `slotted-egraphs` oracle extracts a linear rewrite
sequence where every alpha-renaming or slot permutation is emitted as an
explicit **Slot-Bijection Step** and every associative-commutative reordering is
emitted as a flat **Permutation Witness Array (`perm : Array UInt16`)** checked
in $O(N)$ integer comparisons by `theory/`.

#### 3.3 Cyclic Explanation Graphs and Exponential Tree Blowup Before Flatt et al. (FMCAD 2022)

Basis: documentation + source (Flatt, Coward, Willsey, Tatlock, and Panchekha,
*Small Proofs from Congruence Closure*, FMCAD 2022, DOI
`10.34727/2022/isbn.978-3-85448-053-2_13`).

An e-graph inherently contains cycles: for example, $a = f(a)$ or mutually
reachable congruence merges $c_1 \leftrightarrow c_2$ where child e-classes
depend on parent merges. Prior to Flatt et al. (FMCAD 2022), `egg`'s proof
extractor (`Explanation`) suffered from two severe failure modes when generating
certificates for external checkers:

- **Cycles in congruence explanations causing non-termination:** When an e-node
  merge was justified by congruence over child e-classes whose own shortest
  equivalence path traversed the parent merge, naive recursive explanation
  extraction entered an infinite loop unless union-find timestamps strictly
  gated child recursive calls.
- **Exponential tree proof blowup ($> 10^7$ steps from a $10^3$-node e-graph):**
  When the extracted explanation was flattened into a tree-structured equational
  proof without sub-proof DAG sharing, shared sub-derivations (such as a rewrite
  applied inside a multi-use variable or across $k$ rounds of a loop/hash body)
  were duplicated $2^k$ times, causing downstream proof checkers to run out of
  memory or time out after hours on optimizations that took milliseconds to
  discover.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
Because `TrustedBoundary.lean` forbids `partial` definitions (line 314) and
requires every certificate check to terminate inside Lean's kernel WHNF reducer,
`EqSatCert` and `EgglogProvenanceCert` in `theory/` must enforce two structural
invariants:
1. **Hash-Consed DAG Representation (`TermArena` + `DAGRewriteStep`):** Proof
   certificates must reference sub-proofs and subterms by integer DAG IDs so
   shared subterm rewrites are checked once ($O(|V_{\text{DAG}}|)$), completely
   preventing tree-expansion blowup.
2. **Strictly Increasing Topological Step IDs (`premiseId < step.id`):** Every
   congruence or Horn derivation step $k$ in the certificate array may only cite
   premise steps with index $p < k$. This simple integer guard (`p < k`) makes
   cyclic explanations syntactically unrepresentable and allows the Lean checker
   to verify the entire proof in a single structural `Array.foldl` pass without
   cycle detection or fuel parameters!

#### 3.4 Combinatorial E-Graph Blowup on Associative-Commutative (`AC`) Rules

Basis: documentation + derived (`egg` / `egglog` AC-saturation benchmarks;
Schneider et al. PLDI 2024).

Adding raw associativity $(x + y) + z \leftrightarrow x + (y + z)$ and
commutativity $x + y \leftrightarrow y + x$ rules to a standard binary e-graph
causes a $k$-operand sum $x_1 + x_2 + \dots + x_k$ to generate $k! \cdot C_{k-1}$
distinct binary tree structures across $2^k - 1$ sub-term e-classes. Even for
$k = 8$ (such as an 8-lane SIMD horizontal XOR/add reduction or an 8-term
pointer-offset expression), the e-graph explodes to tens of thousands of nodes
and emits quadratic-length bubble-sort swap chains in its proof certificates.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
For associative-commutative operations in `theory/` (wrapping `BitVec` addition,
bitwise `xor`/`and`/`or`, polynomial addition/multiplication), Anneal's rewrite
checker should include a native **`ac_norm` certificate step** that flattens an
arbitrary binary tree of an AC operator into a list of $N$ leaf `TermId`s and
verifies equivalence against another flattened list using an untrusted
permutation witness `perm : Array UInt16` in $O(N)$ kernel steps.

---

### 4. Computer Algebra, SDP/SOS, Floating-Point, and CHC Certifier Failures

#### 4.1 CAS Branch-Cut, Singularity Cancellation, and `Mathematica` 9.0.1 CRT Determinant Soundness Bugs

Basis: documentation + execution (Durán, Pérez, and Varona, *Notices of the AMS*
61(10):1249–1252, 2014, DOI `10.1090/noti1173`; Fateman, symbolic algebra domain
hazards).

Computer algebra systems (`Mathematica`, `Maple`, `Maxima`, `Singular`) optimize
for generic algebraic fields of characteristic zero or modular homomorphic images
rather than total program semantics, leading to three well-documented classes of
unsoundness:

- **The Durán–Pérez–Varona `Mathematica` 9.0.1 large-integer determinant bug
  (2014):** While studying Karlin–Szegő orthogonal polynomials, Durán, Pérez,
  and Varona discovered that `Mathematica` (versions 8 through 9.0.1) computed
  completely wrong values for determinants of exact integer matrices with
  10,000-digit entries—and even returned *different* wrong integers on repeated
  evaluations of `Det[M]` on the *exact same immutable matrix*! Root-cause
  analysis traced the bug to `Mathematica`'s modular Chinese Remainder Theorem
  (CRT) / homomorphic image linear-algebra routines, where an internal buffer
  / prime-modulus overflow and uninitialized memory read corrupted the CRT
  reconstruction.
- **Generic field division erasing zero-divisor singularities:** CAS
  simplifiers routinely rewrite $\frac{x^2 - 1}{x - 1} \to x + 1$ or cancel
  common factors $g(\vec{x})$ from both sides of $g(\vec{x}) \cdot A(\vec{x}) =
  g(\vec{x}) \cdot B(\vec{x})$, which is invalid at roots $g(\vec{x}) = 0$.
- **Complex branch-cut violations in radical and transcendental identities:**
  Simplifying $\sqrt{x y} \to \sqrt{x}\sqrt{y}$ (false for $x = y = -1$) or
  $\ln(e^z) \to z$ introduces sign errors when applied to real domains without
  positivity certificates.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
When verifying cryptographic field arithmetic (`Curve25519`, `P-256`, `BLS12-381`,
`ML-KEM` NTT) using `Singular` or `CryptoLine`, Anneal must **never** trust the
CAS's internal Gröbner basis engine or modular CRT reconstruction. Instead,
`Singular` is used solely to compute the **explicit Nullstellensatz polynomial
co-factors** $(q_0, q_1, \dots, q_m) \in (\mathbb{Z}[\vec{x}])^{m+1}$ for
$$f(\vec{x}) - g(\vec{x}) = q_0(\vec{x}) \cdot p + \sum_{k=1}^m q_k(\vec{x}) \cdot h_k(\vec{x}).$$
Inside `theory/`, `checkIdealCert` expands both sides over exact GMP-backed
`Int` polynomials (`Init.Data.Int.Basic`) via `normHorner` without ever dividing
by a polynomial or using modular primes! Furthermore, in Anneal's `Language
SemObs` and `BehaviorCodec`, redundant multi-limb representations $(z_0, \dots,
z_4)$ preserve bijection in `BehaviorCodec.decodeOut` by keeping the full
5-limb integer tuple in `L_v.Out` while projecting modulo $p$ in `L_v.obs : Out
→ SemObs`, ensuring `obs_decodeOut` holds without any unverified CAS division.

#### 4.2 Floating-Point SDP Solvers Returning Pseudo-SOS Matrices with Negative Eigenvalues

Basis: documentation + derived (Peyrl and Parrilo, *Theoretical Computer
Science* 409(2):269–281, 2008, DOI `10.1016/j.tcs.2008.06.006`; Monniaux and
Corbineau, ITP 2011, `arXiv:1105.4421`; Harrison, TPHOLs 2007).

To prove a universal nonlinear polynomial inequality $\forall \vec{x} \in
\mathbb{R}^n,\; P(\vec{x}) \ge 0$ via Putinar's or Stengle's Positivstellensatz,
sum-of-squares (`SOS`) tools formulate a Semidefinite Program (`SDP`) finding a
positive semidefinite (`PSD`) Gram matrix $Q \succeq 0$ such that $P(\vec{x}) =
v(\vec{x})^T Q v(\vec{x})$, and solve it using numerical interior-point solvers
(`CSDP`, `MOSEK`, `SDPA`, `SeDuMi`, `Clarabel`). Two fundamental failure modes
occur when bridging numerical SDP outputs to formal proof assistants (Coq
`Micromega`/`Psatz`, HOL Light `SOS`, Lean):

- **Numerical violation of the affine polynomial matching equations ($P(\vec{x})
  \neq v(\vec{x})^T \tilde{Q} v(\vec{x})$):** Floating-point interior-point
  solvers return an approximate matrix $\tilde{Q} \in \mathbb{F}_{64}^{N \times
  N}$ that satisfies the linear coefficient matching constraints only up to
  $10^{-8}\text{--}10^{-12}$. Naive rounding of $\tilde{Q}$ to rationals
  $\mathbb{Q}^{N \times N}$ breaks the algebraic identity $P(\vec{x}) =
  v(\vec{x})^T Q v(\vec{x})$.
- **Degenerate / boundary SOS problems and negative eigenvalues ($\lambda_{\min}
  < 0$):** As documented by Peyrl & Parrilo (2008) and Monniaux & Corbineau
  (2011), when $P(\vec{x})$ has real zeros (for example, $P(x, y) = (x - y)^2
  \ge 0$ or a tight loop ranking bound $V(s) - V(s') - 1 \ge 0$ that is exact at
  the boundary), every valid Gram matrix $Q$ lies on the **boundary** of the PSD
  cone ($\det(Q) = 0$, $\lambda_{\min}(Q) = 0$) rather than its strict interior
  ($Q \succ 0$). When the numerical matrix $\tilde{Q}$ is orthogonally projected
  onto the exact rational affine subspace $\{Q \in \mathbb{Q}^{N \times N} \mid
  P(\vec{x}) = v(\vec{x})^T Q v(\vec{x})\}$, numerical drift pushes the zero
  eigenvalues slightly negative ($\lambda_{\min}(Q_{\mathbb{Q}}) \approx
  -10^{-9}$), causing exact rational Cholesky ($L D L^T$) decomposition to fail
  with a negative diagonal pivot $D_{k,k} < 0$!

**Architectural Lesson for Anneal's `trusted/` Primitives:**
1. In `theory/`, `checkSOSCert` must **never** accept a floating-point matrix or
   run numerical eigenvalue checks. It must require an **exact rational square
   decomposition** $P(\vec{x}) - \sum_i \sigma_i(\vec{x}) g_i(\vec{x}) =
   \sum_{j=1}^r c_j q_j(\vec{x})^2$ with denominator-cleared integer
   coefficients (`Int` from `foundation-lock.json`, since `Rat` is not in
   `foundation-lock.json`!).
2. To handle degenerate boundary polynomials where $P(\vec{x})$ has zeros, the
   untrusted external generator must either perturb the target inequality by a
   strictly positive slack tolerated by the specification (e.g., proving
   $\varepsilon$-relaxed error bounds in `Abstracts`), restrict the projection
   to the facial subspace orthogonal to the rational kernel vectors of $Q$
   (Monniaux & Corbineau 2011), or emit a CAD/Bernstein interval subdivision
   certificate (`CADCert`).

#### 4.3 `FPTaylor` and `Gappa` Subnormal Gradual Underflow, `NaN` Propagation, and Directed-Rounding Failures

Basis: documentation + source + derived (Solovyev, Baranowski, Jacobsen,
Briggs, Rakamarić, and Gopalakrishnan, *ACM TOPLAS* 41(1):2:1–2:39, 2018, DOI
`10.1145/3230733`; Daumas and Melquiond, `Gappa` / `Flocq` IEEE-754
formalization).

In floating-point verification, simplified real-error models frequently use the
standard textbook rounding formula $\text{fl}(x \odot y) = (x \odot y)(1 +
\delta)$ with $|\delta| \le u$ ($u = 2^{-24}$ for `f32`, $u = 2^{-53}$ for
`f64`). Historical experience with `FPTaylor`, `Gappa`, and SMT `QF_FP` solvers
identifies four critical failure modes when this simplified model is applied to
real Rust code:

- **Unsoundness of pure relative-error $(1 + \delta)$ on subnormal gradual
  underflow:** For IEEE-754 results in the subnormal range ($|x \odot y| <
  2^{-126}$ for `f32` or $< 2^{-1022}$ for `f64`), the relative error $|\delta|$
  is **not** bounded by $2^{-24}$ (it can be as large as $100\%$ when a nonzero
  product underflows to `0.0`!). Only the combined model $\text{fl}(x \odot y) =
  (x \odot y)(1 + \delta) + \eta$ with $|\delta| \le u$, $|\eta| \le \eta_{\max}$
  ($2^{-150}$ for `f32`, $2^{-1075}$ for `f64`), and $\delta \cdot \eta = 0$ is
  sound across the normal/subnormal boundary (and for division $\text{fl}(x / y)$
  or `sqrt`, `FPTaylor` had to treat subnormal operands via separate absolute
  bounds because $(x / y)(1 + \delta) + \eta$ is not even preserved under
  nested Taylor expansion if the denominator $y$ can approach zero!).
- **Division-by-zero and `NaN` swallowing in interval arithmetic:** If an
  interval denominator $[ \underline{y}, \overline{y} ]$ straddles zero ($0 \in
  [\underline{y}, \overline{y}]$), IEEE-754 produces `±Infinity` or `NaN`. Once a
  `NaN` enters a computation, every relational comparison (`x <= MAX`) evaluates
  to `false`, yet unguarded real-interval models that neglect `¬isNaN` flags can
  falsely certify bounds before `unsafe { f32::to_int_unchecked::<i32>(x) }`.
- **Fused Multiply-Add (`FMA`) vs. double-rounded `a * b + c` mismatch:** If a
  verifier assumes `a * b + c` undergoes two roundings while the target CPU/LLVM
  emits an FMA instruction (or vice versa via `mul_add`), Sterbenz subtraction
  invariants (`x - y` exact when $1/2 \le y/x \le 2$) and sign-of-error
  certificates can be invalidated.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
1. In `trusted/lean/`, the `@[candidate float]` (and eventually `@[vetted]`)
   MIR floating-point semantics must model bit-exact IEEE-754 operations
   (including subnormals, signed zeros `-0.0`, `±Infinity`, `NaN` propagation,
   and explicit non-contraction of `+`/`*` unless `f32::mul_add` is called,
   matching the Rust Reference).
2. In `theory/`, `GappaCert` and `TaylorModelCert` checkers must verify both
   **finite non-`NaN` enclosure (`isFinite`)** and **exact dyadic mantissa-exponent
   bounds (`DyadicInterval`)** accounting for the subnormal absolute error step
   $\eta$. When mapped onto `Abstracts L_v L_{\text{MIR}} codec v s`, `L_v.sem v q`
   defines the set of acceptable `Float32`/`Float64` outputs (`Out → Prop`) as
   `fun o => o.isFinite ∧ |toDyadic o - f_real q| ≤ ε`, so refinement `s ≤
   codec.toMorphism v` simultaneously proves absence of `NaN`/`±Inf` UB and
   quantitative error bounds!

#### 4.4 `Spacer`, `Eldarica`, and `Golem` CHC Soundness Bugs on Arrays and Algebraic Datatypes

Basis: documentation + execution (`CHC-COMP` 2020–2024 competition reports;
`PyCHC` validation framework; `Z3Prover/z3` `Spacer` issue tracker).

In Constrained Horn Clause (`CHC`) solving (`Spacer` in `Z3`, `Eldarica`,
`Golem`), `CHC-COMP` evaluations and `PyCHC` cross-checking uncovered recurring
soundness bugs (returning `sat`/safe on unsafe CHC systems or `unsat`/unsafe on
satisfiable ones):

- **Unsound array quantifier projection in `Spacer` MBP (Model-Based
  Projection):** `Spacer` uses Model-Based Projection (`MBP`) to eliminate
  existential variables when computing predecessor states across Horn clauses
  over arrays (`QF_ABV` / `QF_ALIA`). Bugs in array `select`/`store` index
  aliasing during `MBP` occasionally dropped an aliasing disequality $i \neq j$,
  producing an over-strengthened lemma that blocked reachable error states and
  caused `Spacer` to return `sat` (safe) with an invalid inductive invariant
  model $\mathcal{M}$.
- **Preprocessing clause inlining / resolution deleting self-loops (`Golem` /
  `Eldarica`):** When a CHC preprocessor eliminated intermediate predicate
  symbols with multiple occurrences in a clause body or cyclic dependency graphs
  over algebraic datatypes (`QF_DT`), unsound clause pruning occasionally
  dropped an unsatisfiable branch and reported `sat`.

**Architectural Lesson for Anneal's `trusted/` Primitives:**
Whenever Anneal uses `Spacer`, `Eldarica`, or `Golem` to synthesize relational
loop invariants or inter-procedural `StepResult.externalCall` contracts, Anneal
must **never** accept the CHC solver's `sat` verdict alone. Instead, the CHC
solver must output the explicit symbolic predicate interpretation $\mathcal{M}(P_i)$
(`CHCModel`), and Anneal's `theory/Anneal/Solv/CHCCheck.lean` substitutes
$\mathcal{M}(P_i)$ into every Horn clause $c_j$ of the `SmallStepMachine`
transition system and requires an independent, kernel-checked ground `Alethe` +
`LIACert` + `LRAT` proof that each substituted clause $\neg c_j[\mathcal{M}]$ is
unsatisfiable. If `Spacer`'s `MBP` had a soundness bug, $\mathcal{M}$ will fail
inductiveness on at least one clause $c_j$, and `checkCHCCert` will reject it!

---

### 5. Kernel Reduction, Memory Walls, and Native-Compilation Trust Gaps

#### 5.1 Why `TrustedBoundary.lean` Forbids `native_decide` (`Lean.ofReduceBool`): The Native-Compiler and FFI Trust Gap

Basis: source + normative (`trusted/audit/TrustedBoundary.lean` lines 312–329,
972; `trusted/lean/foundation-lock.json`; Lean 4 `Lean.ofReduceBool` /
`Std.Tactic.BVDecide` architecture; Coq `vm_compute` / `native_compute` CVE/bug
history).

In Lean 4's standard library (`Std.Tactic.BVDecide`), large `LRAT` certificates
produced by `CaDiCaL` are checked using `native_decide` (which invokes the
kernel axiom `Lean.ofReduceBool`). When `Lean.ofReduceBool` is evaluated, the
Lean kernel does **not** reduce the boolean expression using its small,
auditable WHNF reducer; instead, it compiles the Lean function to C, invokes a
system C compiler (`clang`/`gcc`), dynamically loads the resulting shared
library, executes native machine code (including any `@[implemented_by]` or
`@[extern]` C FFI hooks), and trusts the returned boolean bit!

Historically, both Coq's `vm_compute` / `native_compute` and Lean's native
execution path have demonstrated why a high-assurance verifier like Anneal must
exclude native evaluation from its default TCB:

- **Expanding the TCB by $10^6$ lines of C/LLVM compiler and runtime code:**
  Trusting `native_decide` places Lean's IR compiler, C code generator, `clang`
  optimization passes, and dynamic linker inside the soundness boundary.
- **Silent activation of `@[implemented_by]` and `@[extern]` overrides:** In
  Lean 4, if any transitive dependency attaches `@[implemented_by]` or
  `@[csimp]` to a function, the kernel WHNF reducer ignores that attribute and
  reduces the pure logical definition, whereas `native_decide` executes the
  unverified replacement function!
- **Non-replayability in clean kernel environments:** `TrustedBoundary.lean`
  (line 160 and line 972) loads `.olean` files with `trustLevel := 0`,
  `plugins := #[]`, `loadExts := false`, and replays all declarations in
  `base.toKernelEnv.replay locals`. `TrustedBoundary.lean` explicitly rejects
  `Lean.Parser.Tactic.nativeDecide` (line 319) and `decide +native` (lines
  327–329), and excludes `Lean.ofReduceBool` from `foundation-lock.json`.

#### 5.2 The `Array.set` $O(N^2)$ Trap in Lean 4's Kernel WHNF Reducer vs. GMP `Nat` Fast Paths

Basis: source + execution + derived (`trusted/lean/foundation-lock.json`; Lean 4
kernel `whnf` reducer semantics for `Array` vs. `Nat`).

Because all certificate checkers in Anneal's `theory/` must execute inside Lean
4's interpreted kernel WHNF reducer (`rfl` / kernel `decide`), certificate
checkers that are fast in `#eval` or `native_decide` can hit a catastrophic
performance wall in the kernel if they overlook how the kernel reduces primitive
types:

- **The `Array.set` quadratic copying trap:** In the Lean 4 VM and C runtime,
  `Array α` uses reference counting; when an array has reference count $1$,
  `Array.set` mutates the underlying buffer in-place in $O(1)$ time. **Inside
  the Lean 4 kernel WHNF reducer, however, `Array α` is reduced via its logical
  model (`structure Array α where toList : List α`), where `Array.set` unfolds
  to `List.set`!** Every single `Array.set` call in a kernel `rfl` proof
  traverses and allocates a fresh `List` spine in $O(N)$ time. Consequently, an
  `LRAT` or `UnionFind` checker that performs $50,000$ `Array.set` updates on a
  $10,000$-element clause/literal table takes $5 \times 10^8$ list-cons steps in
  the kernel reducer and times out!
- **The Persistent Radix-Tree (`PArray` / `BinTree`) Solution:** Replacing
  `Array` with an explicit persistent binary/quaternary radix tree (`inductive
  RadixTree (α : Type) | leaf | node (val : Option α) (l r : RadixTree α)`) in
  `theory/` reduces both lookup and functional update to $O(\log_2 N) \le 16$
  constructor steps in the kernel WHNF reducer, restoring linearithmic scaling
  without any runtime array extensions.
- **Exploiting the Kernel's Native GMP `Nat` Fast Path:** Unlike `Array`, the
  Lean 4 kernel reducer has built-in C++/GMP primitives for closed `Nat`
  literals (`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.gcd`,
  `Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`,
  `Nat.shiftRight`). Therefore, representing dense bitsets as single multi-word
  `Nat` bitmasks (via `Nat.land` / `Nat.lor`) and representing linear/polynomial
  dot products over cleared-denominator `Nat` pairs executes in $O(1)$ native
  GMP kernel instructions!

#### 5.3 Monolithic `defnInfo` Memory Blowups in `base.toKernelEnv.replay` vs. `thmInfo` Cut-Splitting and Self-Verified Native Checkers

Basis: source + derived (`trusted/audit/TrustedBoundary.lean` lines 480–520,
972; Tan et al. `cake_lpr` TACAS 2021; Skotåm et al. `CreuSAT`).

In Coq (`Micromega`, `ring`, `SMTCoq`) and Lean 4, checking multi-megabyte
certificates inside the kernel hits a second wall: **AST memory footprint and
double evaluation during kernel replay**. In Anneal, every theorem in
`.anneal/Proof.lean` is checked twice—first by `lean` during compilation, and
second by `base.toKernelEnv.replay locals` during Phase 2 (`"audit"`) of
`TrustedBoundary.lean`.

Two structural hazards arise for large certificates ($> 10^5$ steps):

1. **`defnInfo` unfolding overhead:** If `.anneal/Proof.lean` defines a large
   certificate as a top-level `def my_cert : Array LRATStep := #[...]`
   (`ConstantInfo.defnInfo`), then `TrustedBoundary.exprEdges` walks the entire
   constructor AST of `my_cert`, and the kernel unfolds `my_cert` into memory
   whenever a theorem reduces `checkLRAT cnf my_cert = true`.
2. **Peak WHNF heap memory on monolithic reductions:** Reducing a single
   1,000,000-step `LRAT` proof in one `rfl` call keeps intermediate radix-tree
   versions alive in the kernel WHNF arena until the reduction completes.

**Two Compositional Solutions for Anneal's Architecture:**

- **Solution A — Proof-Irrelevant `thmInfo` Dominator Cut-Splitting (Zero TCB
  Change):** Partition a large `LRAT` or `Alethe` proof along intermediate
  dominator/cut clauses into chunks $C_1, \dots, C_K$ of $\le 5,000$ steps each.
  In `.anneal/Proof.lean`, emit each chunk as a `private theorem chunk_k :
  evalCut k = true := by exact checkChunk_sound <inline-packed-Nat-literal>
  rfl`. Because `chunk_k` is a `thmInfo` (`Prop`), Lean's kernel checks each
  chunk independently, frees its WHNF reduction heap immediately after checking,
  and **never unfolds `chunk_k`'s proof body** when checking `chunk_{k+1}` or
  `Proof.verify_crate`! Furthermore, packing the certificate bytes into a single
  hexadecimal `Nat` literal reduces `TrustedBoundary.exprEdges` traversal cost
  to $O(1)$ `Expr.lit (.natVal n)` node per chunk.
- **Solution B — Self-Verified Rust Certificate Checkers (`cake_lpr` / `CreuSAT`
  Pattern via Anneal `Trusted.CrateTheorem`):** Just as `cake_lpr` (verified in
  HOL4/CakeML) and `CreuSAT` (verified in Creusot/Why3) verify a native SAT/LRAT
  checker implementation once, Anneal can verify a standalone, zero-dependency
  Rust `LRAT`/`Alethe` checker crate `anneal-cert-check` using Anneal's own
  `Trusted.CrateTheorem Mir.crate` (`Abstracts L_{\text{LRAT}} L_{\text{MIR}}`).
  For standard crates, in-kernel `thmInfo` checking (Solution A) keeps the TCB
  minimal; for massive industrial bit-blasted hardware/cryptographic proofs, the
  Anneal-verified native checker provides a formally proved fast path.

#### 5.4 Master Synthesis: Failure Taxonomy Mapped to Anneal's 4 `trusted/` Primitives

| Failure Domain & Historical Incident | Root Cause of Unsoundness or Failure | Affected Anneal `trusted/` Primitive(s) | Mandatory Defense in Anneal `theory/` & `.anneal/Proof.lean` |
| :--- | :--- | :--- | :--- |
| **`drat-trim` parser overflow & missing EOF empty-clause check** (TACAS 2021) | 32-bit `int` wrap-around in C parser; premature exit `0` before deriving `[]` | `TrustedBoundary.lean`, `VerificationResult` | Never trust external C checker exit codes; embed `LRAT` in `.anneal/Proof.lean` and verify `derivedEmptyClause == true` in pure Lean |
| **`VeriPB` cyclic dominance & 64-bit cutting-plane overflow** (JAIR 2023) | Unconstrained deletion under non-trivial dominance preorder; `int64_t` overflow | `Language SemObs`, `Compiles`, `foundation-lock.json` | Use GMP-backed `Nat`/`Int` for all cutting planes; forbid non-equivalence dominance deletion in `Compiles` equivalence proofs |
| **`QBFfuzz` `DepQBF`/`CAQE` universal reduction soundness bugs** (SAT 2010) | Stale dependency-scheme caches dropping dependent $\forall$ literals | `SmallStepMachine` (`externalCall`), `ProductiveOn` | Replace multi-alternation `QRAT` checking with explicit **Skolem AIG circuits** $\vec{y} := \vec{S}(\vec{x})$ + propositional `LRAT` |
| **Bit-blasting `bvudiv x 0` / shift overshoot mismatch** (`SMTCoq`, `lean-smt`) | SMT-LIB total `bvudiv x 0 = -1` masks Rust MIR division-by-zero / shift UB | `Abstracts`, `BehaviorCodec`, `SmallStepMachine` | `BehaviorCodec` maps `.failed .ub` to `none`; `Abstracts` forces circuit guard to prove `divisor != 0 ∧ shift < width` |
| **`YinYang` / `Storm` / `Murxla` / `HistFuzz` 450+ SMT soundness bugs** (2020–2023) | Incremental `push`/`pop` lemma leakage, unsound string/NLA rewrites, `MBQI` bugs | `VerificationResult`, `SpecOn`, `TrustedBoundary.lean` | Zero trust in `Z3`/`cvc5` verdicts; require checkable `Alethe` + `LIACert` + `LRAT` + ground `InstCert` witnesses for every obligation |
| **`cvc5` / `veriT` `Alethe` `trust` holes & tactic proof blowup** (CAV 2025) | Unlogged preprocessing emits `:rule trust`; tactic reconstruction creates $10^7$ `Expr`s | `TrustedBoundary.lean` (`closure`, `exprEdges`, `replay`) | `TrustedBoundary` blocks `trust` axioms; run `cvc5` with proof-safe flags and check via reflective `TermArena` (`O(1)` `Expr` nodes) |
| **`egg` conditional rewrite e-class conflation & cyclic explanations** (FMCAD 2022) | Checking side conditions on e-class rather than ground term; cyclic congruence merges | `Abstracts`, `Compiles` (`Partial.defined`) | Check side conditions on concrete `TermId`s in `TermArena`; enforce topological step ordering `premiseId < step.id` on DAG proofs |
| **Slotted E-Graph binder capture & `AC` $n!$ e-node blowup** (PLDI 2024) | De Bruijn shifting breaks sharing; AC rules generate $n! C_{n-1}$ trees | `Compiles` (iterator/SIMD fusion) | Emit explicit slot bijections + flat `perm : Array UInt16` AC permutation witnesses verified in $O(N)$ kernel comparisons |
| **`Mathematica` 9.0.1 CRT determinant bug & CAS singularity cancellation** (AMS 2014) | Corrupted modular CRT reconstruction; dividing by zero-divisor polynomials | `Language SemObs` (`obs`), `BehaviorCodec` | Never divide polynomials or trust CAS Gröbner engines; verify explicit co-factors $f - g = q_0 p + \sum q_k h_k$ over `Int` via `normHorner` |
| **SDP/SOS negative eigenvalues $\lambda_{\min} \approx -10^{-9}$** (Peyrl & Parrilo 2008) | Floating-point SDP drift on degenerate boundary polynomials fails rational $L D L^T$ | `ProductiveOn` (nonlinear ranking), `SpecOn` | Require exact denominator-cleared rational sum-of-squares $\sum c_j q_j(\vec{x})^2$ over `Int`; use facial projection or Bernstein certificates |
| **`FPTaylor` / `Gappa` subnormal underflow & `NaN` swallowing** (TOPLAS 2018) | $(1+\delta)$ fails for subnormals ($< 2^{-126}$); interval division swallows `NaN` | `Abstracts` ($\varepsilon$-ball spec), `SmallStepMachine` | Include additive subnormal error $\eta$ and explicit `isFinite ∧ ¬isNaN` guards in `DyadicInterval`; model $\varepsilon$-balls via `Out → Prop` |
| **`Spacer` / `Eldarica` / `Golem` CHC `MBP` array aliasing bugs** (`CHC-COMP`) | Unsound existential array projection yields non-inductive invariant models $\mathcal{M}$ | `SmallStepMachine`, `EventualBehaviorOf` | Substitute candidate $\mathcal{M}(P_i)$ into each Horn clause $c_j$ and check ground UNSAT of $\neg c_j[\mathcal{M}]$ inside `theory/` |
| **Lean kernel `Array.set` $O(N^2)$ & monolithic `defnInfo` replay stall** | Kernel reduces `Array.set` as `List.set`; `defnInfo` unfolds during `replay` | `TrustedBoundary.lean` (`replay`), `foundation-lock.json` | Use persistent radix-2 trees (`PArray`), GMP `Nat`-packed literals, and proof-irrelevant `private theorem` (`thmInfo`) cut chunks |

## Boundaries

- **Known not to apply (trusting external solver exit codes or `native_decide`
  on Anneal's default trust boundary):** Under `trusted/audit/TrustedBoundary.lean`
  at `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`, conclusions from
  external solvers (`CaDiCaL`, `cvc5`, `Z3`, `egglog`, `Singular`, `Gappa`,
  `Spacer`) cannot enter `Proof.verify_crate` via `axiom`, `sorryAx`,
  `@[extern]`, `@[implemented_by]`, `native_decide`, or `decide +native`. Any
  external proof integration that depends on `Lean.ofReduceBool` is rejected
  during Phase 1 (`"preflight"`, lines 319 and 327–329) and Phase 2 (`"audit"`,
  axiom closure check against `foundation-lock.json`).
- **Unsupported (`Rat` and `Std.Sat` in `trusted/lean/foundation-lock.json`):**
  The locked Lean `v4.34.1` foundation (`trusted/lean/foundation-lock.json`)
  includes `Init.Data.Nat.*`, `Init.Data.Int.Basic`, `Init.Data.BitVec.BasicAux`,
  `Init.Data.ByteArray.Bootstrap`, and `Init.WF`, but does **not** include
  `Std.Sat`, `Std.Tactic.BVDecide`, or `Rat`. Consequently, certificate checkers
  in `theory/` must define their own self-contained `LRAT`, `Alethe`,
  denominator-cleared `Int` polynomial, and `DyadicInterval` checkers on top of
  `Init.*`.
- **Not examined (live fuzzing execution against 2026 nightly solver builds):**
  This report synthesizes published fuzzing campaigns, competition postmortems,
  and Anneal's pinned source code; we did not execute new multi-day `YinYang` or
  `Murxla` fuzzing runs against 2026 solver binaries during this investigation,
  because Anneal's zero-trust certificate architecture treats all past, present,
  and future external solver binaries as untrusted oracles.
- **Unknown (exact cut-chunk threshold where `base.toKernelEnv.replay` wall-clock
  time exceeds interactive IDE budgets across hardware targets):** While
  splitting `LRAT` and `Alethe` certificates into `private theorem` (`thmInfo`)
  cut chunks bounds peak kernel WHNF memory per chunk, the optimal chunk size
  (e.g., $2,500$ vs. $10,000$ steps) for sub-second `cargo anneal verify`
  turnaround on developer laptops depends on concrete `RadixTree` branching
  factors (`radix-2` vs. `radix-4` vs. `Nat`-packed bitsets) that must be
  benchmarked when implementing `theory/Anneal/Solv/`.

## Evidence

### Primary Anneal Repository Evidence (`joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`)

- **`trusted/PRINCIPLES.md` (lines 18–48):** Establishes that UB-freedom is
  always on, that Anneal never fails open, and that the TCB audit log must
  enumerate every trusted component and assumption.
- **`trusted/lean/lean-toolchain` (line 1):** Pins `leanprover/lean4:v4.34.1`.
- **`trusted/lean/Trusted.lean` (lines 9–11) and
  `trusted/lean/Trusted/Attributes.lean` (lines 1–140):** Defines `prelude`-based
  trust-tier attribute stripping (`Trusted.expandTrustDeclaration`) and the
  kernel expression guard `Trusted.candidate` (`@[vetted, reducible] def
  candidate (_feat : String) {α : Sort u} (x : α) : α := x`).
- **`trusted/audit/TrustedBoundary.lean` (lines 13–107, 156–207, 296–352,
  480–520, 960–1014):**
  - Lines 312–329 (`inspectSyntax`): Rejects `unsafe`, `partial`, `meta`,
    `axiom`, `coinductive`, `set_option`, `Lean.byElab`,
    `Lean.Parser.Tactic.runTac`, `Lean.Parser.Tactic.nativeDecide`, and `decide`
    with `native`.
  - Lines 156–165 (`importEnv`): Imports `.olean` artifacts at `trustLevel := 0`
    with `plugins := #[]`, `loadExts := false`, and `level := .private`
    (`env.setExporting false`).
  - Lines 480–520 (`exprEdges`) and line 972 (`base.toKernelEnv.replay locals`):
    Traverses all kernel `Expr` nodes in `locals` and replays all non-foundation
    constants in a clean `foundation`-only kernel environment.
- **`trusted/lean/foundation-lock.json`:** Locks the permitted `Init.*` module
  closure and restricts axioms to `Classical.choice`, `Quot.sound`, and
  `propext`.

### Primary Literature and Postmortem Evidence

1. **SAT / PB Certificate Checking (`cake_lpr`, `drat-trim`, `VeriPB`,
   `CakePB`):**
   - Yong Kiam Tan, Marijn J. H. Heule, and Magnus O. Myreen, *cake\_lpr:
     Verified Propagation Redundancy Checking in CakeML*, TACAS 2021, LNCS
     12652, pp. 223–241, DOI `10.1007/978-3-030-72013-1_18`. Documents
     `drat-trim` parser overflow bugs, missing empty-clause checks, and verified
     `LRAT`/`LPR` checking.
   - Bart Bogaerts, Stephan Gocht, Ciaran McCreesh, and Jakob Nordström,
     *Certified Dominance and Symmetry Breaking for Combinatorial Optimisation*,
     Journal of Artificial Intelligence Research (JAIR) 77:1539–1589, 2023, DOI
     `10.1613/jair.1.14714`, `arXiv:2211.09398`. Documents cyclic dominance
     hazards and checked vs. unchecked deletion conditions (Remark 16) in
     `VeriPB`.
2. **QBF Solver Fuzzing (`QBFfuzz`):**
   - Robert Brummayer, Florian Lonsing, and Armin Biere, *Automated Testing and
     Debugging of SAT and QBF Solvers*, SAT 2010, LNCS 6175, pp. 44–57, DOI
     `10.1007/978-3-642-14186-7_6`.
3. **SMT Solver Soundness Fuzzing (`YinYang`, `OpFuzz`, `Storm`, `Murxla`,
   `HistFuzz`):**
   - Dominik Winterer, Chengyu Zhang, and Zhendong Su, *Validating SMT Solvers
     via Semantic Fusion*, PLDI 2020, pp. 718–730, DOI
     `10.1145/3385412.3385985`; and *On the Unusual Effectiveness of Type-Aware
     Operator Mutations for Testing SMT Solvers*, OOPSLA 2020, DOI
     `10.1145/3428261`.
   - Muhammad Numair Mansur, Maria Christakis, Valentin Wüstholz, and Fuyuan
     Zhang, *Detecting Critical Bugs in SMT Solvers Using Blackbox Mutational
     Fuzzing* (`Storm`), ESEC/FSE 2020, pp. 701–712, DOI
     `10.1145/3368089.3409763`, `arXiv:2004.01980`.
   - Aina Niemetz, Mathias Preiner, and Armin Biere, *Murxla: A Modular and
     Highly Extensible API Fuzzer for SMT Solvers*, CAV 2022, LNCS 13372, pp.
     92–106, DOI `10.1007/978-3-031-13188-2_21`.
   - Weisong Sun, Chengyu Zhang, and Zhendong Su, *History-Driven Test Program
     Synthesis for SMT Solvers* (`HistFuzz`), ICSE 2023, pp. 1882–1894, DOI
     `10.1109/ICSE48619.2023.00161`, `arXiv:2302.01556`.
4. **SMT Proof Reconstruction (`Alethe`, `SMTCoq`, `lean-smt`):**
   - Abdalrhman Mohamed, Tomaz Mascarenhas, Harun Khan, Haniel Barbosa, Andrew
     Reynolds, Yoni Zohar, Clark Barrett, and Cesare Tinelli, *lean-smt: An SMT
     Tactic for Discharging Proof Obligations in Lean*, CAV 2025,
     `arXiv:2505.15796`.
5. **E-Graphs and Equality Saturation (`egg`, `Slotted E-Graphs`):**
   - Oliver Flatt, Samuel Coward, Max Willsey, Zachary Tatlock, and Pavel
     Panchekha, *Small Proofs from Congruence Closure*, FMCAD 2022, pp. 75–83,
     DOI `10.34727/2022/isbn.978-3-85448-053-2_13`.
   - Rudi Schneider, Thomas Kœhler, and Michel Steuwer, *Slotted E-Graphs*,
     PLDI 2024, PACMPL 8(PLDI):205, DOI `10.1145/3656430`.
6. **Computer Algebra, SDP/SOS, Floating-Point, and CHC Certifiers:**
   - Antonio J. Durán, Mario Pérez, and Juan L. Varona, *The Misfortunes of a
     Trio of Mathematicians Using Computer Algebra Systems. Can We Trust in
     Them?*, Notices of the AMS 61(10):1249–1252, 2014, DOI `10.1090/noti1173`.
   - Helfried Peyrl and Pablo A. Parrilo, *Computing sum of squares
     decompositions with rational coefficients*, Theoretical Computer Science
     409(2):269–281, 2008, DOI `10.1016/j.tcs.2008.06.006`.
   - David Monniaux and Pierre Corbineau, *On the Generation of
     Positivstellensatz Witnesses in Degenerate Cases*, ITP 2011, LNCS 6898, pp.
     249–264, `arXiv:1105.4421`.
   - Alexey Solovyev, Marek S. Baranowski, Ian Jacobsen, Charles Briggs, Zvonimir
     Rakamarić, and Ganesh Gopalakrishnan, *Rigorous Estimation of Floating-Point
     Round-Off Errors with Symbolic Taylor Expansions* (`FPTaylor`), ACM TOPLAS
     41(1):2:1–2:39, 2018, DOI `10.1145/3230733`.
   - Anvesh Komuravelli, Arie Gurfinkel, and Sagar Chaki, *SMT-Based Model
     Checking for Recursive Programs* (`Spacer`), Formal Methods in System
     Design / JAR 2016, DOI `10.1007/s10817-016-9376-4`.

## Revalidation

To revalidate the Anneal-specific architectural constraints and kernel reduction
findings after an upgrade to `trusted/lean/lean-toolchain`,
`trusted/lean/foundation-lock.json`, or `trusted/audit/TrustedBoundary.lean`:

1. **Check the `native_decide` and axiom allowlist boundary:** Inspect
   `inspectSyntax` in `trusted/audit/TrustedBoundary.lean` and run
   `cargo test --manifest-path trusted/audit/Cargo.toml` to verify that
   `native_decide`, `decide +native`, `partial`, `unsafe`, and custom axioms
   remain rejected in both `"preflight"` and `"audit"` modes.
2. **Check `foundation-lock.json` numeric and container primitives:** Inspect
   `trusted/lean/foundation-lock.json` to confirm which `Init.Data.*` modules
   are locked and whether `Array.set` in the target Lean release's kernel WHNF
   reducer still unfolds through `List.set` (tested by timing a 10,000-step
   kernel `rfl` reduction on `Array.set` vs. a depth-16 binary `RadixTree` under
   `base.toKernelEnv.replay`).
3. **Check `cvc5` / `CaDiCaL` proof-format granularity:** When pinning or
   upgrading an external solver binary in `cargo-anneal`, run the solver on a
   regression suite of `QF_ABV`, `QF_LIA`, and `QF_DT` verification conditions
   and verify that zero `:rule trust` or `:rule hole` steps appear in the emitted
   `Alethe` / `LRAT` certificates.
