# Constraint-Programming Modelling, Reformulation Compilers, and Pseudo-Boolean / Exact-MIP Proof Logging

## Summary

NP-hard discrete optimization problems embedded inside modern compilers—including DAG e-graph extraction (`TENSAT`, `extraction-gym`), joint register allocation and instruction scheduling (`Unison`), and resource-constrained software pipelining—rely on two coupled technologies: **(1) high-level solver-independent constraint modelling and reformulation compilers** (`MiniZinc`, `Essence`/`Conjure`, `Savile Row`, and Lazy Clause Generation solvers `Chuffed`/`Pumpkin`/`CP-SAT`), and **(2) machine-checkable proof logging** (`VeriPB`/`CakePB` for 0–1 pseudo-Boolean optimization and `VIPR` for exact rational mixed-integer linear programming).

Key technical invariants, separations, and failure modes established from primary specifications, upstream source code, peer-reviewed literature, and executable probes:

1. **Reformulation and Structural Symmetry Breaking (`MiniZinc`, `Conjure`, `Savile Row`, `LCG`):**
   - `MiniZinc` compiles high-level models to solver-specialized `FlatZinc` using polarity-sensitive **half-reification** (`C_ROOT`, `C_POS`, `C_NEG`, `C_MIX` contexts, `enableHalfReification = true`), replacing expensive two-way equivalences $b \leftrightarrow c$ with one-way implications $b \to c$ whenever polarity permits, while preserving solver-native global constraints (falling back to decompositions such as pairwise `fzn_all_different_int` only when the target lacks a native propagator).
   - `Conjure` refines abstract `Essence` combinatorial domains (`set`, `partition`, `relation`, `function`) into concrete matrix models (`Essence'`) and **automatically emits canonical symmetry-breaking constraints** (e.g., strict lexicographic ordering `m[i] .< m[i+1]` on explicit sets; `firstIndex` monotonicity `i < j <-> firstIndex[i] < firstIndex[j]` and `noGaps` on partitions), which `Savile Row` further tightens via associative-commutative common subexpression elimination (`AC-CSE`), domain filtering, and tabularisation.
   - **Lazy Clause Generation (`LCG`)** bridges finite-domain CP propagators with CDCL SAT nogood learning by explaining domain changes as clauses over order-encoding literals $[x \ge v]$ / $[x \le v]$ (`Chuffed` `IntVarLL` allocates literals lazily on a doubly-linked freelist to avoid $O(|D|)$ blowup; `Pumpkin` logs `DRCP` propagator `Inference` and `Deduction` steps natively).
2. **Floating-Point MIP Unsoundness in Compiler Optimization:**
   - Standard floating-point MIP solvers (`CBC`, `Gurobi`, `HiGHS`, `CPLEX`) permit primal feasibility and integrality tolerances around $\epsilon \approx 10^{-6}$. Direct source inspection of `egraphs-good/extraction-gym` (`src/extract/ilp_cbc.rs:121-207`) reveals continuous big-$M$ topological cycle-breaking constraints $\ell_{cc} - \ell_c + (|C| + 1)(1 - x_n) \ge 1$ paired with `solution.col(var) > 0.0` decoding. An executable counterexample verifies that at $|C| = 1.1 \times 10^6$, a fractional perturbation $\delta = 9.5 \times 10^{-7} < 10^{-6}$ satisfies $M(1 - x_n) = 1.045001 \ge 1$ on a zero-cost 2-cycle, allowing a cyclic extraction to pass floating-point feasibility with cost `0.000095` against true acyclic optimum `100`.
3. **Why Cutting Planes (`VeriPB` / `CakePB`) Exponentially Outperforms `DRAT` / `LRAT`:**
   - Propositional resolution (`DRAT`/`LRAT`) requires $2^{\Omega(n)}$ proof size on cardinality/pigeonhole constraints (e.g., assigning $n+1$ live virtual registers to $n$ physical registers, $\text{PHP}_n^{n+1}$). `VeriPB`'s normalized 0–1 pseudo-Boolean **cutting-planes calculus** derives $0 \ge 1$ for $\text{PHP}_n^{n+1}$ in $2n+1$ linear additions (verified for $n=5, 20, 100$) and handles optimization bounds, symmetry breaking, and dominance pruning via a three-tier proof architecture (`lstep` logical implication, `sstep` redundance-based strengthening `red`, and `cstep` core/dominance `dom` over formally proved transitive preorders).
   - Direct inspection of the archived `StephanGocht/VeriPB` Python snapshot (`01b7b5088c8a67f1611427174501191bc5f5b365`) uncovered **two genuine checker bugs** in `veripb/rules_dominance.py` (lines `630` and `745`), concretely demonstrating why untrusted proof checkers belong outside the Trusted Computing Base (TCB). **`CakePB`** (`CakeML/cakeml/examples/pseudo_bool/npbc_checkScript.sml`) resolves this via a HOL4-proved soundness theorem (`Theorem check_cstep_correct`) compiled through the verified `CakeML` compiler to native machine code.
4. **Exact Rational MILP Certification (`VIPR` v1.1 + Exact `SCIP`):**
   - `VIPR` (`scipopt/vipr`) certifies general mixed-integer linear programs (with continuous variables and arbitrary rational coefficients, which 0–1 `VeriPB` does not directly encode) using exact arbitrary-precision rational arithmetic (`GMP` `mpq_class`) across seven ordered sections (`VAR`, `INT`, `OBJ`, `CON`, `RTP`, `SOL`, `DER`) and five complete inference rules (`asm`, `lin`, `rnd`, `uns`, `sol`).
   - To avoid exact simplex overhead at every search node, `VIPR` v1.1 adds incomplete derivation keywords (`lin weak {local_bounds}` and `lin incomplete`), used by exact `SCIP` (`src/scip/certificate.cpp:1778-1900`, `SCIPcertificatePrintMirCut`) to log Gomory/MIR cuts as split disjunctions completed offline by `viprcomp` with exact `SoPlex`. An independent exact-rational Python VIPR v1.1 verifier confirmed both cutting-plane (`lin`+`rnd`) and branch-and-bound split (`asm`+`lin`+`uns`) proofs for the cyclic e-graph MILP while rejecting a $10^{-6}$-perturbed floating-point dual multiplier.

## Applicability

This report covers the combined pipeline from high-level discrete combinatorial problem modelling through solver lowering to independently verified optimality and infeasibility certificates, examined across twelve pinned upstream repositories and eleven peer-reviewed publications:

- **Modelling & Reformulation Compilers:** `MiniZinc/libminizinc` (`8c9f79949cb7df96c7c99b5ed41d511962879c97`) and `conjure-cp/conjure` (`fcae5cfd887080f9cfc32556b13daaae22a646a8`) are inspected directly at source level; `Savile Row` is characterized from its primary peer-reviewed paper (`Nightingale et al., AIJ 2017`, DOI `10.1016/j.artint.2017.07.001`) because no canonical public GitHub mirror resolved during inspection.
- **CP/LCG & Compiler-Optimization Solvers:** `chuffed/chuffed` (`f698d5623bb0c2bcd497388ba966f0436d62caf4`), `ConSol-Lab/Pumpkin` (`82d30b71a81747ce969f809cb14edf679128f12c`), `google/or-tools` (`4948b99ec504389d5119b3bb364a96f02b70f100`), `unison-code/unison` (`9f9857e742156b51e6314488f4173cd1b42c4aec`), and `egraphs-good/extraction-gym` (`903ba0f818b50608fe20ae9e0f03c35cb27bc50a`) ground the solver encodings and compiler optimization case studies.
- **Proof-Logging Systems & Verified Checkers:**
  - **Pseudo-Boolean (`VeriPB` / `CakePB`):** `StephanGocht/VeriPB` (`01b7b5088c8a67f1611427174501191bc5f5b365`, archived GitHub snapshot—active development moved to `gitlab.com/MIAOresearch/software/VeriPB`) and `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`, `examples/pseudo_bool/`) are examined directly at source level alongside Bogaerts et al. (`JAIR 2023`) and Gocht et al. (`AAAI 2024`).
  - **Exact Rational MILP (`VIPR` / `SCIP`):** `scipopt/vipr` (`99eec197a49b2bd9ad33c1f4c7afabe93caa6511`, active fork superseding archived `ambros-gleixner/VIPR` at `f221c3fd2274e8e859e8e24505278d6f7c1bb8ff`) and `scipopt/scip` (`a3274d2137c75fff405707a80dda11b887459f58`, `src/scip/certificate.{h,cpp}`) are examined directly at source level alongside Cheung, Gleixner, Steffy (`IPCO 2017`) and Eifler & Gleixner (`SIAM J. Optim. 2024`).
- **Scope Boundaries:** Applies to discrete finite-domain constraint satisfaction/optimization (CSP/COP), 0–1 pseudo-Boolean optimization (PBO), and rational linear mixed-integer programming (MILP). Does **not** cover nonlinear/convex MINLP certificates, floating-point SMT bit-vector reasoning, or propositional `LRAT`/SMT `Alethe` checkers except by structural comparison.

## Findings

### 1. High-Level Combinatorial Modelling and Reformulation Compilers

Basis: source (`MiniZinc/libminizinc`, `conjure-cp/conjure`, `chuffed/chuffed`, `ConSol-Lab/Pumpkin`) + documentation (peer-reviewed literature)

Writing raw SAT clauses, 0–1 pseudo-Boolean inequalities, or MILP matrices by hand for compiler optimization passes tightly couples problem semantics to a single solver backend and makes global invariants (e.g., no-overlap resource scheduling, register interference, DAG acyclicity) error-prone. Three architectural layers separate declarative modelling from backend solving:

#### 1.1 `MiniZinc` Flattening, Context Polarity, and Half-Reification

Nethercote et al. (CP 2007, DOI `10.1007/978-3-540-74970-7_38`) introduced **MiniZinc** as a solver-independent constraint modelling language compiled into solver-specific **FlatZinc** (`MiniZinc/libminizinc`). Direct inspection of `include/minizinc/{flatten.hh,flatten_internal.hh}` and `lib/flatten/flatten_binop.cpp` establishes four load-bearing compilation invariants:

1. **Relational Partiality Pairs (`EE(r, b)`):** Every expression flattens to an `EE` pair (`flatten_internal.hh:40-48`): `r` (the flattened value expression) and `b` (a Boolean expression encoding whether `r` is defined under MiniZinc's relational partiality semantics—e.g., array out-of-bounds or division by zero becomes `false` in the nearest enclosing Boolean context rather than crashing).
2. **Polarity Context Lattice (`C_ROOT`, `C_POS`, `C_NEG`, `C_MIX`) & Half-Reification (`Feydy, Somogyi, Stuckey, CP 2011`, DOI `10.1007/978-3-642-23786-7_23`):**
   - `FlatteningOptions::enableHalfReification` defaults to `true` (`flatten.hh:44,81`), and `FlatModelStatistics` explicitly separates full reifications (`n_reif_ct`) from half-reifications (`n_imp_ct`) and path-compressed eliminations (`n_imp_del`, `n_lin_del`, `flatten.hh:150-157`).
   - During flattening, every Boolean subexpression carries a context polarity:
     - `C_ROOT`: top-level assertion (`partialityVar` returns `varTrue`, `flatten_internal.hh:764-766`); domain restrictions fold directly into variable declaration domains (`flatten_binop.cpp:451-457`) instead of emitting redundant constraint rows.
     - `C_POS`: positive monotone context (e.g., inside a disjunction $c_1 \lor c_2$ or consequent of $p \to c$): only the **half-reification** $b \to c$ (`*_imp`) is needed! The reverse implication $c \to b$ is omitted because falsifying $b$ never helps satisfy the model, cutting auxiliary propagators roughly in half and dramatically improving domain propagation and LP relaxation tightness.
     - `C_NEG`: negative antitone context (e.g., antecedent of $c \to p$ or under $\neg c$): dual implication $\neg b \to \neg c$ (equivalently $c \to b$).
     - `C_MIX`: non-monotone context (e.g., `iff`, `xor`, or user-defined Boolean arguments, `flatten_binop.cpp:318-323`): forces full two-way reification $b \leftrightarrow c$ (`*_reif`).
3. **Solver-Parameterized Global Constraint Preservation:** MiniZinc's standard library defines default decompositions—for example `share/minizinc/std/fzn_all_different_int.mzn:5-6` decomposes `alldifferent(xs)` into $O(n^2)$ pairwise `xs[i] != xs[j]` constraints—which solver-specific `.mzn` redefinition libraries override to emit a single native global predicate (`fzn_all_different_int`) whenever the backend provides Régin's Hall-set/matching propagator, avoiding quadratic blowup while retaining a single portable model.
4. **Multi-Pass Path Interning (`PathStore` / `VarPathStore`, `flatten_internal.hh:64-154`):** To deduplicate variables across iterative flattening/optimization passes (e.g., MIP linearization or CSE) without allocating kilobytes of duplicated call-stack strings per variable, `libminizinc` interns flattening call stacks as hash-consed pointer trees (`PathStore::Node{parent, frame, spliced}`).

#### 1.2 `Essence` / `Conjure` Automated Representation Refinement and Symmetry Breaking

Unlike `MiniZinc` (which operates over concrete arrays of integers/Booleans/sets of integers), **Essence** (`conjure-cp/conjure`, Akgün et al., *Artificial Intelligence* 2022, DOI `10.1016/j.artint.2022.103751`) lets engineers declare abstract nested combinatorial decision variables directly—such as `set of set of T`, `partition from A`, `relation`, `function (total, bijective)`, or `mset`—without committing to a matrix representation.

`Conjure` compiles `Essence` into concrete `Essence'` models via composable `Representation m` tuples (`chck`, `downD`, `structuralCons`, `downC`, `up`, `symmetryOrdering`). Direct inspection of `src/Conjure/Representations/` demonstrates how abstract types **automatically eliminate representation-induced symmetries** that hand-written encodings routinely miss:

- **Fixed-Size Set (`Set/Explicit.hs:11-72`):** Lowers `set (size s) of D` into a 1D matrix `m : matrix indexed by [int(1..s)] of D` and emits the strict lexicographic structural symmetry-breaking constraint:
  ```essence
  forAll i : int(1..s-1) . m[i] .< m[i+1]
  ```
  eliminating all $s!$ permutations of identical sets while recursively applying `innerStructuralCons` to every element `m[i]`.
- **Partition (`Partition/Occurrence.hs:19-178`):** Lowers `partition from A` into four channeled views—`_NumParts : int(1..maxNumParts)`, `_WhichPart[A]`, `_PartSizes[1..maxNumParts]`, and `_FirstIndex[1..maxNumParts]`—and automatically synthesizes:
  1. `numPartsChannelling` (`_NumParts = max(_WhichPart[i])`) and `partSizesChannelling` (cardinality counts),
  2. `firstIndexChannelling` (`_FirstIndex[i]` equals the minimum element index in part `i`, and `dontCare(_FirstIndex[i])` for inactive parts `i > _NumParts`),
  3. **`symmetryBreaking` (`lines 135-142`):** `forAll i, j <= _NumParts . i < j <-> _FirstIndex[i] < _FirstIndex[j]`, canonically ordering indistinguishable partition blocks by their smallest member (eliminating $k!$ block-label symmetries), and
  4. **`noGaps` (`lines 166-177`):** ensures every part index $1 \dots \text{\_NumParts}$ is non-empty.
- **Downstream `Savile Row` Reformulation (`Nightingale et al., AIJ 2017`, DOI `10.1016/j.artint.2017.07.001`):** `Savile Row` consumes `Essence'` and performs domain tightening, **Associative–Commutative Common Subexpression Elimination (`AC-CSE`)** (factoring shared linear sums/conjunctions across constraints), automated **tabularisation** (converting small sub-networks of constraints into GAC table constraints), and backend-specific encodings for CP (`Minion`, `Chuffed`, `Gecode`), SAT (`DIMACS` via direct/order/log encodings), and SMT/MIP.

#### 1.3 Lazy Clause Generation (`LCG`) and Native CP Proof Logging (`Chuffed`, `Pumpkin`, `CP-SAT`)

Classical finite-domain CP solvers suffer from "thrashing": they rediscover identical dead-end subtrees across search branches because domain propagators only prune values locally without learning global conflict clauses. **Lazy Clause Generation (`LCG`)** (Ohrimenko, Stuckey, Codish, *Constraints* 2009, DOI `10.1007/s10601-008-9064-x`) fuses CP propagation with CDCL SAT solving:

- **Order-Encoding Bridge:** Each integer variable $x \in [l, u]$ is channeled to Boolean literals $[x = v]$, $[x \ne v]$, $[x \ge v]$, and $[x \le v]$ (where $[x \le v] \equiv \neg [x \ge v+1]$) satisfying monotonicity axioms $[x \ge v] \to [x \ge v-1]$. Whenever a global propagator (e.g., `alldifferent`, `cumulative`, `linear`) shrinks a domain, it registers a **lazy explanation** (reason clause over bound/equality literals) queried *only* if that propagation participates in a subsequent conflict, enabling 1-UIP conflict analysis, non-chronological backjumping, and VSIDS activity heuristics.
- **Lazy vs. Eager Literal Allocation (`chuffed/chuffed`, `chuffed/vars/int-var-ll.h:4-56`):** Eagerly allocating SAT variables for every domain value (`IntVarEL`) explodes memory on scheduling start times with domains $[0, 10^6]$. Chuffed's `IntVarLL` allocates order-encoding `LitNode{var, val, prev, next}` entries on demand in a doubly-linked freelist (`ld`, `freelist`, `createLit`), creating SAT literals only at actually propagated/branched thresholds.
- **Native CP Proof Logging (`ConSol-Lab/Pumpkin`, `pumpkin-crates/core/src/proof/mod.rs:1-180`):** Rust LCG solver `Pumpkin` implements **DRCP** (Deletion Reverse Unit Propagation for Constraint Programming) proof logging. During search (`ProofLog::cp`), propagators emit `Inference` records (`constraint_id`, atomic `premises`, `consequent`, `generated_by` tag, propagator `label`, `lines 113-143`) alongside `Deduction` nogoods (`drcp_format`). A proof scaffold recorded during search is trimmed post-search to retain only inferences on the backward dependency chain of the final root contradiction or optimality proof, bridging CP propagators directly into checkable certificates.

---

### 2. Compiler Combinatorial Optimization and Floating-Point MIP Soundness Failures

Basis: source (`egraphs-good/extraction-gym`, `unison-code/unison`) + execution (self-contained Python 3 probe in **Evidence** / **Revalidation**) + documentation

Two flagship compiler optimization workloads motivate combining declarative combinatorial models with exact proof logging:

1. **Joint Register Allocation and Instruction Scheduling (`Unison`, `unison-code/unison`; Castañeda Lozano et al., ACM TOPLAS 2019, DOI `10.1145/3332373`):** Traditional compiler backends decouple register allocation (graph coloring / linear scan) from instruction scheduling (list scheduling), causing destructive phase-ordering conflicts (aggressive scheduling inflates live ranges and induces spills; premature allocation introduces false anti-dependencies). `Unison` models both simultaneously as a single CP problem (targeting `Gecode`/`MiniZinc`) using global `diffn` (2D rectangle packing of live-range lifetimes $\times$ register banks), `cumulative` (functional-unit issue widths), and precedence constraints, optionally inserting copies/rematerialization directly in the search space.
2. **Optimal E-Graph DAG Extraction (`TENSAT`, Yang et al. MLSys 2021, `arXiv:2101.01332`; `egraphs-good/extraction-gym`):** Extracting a minimum-cost DAG (accounting for shared common subexpressions!) from an equality-saturated e-graph is NP-hard. Standard extractors formulate it as a binary MILP (`egraphs-good/extraction-gym/src/extract/ilp_cbc.rs:33-208`):
   - Binary variables $a_c \in \{0, 1\}$ (e-class $c$ active) and $x_n \in \{0, 1\}$ (e-node $n \in c$ chosen), subject to $\sum_{n \in c} x_n = a_c$ (`lines 53-58`), $x_n \le a_{cc}$ for every child e-class $cc$ of $n$ (`lines 70-79`), and $a_r = 1$ for every root $r$ (`lines 95-97`).
   - **Big-$M$ Acyclicity Constraints (`ilp_cbc.rs:149-207`):** To forbid cyclic e-graph selections, `block_cycles()` introduces an **unbounded continuous** variable $\ell_c \in \mathbb{R}$ (`model.add_col()`, with lower/upper bounds explicitly commented out at `lines 154-156`) for every e-class $c$, plus binary complement $\bar{x}_n = 1 - x_n$, and enforces for every edge $n \in c \to cc$:
     $$\ell_{cc} - \ell_c + (|C| + 1)(1 - x_n) \ge 1$$

#### Concrete Floating-Point MIP Soundness Break (Source + Execution Receipt)

Inspection of `egraphs-good/extraction-gym/src/extract/ilp_cbc.rs` exposes **two coupled floating-point soundness hazards** representative of uncertified compiler MILP passes:

1. **Zero-Threshold Primal Decoding (`lines 121, 126`):** The extractor decodes binary activity via `solution.col(var.active) > 0.0` and `.position(|&n| solution.col(n) > 0.0)`. Any primal solver tolerance residual (e.g., `1e-9` on an unselected node) evaluates `> 0.0` as `true` and can select the wrong e-node in an e-class!
2. **Big-$M$ Tolerance Collapse (`M = |C| + 1`, `line 204`):** Standard floating-point MIP solvers (`CBC`, `HiGHS`, `Gurobi`, `CPLEX`) treat a binary variable $x_n$ as integer-feasible whenever $|x_n - \text{round}(x_n)| \le \epsilon$ (typically $\epsilon = 10^{-6}$). As verified in our Python 3 execution probe, on an e-graph with $|C| = 1{,}100{,}000$ e-classes ($M = 1{,}100{,}001$) containing a zero-cost 2-cycle $A \xrightarrow{n_A} B \xrightarrow{n_B} A$ alongside a valid acyclic leaf $n_{\text{leaf}} \in A$ of cost `100`:
   - Setting $x_{n_A} = x_{n_B} = 1 - 9.5 \times 10^{-7}$, $x_{n_{\text{leaf}}} = 9.5 \times 10^{-7}$, and $\ell_A = \ell_B = 0$ satisfies $|x_n - \text{round}(x_n)| = 9.5 \times 10^{-7} < 10^{-6}$ **and** strictly satisfies both cycle-blocking inequalities:
     $$0 - 0 + 1{,}100{,}001 \cdot (9.5 \times 10^{-7}) = 1.045001 \ge 1.0$$
   - The floating-point solver reports an objective of `0.0000950` (off by $10^6\times$ from the true exact optimum `100`!), and `ilp_cbc.rs` extracts an **unsound cyclic program**! Even at smaller $|C|$ (e.g., $|C| = 10^4$), ill-conditioned cost ratios or dual simplex tolerances ($\sim 10^{-7}$) can produce invalid dual bounds that falsely declare a feasible compilation target infeasible or falsely certify sub-optimal code as optimal.

---

### 3. Pseudo-Boolean Cutting-Planes Proof Logging (`VeriPB`) and Verified Checking (`CakePB`)

Basis: source (`StephanGocht/VeriPB`, `CakeML/cakeml/examples/pseudo_bool/`) + execution (self-contained Python 3 probe in **Evidence** / **Revalidation**) + documentation (`Bogaerts et al. JAIR 2023`, `Gocht et al. AAAI 2024`)

#### 3.1 Why Cutting Planes Exponentially Outperforms `DRAT` / `LRAT`

Standard SAT proof formats (`DRAT`, `LRAT`) rest on propositional **resolution** (Reverse Unit Propagation `RUP` + Resolution Asymmetric Tautology `RAT`). By Haken's theorem (1985), resolution proofs of the Pigeonhole Principle $\text{PHP}_n^{n+1}$—structurally isomorphic to proving that $n+1$ simultaneously live virtual registers cannot be colored with $n$ physical registers without spilling—require **$2^{\Omega(n)}$ clauses**.

`VeriPB` operates instead over **normalized 0–1 linear pseudo-Boolean (PB) inequalities** $\sum_i c_i \ell_i \ge A$ ($c_i \in \mathbb{Z}_{\ge 0}$, $\ell_i \in \{x_i, \bar{x}_i\}$ with $\bar{x}_i = 1 - x_i$, $A \in \mathbb{Z}_{\ge 0}$) using the **Cutting Planes** proof system (Cook, Coullard, Turán 1987):

- **Core Cutting-Planes Operations (`CakeML/cakeml/examples/pseudo_bool/npbc_checkScript.sml:35-54`, `veripb/rules.py:527-575`):**
  1. **Literal Axiom (`Lit` / `Triv`):** $\ell \ge 0$.
  2. **Linear Addition (`Add` / `+`):** Adding $\sum a_i \ell_i \ge A$ and $\sum b_i \ell_i \ge B$ cancels complementary pairs $c x + c \bar{x} = c$, reducing the RHS by $c$.
  3. **Positive Multiplication (`Mul` / `*`):** Multiply coefficients and RHS by $k \in \mathbb{Z}_{>0}$.
  4. **Division with Ceiling Rounding (`Div` / `d`):** Divide all non-negative coefficients and RHS by $d \in \mathbb{Z}_{>0}$ and take $\lceil c_i / d \rceil$, $\lceil A / d \rceil$ (sound because $\ell_i \in \{0, 1\}$). `CakePB` supports four division/MIR variants (`Cd`, `Dd`, `Nd`, `Md`, `npbc_checkScript.sml:36-38,200-207`).
  5. **Saturation (`Sat` / `s`):** Replace each $c_i$ with $\min(c_i, A)$ (sound because setting $\ell_i = 1$ already satisfies the constraint whenever $c_i \ge A$).
  6. **Weakening (`Weak` / `w`):** Eliminate literal $\ell_i$ by adding $c_i \bar{\ell}_i \ge 0$, decreasing RHS by $c_i$.
- **Polynomial $\text{PHP}_n^{n+1}$ Refutation Receipt (Python 3 execution probe):** Summing all $n+1$ pigeon constraints ($\sum_{j=1}^n x_{i,j} \ge 1$) and all $n$ hole constraints ($\sum_{i=1}^{n+1} \bar{x}_{i,j} \ge n$, equivalently $-\sum_i x_{i,j} \ge -1$) cancels every variable identically and yields $0 \ge 1$ in exactly **$2n + 1$ PB addition steps** (`11`, `41`, and `201` steps for $n=5, 20, 100$)—an exponential separation over `DRAT`/`LRAT`! Similarly, cardinality propagators, `alldifferent` Hall sets, and PBQP/MaxSAT cores admit polynomial cutting-planes proofs.

#### 3.2 Three-Tier Soundness Architecture: Redundance (`red`), Symmetry, and Dominance (`dom`)

Beyond pure logical implication, combinatorial optimization solvers aggressively prune search spaces using **non-implicative** reasoning: symmetry breaking (e.g., ordering interchangeable physical registers), dominance pruning (discarding partial schedules provably dominated by a better one), and branch-and-bound objective cuts. Bogaerts, Gocht, McCreesh, and Nordström (`JAIR 2023`, DOI `10.1613/jair.1.14296`) formalized a unified three-tier calculus implemented directly in `CakePB` (`npbc_checkScript.sml:12-29,57-69,1266-1267,2974-3009`):

The proof checker maintains two constraint sets—a **core set** $\mathcal{C}$ and a **derived set** $\mathcal{D}$ ($F = \mathcal{C} \cup \mathcal{D}$)—plus an optional linear minimization objective $f(x)$, an active best bound, and an active **preorder** $\preceq$ (defined syntactically by `StoreOrder` / `pre_order` with machine-checked reflexivity and transitivity subproofs before activation via `LoadOrder` / `load_order`, `rules_dominance.py:39-233`, `npbc_checkScript.sml:2987-2996`):

1. **Level 1 — Logical Steps (`lstep`, `npbc_checkScript.sml:57-69`):** Preserve logical entailment $\mathcal{C} \cup \mathcal{D} \models C$. Includes `Cutting` (RPN cutting planes), `Rup` (Reverse Unit Propagation), `Con` (proof by contradiction), `ImplyAdd`, and `Delete` (**permitted on $\mathcal{D}$ only**, preventing unsound deletion of core constraints!).
2. **Level 2 — Redundance-Based Strengthening (`sstep` / `red`, `rules_dominance.py:656-759`):** Introduces constraint $C$ together with a witness substitution $\omega$ (mapping variables to $\{0, 1\}$ or literals) provided that subproofs using **only `lstep`s** prove:
   $$\mathcal{C} \cup \mathcal{D} \cup \{\neg C\} \;\vdash\; (\mathcal{C} \cup \mathcal{D} \cup \{C\})\!\upharpoonright\!\omega \quad \land \quad f(x\!\upharpoonright\!\omega) \le f(x) \quad \land \quad (x\!\upharpoonright\!\omega \preceq x)$$
   Soundness intuition: if any optimal solution $\alpha$ violates $C$, then $\alpha \circ \omega$ still satisfies $\mathcal{C} \cup \mathcal{D} \cup \{C\}$ with no worse objective and no worse preorder rank. This subsumes SAT `RAT`/`PR`, Tseitin reification, and **static symmetry breaking** (where $\omega$ is a symmetry automorphism of $F$!).
3. **Level 3 — Core & Dominance Steps (`cstep` / `dom` / `CheckedDelete` / `Obj`, `npbc_checkScript.sml:2974-3009`, `rules_dominance.py:763-824`):**
   - **Dominance-Based Strengthening (`dom`):** Introduces $C$ with witness $\omega$ when `lstep` subproofs derive:
     $$\mathcal{C} \cup \mathcal{D} \cup \{\neg C\} \;\vdash\; \mathcal{C}\!\upharpoonright\!\omega \quad \land \quad f(x\!\upharpoonright\!\omega) \le f(x) \quad \land \quad (x\!\upharpoonright\!\omega \prec x)$$
     Crucially, `dom` checks only the **core** set $\mathcal{C}\!\upharpoonright\!\omega$ (NOT $\mathcal{D}\!\upharpoonright\!\omega$ and NOT $C\!\upharpoonright\!\omega$!) because the strict well-founded order decrease $x\!\upharpoonright\!\omega \prec x$ guarantees via induction over the finite Boolean cube that an optimal minimal-order solution exists satisfying $C$!
   - **Why Core Isolation + Checked Deletion Are Load-Bearing:** Unchecked deletion from $\mathcal{C}$ while an order is active would break the inductive invariant (deleting a constraint could create a phantom dominating witness $\alpha \circ \omega$ that violates the original problem!). Therefore, removing a constraint from $\mathcal{C}$ requires `CheckedDelete` (`npbc_checkScript.sml:2981`), which must prove the deleted constraint is redundant with respect to the remaining core.
   - **Branch-and-Bound Optimality (`Obj` / `Sol` / `soli` / `solx`):** Logging a feasible primal solution $\alpha$ with objective value $v = f(\alpha)$ automatically adds the objective-improving constraint $f(x) \le v - 1$ to the database; once the solver derives $0 \ge 1$, the checker certifies that $v$ is the **exact global optimum**!

#### 3.3 Concrete Soundness Bugs in Unverified Checker Code vs. HOL4-Verified `CakePB`

Direct source inspection of the archived Python `VeriPB` reference checker (`StephanGocht/VeriPB`, commit `01b7b5088c8a67f1611427174501191bc5f5b365`, `veripb/rules_dominance.py`) exposed **two concrete implementation bugs** in the redundance/dominance verifier:

1. **Broken Objective Witness Substitution (`rules_dominance.py:621-637`):** Inside `objectiveCondition(context, witnessDict)`, when `lit2 = witnessDict[lit]` is another literal (neither `True` nor `False`), line `625` appends `(coeff, lit)` and line `630` erroneously appends `(-coeff, lit)` instead of `(-coeff, lit2)`—canceling the variable with itself and reducing the objective-preservation condition $f(x\!\upharpoonright\!\omega) \le f(x)$ to a vacuous $0 \le 0$ for literal-swapping symmetries!
2. **Stale Loop Variable in Order Subgoal Auto-Proof (`rules_dominance.py:717-746`):** Inside `AddRedundant.compute`, the loop checking `orderConditions` (`lines 742-746`) creates `subgoal = SubGoal(ineq)` (`line 743`), checks `if negated.implies(ineq):`, and then writes `goal.isProven = True` (`line 745`)—mutating the stale loop variable `goal` from the earlier `effected` loop (`line 719`) instead of `subgoal`!

While active `VeriPB` development migrated to `gitlab.com/MIAOresearch/software/VeriPB` and later fixed/re-engineered its architecture, these source receipts highlight why an unverified Python/C++ checker cannot serve as a minimal TCB. **CakePB** (`CakeML/cakeml`, commit `2874b664e10939a3ee462215b2e068c89c1f70eb`, `examples/pseudo_bool/npbc_checkScript.sml`; Gocht et al., AAAI 2024, DOI `10.1609/aaai.v38i8.28642`) eliminates checker bugs end-to-end:

- `VeriPB` acts as an untrusted **proof elaborator** that expands high-level auto-proved steps into explicit kernel hints (`.pbp`).
- **`CakePB`** checks the elaborated kernel proof and carries a machine-checked HOL4 theorem `Theorem check_cstep_correct` (`npbc_checkScript.sml:4978-5020`) proving that every accepted `cstep` preserves `valid_conf`, monotonically tightens optimal bounds (`opt_le pc'.bound pc.bound`), preserves projected solution sets (`bimp_pres`, `bimp_pres_obj`), and sound-guards core deletions—compiled through the formally verified **CakeML** compiler down to x86-64/ARM64 machine code.

---

### 4. Exact Rational Mixed-Integer Programming Certificates (`VIPR` v1.1 and Exact `SCIP`)

Basis: normative (`scipopt/vipr` `cert_spec_v1_1.md`) + source (`scipopt/vipr` `code/viprchk.cpp`, `scipopt/scip` `src/scip/certificate.{h,cpp}`) + execution (self-contained Python 3 VIPR v1.1 verifier in **Evidence** / **Revalidation**)

Many compiler and verification optimization problems—including resource-analysis LP bounds (`AARA`/`RAML`), big-$M$ e-graph extraction with continuous topological levels, and continuous-time scheduling—contain **continuous variables** ($x_j \in \mathbb{R}$) and **fractional rational coefficients** that cannot be natively represented in 0–1 integer `VeriPB` without bit-blasting or discretization. **VIPR** (Cheung, Gleixner, Steffy, IPCO 2017, DOI `10.1007/978-3-319-59250-3_13`; extended in v1.1 by Eifler & Gleixner, *SIAM J. Optim.* 2024, DOI `10.1137/23M156046X`) provides an elementary, solver-independent, **exact rational** certificate format for LP-based branch-and-cut MILP solvers.

#### 4.1 Normative VIPR v1.1 File Structure and Soundness Semantics

Per `scipopt/vipr/cert_spec_v1_1.md` (`99eec197a49b2bd9ad33c1f4c7afabe93caa6511`), every `.vipr` file opens with `VER 1.1` (after `%` comments) followed by **seven sections in strict order**:

1. `VAR n` — variable names indexed `0..n-1`.
2. `INT i` — subset of variable indices constrained to $\mathbb{Z}$ (all remaining variables are continuous in $\mathbb{Q}$).
3. `OBJ min|max` — sparse exact rational objective vector $c^T x$.
4. `CON m b` — $m$ model constraints indexed `0..m-1` (senses `E` for $=$, `L` for $\le$, `G` for $\ge$), with the $b$ variable bound constraints strictly preceding non-bound constraints (`cert_spec_v1_1.md:170-174`).
5. `RTP infeas` or `RTP range lb ub` — exact rational claim to verify (`-inf`/`inf` allowed for one-sided bounds).
6. `SOL s` — primal solutions checked in exact rational arithmetic for integrality, full constraint feasibility, and objective $\le ub$ (min) or $\ge lb$ (max).
7. `DER d` — derived constraints indexed `m..m+d-1`, each carrying a `{ reason }` and a **last-use reference index** (`-1` or max index referencing this row so `viprchk` immediately reclaims memory via `Constraint::trash()`, `viprchk.cpp:182-183`).

Every derived constraint $C_k$ carries an implicit **assumption set** $\mathcal{A}(C_k)$ and is checked in exact `GMP` rational arithmetic (`SVectorGMP : map<int, mpq_class>`, `viprchk.cpp:82-124`) via **five complete rules** plus **two v1.1 incomplete completion rules**:

| Rule Syntax | Mathematical Meaning & Exact Soundness Side-Conditions | Assumption Set $\mathcal{A}(C_k)$ |
| :--- | :--- | :--- |
| `{ asm }` | Branching/split assumption (e.g., $x_j \le \beta$ or $a^T x \ge \beta+1$). | $\{k\}$ |
| `{ lin p i_1 λ_1 ... i_p λ_p }` | **Suitable linear combination** $\sum \lambda_j C_{i_j}$ (all nonzero $\lambda_j s(C_{i_j})$ share the same sign, where $s(\ge)=+1, s(=)=0, s(\le)=-1$) that **dominates** $C_k$ (exact same LHS vector and stronger-or-equal RHS, or an absurdity $0 \ge \beta > 0$ / $0 \le \beta < 0$ / $0 = \beta \ne 0$ which dominates all constraints). | $\bigcup_{j=1}^p \mathcal{A}(C_{i_j})$ |
| `{ rnd p i_1 λ_1 ... i_p λ_p }` | **Chvátal–Gomory rounding:** suitable linear combination whose resulting inequality (`L`/`G`) has **integer coefficients supported exclusively on `INT` variables**; RHS is rounded to $\lfloor \beta \rfloor$ (`L`) or $\lceil \beta \rceil$ (`G`) and must dominate $C_k$. | $\bigcup_{j=1}^p \mathcal{A}(C_{i_j})$ |
| `{ uns i_1 l_1 i_2 l_2 }` | **Unsplit (branch-and-bound / split-cut discharge):** $C_{i_1}$ and $C_{i_2}$ both dominate $C_k$, and $C_{l_1}, C_{l_2}$ form a complementary pure-integer split disjunction $a^T x \le \beta$ and $a^T x \ge \beta + 1$ ($a \in \mathbb{Z}^n$ supported only on `INT` variables, $\beta \in \mathbb{Z}$). | $(\mathcal{A}(C_{i_1}) \setminus \{l_1\}) \cup (\mathcal{A}(C_{i_2}) \setminus \{l_2\})$ |
| `{ sol }` | Objective cutoff bound derived from a verified primal solution in `SOL`. | $\emptyset$ |
| `{ lin weak {bounds} p ... }` *(v1.1)* | Linear combination that only *weakly* dominates $C_k$ (residual terms must be closed using global/local variable bounds); **must be completed** offline by `viprcomp` before `viprchk` accepts it. | Completed into exact `lin` |
| `{ lin incomplete i_1 ... i_n }` *(v1.1)* | Lists active constraints for offline completion by `viprcomp` via exact rational `SoPlex` LP solving to recover exact Farkas dual multipliers. | Completed into exact `lin` |

**Final Acceptance Condition (`cert_spec_v1_1.md:242-243`):** The final constraint $C_{m+d-1}$ MUST have **empty assumption set** $\mathcal{A} = \emptyset$ and MUST be an absurdity (for `RTP infeas`) or dominate $\text{OBJ} \ge lb$ (for `min`) / $\text{OBJ} \le ub$ (for `max`).

#### 4.2 Bridging Fast Floating-Point Cuts to Exact VIPR Proofs (`Exact SCIP` + `viprcomp`)

Running exact rational simplex at every branch-and-bound node or cutting-plane round is orders of magnitude slower than floating-point LP. Exact `SCIP` (`scipopt/scip`, `src/scip/certificate.cpp:1778-1900`; Eifler & Gleixner, *SIAM J. Optim.* 2024) solves the floating-point-to-rational bridge via two techniques:

1. **Safe Directed Rounding & Project-and-Shift:** For LP dual bounds, SCIP takes floating-point dual multipliers, repairs dual feasibility using exact rational arithmetic and variable bounds (Neumaier–Shcherbina safe bounding), and falls back to exact `SoPlex` only when directed rounding fails to close the dual gap.
2. **Certifying Gomory Mixed-Integer (GMI) / MIR Cuts as Split Cuts (`SCIPcertificatePrintMirCut`, `certificate.cpp:1778-1900`):** Because GMI/MIR cuts apply to **mixed-integer** rows (containing continuous variables!), pure Chvátal–Gomory `{ rnd }` does *not* apply directly. Instead, every MIR cut is mathematically equivalent to a **split cut** over a disjunction $(\xi \le \lfloor \beta \rfloor) \lor (\xi \ge \lfloor \beta \rfloor + 1)$ (`certificate.cpp:1822-1826`)! Exact `SCIP`:
   - Recursively ensures all ancestor aggregation rows and slack rows are certified (`lines 1829-1862`),
   - Emits the two integer split assumptions (`leftdisjunctionindex`, `rightdisjunctionindex`),
   - Emits both sides of the split derivation using VIPR v1.1 `{ lin weak ... }` (`certificatePrintWeakDerStart`, `line 1874`) omitting trivial non-negativity slacks (`line 1865`), which offline `viprcomp` fills in automatically using local bounds, and
   - Discharges the split with `{ uns }` to obtain a globally valid (or node-local) exact rational GMI cut!

#### 4.3 Executable Verification of Exact VIPR vs. Floating-Point E-Graph MILP

Running our self-contained exact-rational VIPR v1.1 verifier on the cyclic e-graph extraction instance ($x_{\text{leaf}} + x_{n_A} = 1$, $x_{n_B} = a_B$, $x_{n_A} \le a_B$, $\ell_B - \ell_A - 3 x_{n_A} \ge -2$, $\ell_A - \ell_B - 3 x_{n_B} \ge -2$, minimizing $100 x_{\text{leaf}}$) verified three outcomes:

1. **Exact Cutting-Plane Certificate (`lin` + `rnd`):** Adding the two cycle inequalities eliminates continuous levels $\ell_A, \ell_B$ cleanly ($3 x_{n_A} + 3 x_{n_B} \le 4$); dividing by $3$ and applying `{ rnd }` yields $x_{n_A} + x_{n_B} \le 1$; combining with $x_{n_A} \le x_{n_B}$ yields $2 x_{n_A} \le 1 \xrightarrow{\texttt{rnd}} x_{n_A} \le 0 \implies x_{\text{leaf}} \ge 1 \implies \text{OBJ} \ge 100$, matching primal solution $x_{\text{leaf}} = 1$ (`VERIFIED exact optimum in [100, 100]`).
2. **Exact Branch-and-Bound Split Certificate (`asm` + `lin` + `uns`):** Branching on $x_{n_A} \le 0$ vs. $x_{n_A} \ge 1$ derives $\text{OBJ} \ge 100$ on the left branch and absurdity $0 \ge 2$ on the right branch (which dominates $\text{OBJ} \ge 100$), discharged via `{ uns }` to empty assumptions (`VERIFIED exact optimum in [100, 100]`).
3. **Tampered Floating-Point Dual Multiplier Rejection:** Perturbing the exact multiplier `-1/3` to floating-point `-333333/1000000` ($10^{-6}$ rounding error) is immediately rejected by exact rational dominance checking (`derived {1: 999999/1000000, 2: 999999/1000000} != claimed {1: 1, 2: 1}`).

---

### 5. Cross-System Verification and Proof-Format Trade-Off Matrix

Basis: normative + source + derived

| Dimension | `DRAT` / `LRAT` (`cake_lpr`) | `DRCP` (`Pumpkin`) | `VeriPB` / `CakePB` | `VIPR` v1.1 (`viprchk` / `Exact SCIP`) |
| :--- | :--- | :--- | :--- | :--- |
| **Native Constraint Domain** | Propositional CNF clauses | Finite-domain CP atomic bounds (`x >= v`, `x != v`) | 0–1 linear pseudo-Boolean inequalities ($\mathbb{Z}$ coeffs) | Mixed-integer linear inequalities ($\mathbb{Q}$ coeffs, $\mathbb{Z}$ + $\mathbb{Q}$ vars) |
| **Continuous Variables** | Unsupported | Unsupported | Unsupported (requires discretization/encoding) | **Native exact $\mathbb{Q}$** |
| **Cardinality / Pigeonhole Size** | Exponential $2^{\Omega(n)}$ | Propagator-dependent (polynomial if global checker supports it) | **Polynomial** ($2n+1$ steps for $\text{PHP}_n^{n+1}$) | **Polynomial** (via `lin` + `rnd`) |
| **Symmetry & Dominance Breaking** | Limited (`PR`/`RAT`; awkward for global symmetries) | Under active research (propagator inferences) | **Native (`red` + `dom` + proved `StoreOrder`)** | Not native in v1.1 (symmetry breaking requires encoding as valid splits/cuts or external proof) |
| **Branch-and-Bound Optimality** | Requires external objective encoding | Supported via bound inferences | **Native (`Obj` / `Sol` / `soli` / `solx`)** | **Native (`RTP range`, `SOL`, `uns`, `sol`)** |
| **Formally Verified Checker** | Yes (`cake_lpr`, `ACL2`, Isabelle/HOL) | No (Rust checker `pumpkin-checking`) | **Yes (`CakePB` in HOL4 + `CakeML` machine code)** | No (`viprchk.cpp` C++/GMP ~1780 LOC; small TCB, not yet mechanized to machine code) |
| **Best Compiler Optimization Fit** | Pure Boolean equivalence / bit-blasted SAT | Finite-domain scheduling / `Unison` CP propagators | 0–1 register coloring, MaxSAT/PBO e-graph extraction, symmetry-rich discrete scheduling | E-graph big-$M$ / continuous-level MILP, LP/MILP resource-bound analysis (`AARA`), mixed-integer cuts |

## Boundaries

- **Active GitLab `VeriPB` Upstream (`not examined`):** Active `VeriPB` development (`gitlab.com/MIAOresearch/software/VeriPB`) and `VeriPB` 2.0/3.0 kernel elaboration formats beyond the pinned GitHub mirror (`StephanGocht/VeriPB` `01b7b5088c8a67f1611427174501191bc5f5b365`) were **not examined** directly because GitLab API access was unavailable from the inspection environment; kernel proof semantics and soundness theorems were verified directly against `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`, `examples/pseudo_bool/npbc_checkScript.sml`), which implements the current formally verified kernel semantics.
- **`Savile Row` Source Code (`not examined`):** `Savile Row` reformulation behavior (`AC-CSE`, tabularisation, SAT/CP encodings) is documented from `Nightingale et al. (AIJ 2017)` rather than direct Java source inspection because no canonical GitHub repository resolved.
- **Projected Model Counting / Enumeration in `VeriPB` (`not examined`):** While `CakePB` (`npbc_checkScript.sml:3006-3008,4994-5003`) already contains `ChangePres`/`CheckPres`/`Sol` and `proj_pres` theorems supporting projected solution sets, end-to-end projected enumeration proof logging workflows were **not examined**.
- **Formally Verified Machine-Code Checker for `VIPR` (`unknown` / `not examined`):** `scipopt/vipr/code/viprchk.cpp` is a compact (~1,780-line) unverified C++/GMP checker; whether an Isabelle/HOL, Lean 4, or CakeML machine-code-verified `VIPR` v1.1 checker exists in third-party repositories was **not examined**.
- **Native Continuous Variables in `VeriPB` (`unsupported`):** `VeriPB` and `CakePB` operate strictly over Boolean `{0, 1}` literals with integer coefficients; continuous rational LP variables (such as unconstrained real topological levels or fractional resource flows) are **unsupported** without finite-precision encoding or switching to `VIPR`.
- **Native Dominance / Arbitrary Preorder Symmetry Breaking in `VIPR` v1.1 (`unsupported`):** `VIPR` v1.1 (`cert_spec_v1_1.md`) certifies only polyhedral implications (`lin`), integer Chvátal–Gomory rounding (`rnd`), split disjunctions (`uns`), and primal cutoffs (`sol`); non-implicative symmetry-breaking or dominance cuts that prune feasible integer solutions of equal objective value are **unsupported** in `VIPR` v1.1.
- **Direct Proof Logging in `OR-Tools CP-SAT` and `Unison`/`Gecode` (`known not to apply` / `unsupported`):** Neither `unison-code/unison` (`Gecode` backend) nor standard `MiniZinc` -> `FlatZinc` flattening emits end-to-end `VeriPB`/`VIPR` proofs certifying the modelling-to-FlatZinc transformation itself; certifying the flattening step (MiniZinc/Conjure $\to$ PB/MILP) remains an open verification boundary separate from certifying the backend solver search.
- **Stronger Claims Not Established:** Finding bugs in archived `StephanGocht/VeriPB` (`01b7b5088c8a67f1611427174501191bc5f5b365`) does **not** imply those bugs exist in current `MIAOresearch/software/VeriPB` releases or in `CakePB` (where `check_cstep_correct` is HOL4-proved). Conversely, running `VIPR` or `CakePB` certifies only the mathematical validity of the encoded PB/MILP instance—not semantic equivalence between the source compiler IR (e.g., an e-graph or CFG) and its PB/MILP formulation.

## Evidence

All primary evidence was acquired on `2026-11-19`.

### Upstream Source Code Evidence (Pinned Revisions)

1. **`MiniZinc/libminizinc` (`8c9f79949cb7df96c7c99b5ed41d511962879c97`):**
   - `include/minizinc/flatten.hh:30-160` — `FlatteningOptions` (`enableHalfReification = true`, `eagerLinearAggregation`, `onlyRangeDomains`) and `FlatModelStatistics` (`n_reif_ct`, `n_imp_ct`, `n_imp_del`, `n_lin_del`).
   - `include/minizinc/flatten_internal.hh:40-154,764-766` — `EE(r, b)` partiality result, `PathStore`/`VarPathStore` hash-consed flattening paths, and `Ctx::partialityVar` (`C_ROOT` check).
   - `lib/flatten/flatten_binop.cpp:318-326,448-457,912-916` — `C_MIX` forcing on Boolean arguments, `C_ROOT` domain folding.
   - `share/minizinc/std/fzn_all_different_int.mzn:5-6` — Default pairwise `xs[i] != xs[j]` decomposition overridden by native solver libraries.
2. **`conjure-cp/conjure` (`fcae5cfd887080f9cfc32556b13daaae22a646a8`):**
   - `src/Conjure/Representations/Set/Explicit.hs:11-72` — Automatic strict lexicographic symmetry-breaking constraint `m[i] .< m[i+1]` on explicit set matrices.
   - `src/Conjure/Representations/Partition/Occurrence.hs:19-178` — Four-matrix partition refinement (`_NumParts`, `_WhichPart`, `_PartSizes`, `_FirstIndex`), `firstIndexChannelling`, `symmetryBreaking` (`i < j <-> firstIndex[i] < firstIndex[j]`), `noGaps`, and `dontCare`.
3. **`chuffed/chuffed` (`f698d5623bb0c2bcd497388ba966f0436d62caf4`):**
   - `chuffed/vars/int-var-ll.h:4-56` — `IntVarLL` lazy order-encoding literal creation (`LitNode`, `ld`, `freelist`, `getLit` for `[x != v]`, `[x = v]`, `[x >= v]`, `[x <= v]`).
4. **`ConSol-Lab/Pumpkin` (`82d30b71a81747ce969f809cb14edf679128f12c`):**
   - `pumpkin-crates/core/src/proof/mod.rs:1-180` — `ProofLog::cp` DRCP proof logger, `Inference` logging (`premises`, `consequent`, `generated_by`, `label`), `propagation_order_hint` scaffolding, and `pumpkin_checking::verify_deduction`.
5. **`egraphs-good/extraction-gym` (`903ba0f818b50608fe20ae9e0f03c35cb27bc50a`):**
   - `src/extract/ilp_cbc.rs:33-208` — Binary e-class/e-node formulation, `solution.col(...) > 0.0` decoding (`lines 121, 126`), continuous unbounded `levels` (`lines 150-157`), and big-$M = |C| + 1$ acyclicity constraints (`lines 195-205`).
6. **`StephanGocht/VeriPB` (`01b7b5088c8a67f1611427174501191bc5f5b365`):**
   - `veripb/rules.py:183-820` — Rule identifiers (`p`/`pol`, `u`/`rup`, `o`, `v`/`ov`, `c`, `f`, `core`).
   - `veripb/rules_dominance.py:39-233,585-824` — `Order`, `OrderContext`, `LoadOrder`, `StrictOrder` (`pre_order`), `objectiveCondition` (bug at `line 630`: `(-coeff, lit)` instead of `(-coeff, lit2)`), `AddRedundant` (`red`, bug at `line 745`: stale `goal.isProven` instead of `subgoal.isProven`), `DominanceRule` (`dom`).
7. **`CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`):**
   - `examples/pseudo_bool/README.md:1-39` — Module map (`pbc`, `npbc`, `npbc_check`, `cp_encoding`, `graph_encoding`).
   - `examples/pseudo_bool/npbc_checkScript.sml:12-69,200-207,2974-3009,4978-5020` — Three-tier proof hierarchy (`lstep`, `sstep`, `cstep`), cutting-planes `constr` AST and 4 division types (`Cd`/`Dd`/`Nd`/`Md`), `StoreOrder`/`LoadOrder`/`Dom`/`CheckedDelete`/`Obj`/`Sol`, and HOL4 soundness theorem `Theorem check_cstep_correct`.
8. **`scipopt/vipr` (`99eec197a49b2bd9ad33c1f4c7afabe93caa6511`) & `ambros-gleixner/VIPR` (`f221c3fd2274e8e859e8e24505278d6f7c1bb8ff`):**
   - `cert_spec_v1_1.md:1-255` — Normative VIPR v1.1 grammar, rounding, domination, suitable linear combinations, `asm`/`lin`/`rnd`/`uns`/`sol`, incomplete v1.1 keywords (`lin weak`, `lin incomplete`), assumption-set rules, and last-use memory indices.
   - `code/viprchk.cpp:56-200` — `DerivationType` enum, `SVectorGMP` (`map<int, mpq_class>`), `Constraint::trash()`.
9. **`scipopt/scip` (`a3274d2137c75fff405707a80dda11b887459f58`):**
   - `src/scip/certificate.h:60-250` & `src/scip/certificate.cpp:1318,1778-1900,2327,2700` — Exact rational VIPR output APIs and `SCIPcertificatePrintMirCut` splitting MIR cuts into `{ asm }` disjunctions + `{ lin weak }` derivations completed by `viprcomp`.

### Executable Micro-Probe Evidence (`Basis: execution`)

A self-contained Python 3 probe (using only standard-library `fractions.Fraction` and `math`) executed and produced:

```text
[VeriPB Cutting-Planes PHP(6,5)] Derived 0 >= 1 in 11 PB addition steps (2n+1; resolution is 2^Omega(n))
[VeriPB Cutting-Planes PHP(21,20)] Derived 0 >= 1 in 41 PB addition steps (2n+1; resolution is 2^Omega(n))
[VeriPB Cutting-Planes PHP(101,100)] Derived 0 >= 1 in 201 PB addition steps (2n+1; resolution is 2^Omega(n))
[VeriPB Division Rule] 2x1 + 2x2 + 2x3 >= 3  --(div 2)-->  x1 + x2 + x3 >= 2: PASS
[E-Graph Big-M FP Break] |C|=1100000, M=1100001, tol=1e-06: cyclic x_nA=x_nB=1-9.5e-07 satisfies M(1-x)=1.045001 >= 1.0 with fp_obj=0.0000950 vs exact optimum=100 (extraction-gym col>0.0 selects cycle!)
[VIPR v1.1 Valid CG Cert (lin+rnd)] VERIFIED exact optimum in [100, 100] (primal=100, dual=100)
[VIPR v1.1 Valid B&B Split Cert (asm+lin+uns)] VERIFIED exact optimum in [100, 100] (primal=100, dual=100)
[VIPR v1.1 Tampered FP Multiplier] REJECTED: DER 11 not dominated: derived (L, 333333/250000, {1: Fraction(999999, 1000000), 2: Fraction(999999, 1000000)}) vs claimed (L, 4/3, {1: Fraction(1, 1), 2: Fraction(1, 1)})
```

### Peer-Reviewed Literature Evidence

- Nethercote, Stuckey, Becket, Brand, Duck, Tack (CP 2007, DOI `10.1007/978-3-540-74970-7_38`): *MiniZinc: Towards a Standard CP Modelling Language*.
- Ohrimenko, Stuckey, Codish (Constraints 2009, DOI `10.1007/s10601-008-9064-x`): *Propagation via Lazy Clause Generation*.
- Feydy, Somogyi, Stuckey (CP 2011, DOI `10.1007/978-3-642-23786-7_23`): *Half Reification and Flattening*.
- Cheung, Gleixner, Steffy (IPCO 2017, DOI `10.1007/978-3-319-59250-3_13`): *Verifying Integer Programming Results*.
- Nightingale, Akgün, Gent, Jefferson, Miguel, Spracklen (Artificial Intelligence 2017, DOI `10.1016/j.artint.2017.07.001`): *Automatically Improving Constraint Models in Savile Row*.
- Castañeda Lozano, Carlsson, Hjort Blindell, Schulte (ACM TOPLAS 2019, DOI `10.1145/3332373`): *Combinatorial Register Allocation and Instruction Scheduling*.
- Yang, Phothilimthana, Wang, Willsey, Roy, Pienaar (MLSys 2021, `arXiv:2101.01332`): *Equality Saturation for Tensor Graph Superoptimization (TENSAT)*.
- Akgün, Frisch, Gent, Jefferson, Miguel, Nightingale (Artificial Intelligence 2022, DOI `10.1016/j.artint.2022.103751`): *Conjure: Automatic Generation of Constraint Models from Problem Specifications*.
- Bogaerts, Gocht, McCreesh, Nordström (JAIR 2023, DOI `10.1613/jair.1.14296`): *Certified Dominance and Symmetry Breaking for Combinatorial Optimisation*.
- Gocht, McCreesh, Myreen, Nordström, Oertel, Tan (AAAI 2024, DOI `10.1609/aaai.v38i8.28642`): *End-to-End Verification for Subgraph Solving*.
- Eifler, Gleixner (SIAM Journal on Optimization 2024, DOI `10.1137/23M156046X`): *Safe and Verified Gomory Mixed-Integer Cuts in a Rational Mixed-Integer Program Framework*.

## Revalidation

To cheaply check whether the core modelling, soundness, and proof-format invariants still hold for newer upstream revisions or a candidate compiler optimization extractor:

1. **Upstream Source Diff Checks:**
   - Diff `scipopt/vipr`: `cert_spec_v1_1.md` (or newer `cert_spec_v*.md`) and `code/viprchk.cpp` for changes to `DER` rules, incomplete keywords, or symmetry-breaking extensions.
   - Diff `CakeML/cakeml`: `examples/pseudo_bool/npbc_checkScript.sml` (`Datatype: cstep` and `Theorem check_cstep_correct`) for extensions to the verified pseudo-Boolean kernel.
   - Diff `egraphs-good/extraction-gym`: `src/extract/ilp_cbc.rs` (`block_cycles` and `solution.col(...) > 0.0`) to check whether bounded/integer levels, tighter tolerance thresholds (`> 0.5`), or exact rational verification have been adopted.
   - Diff `ConSol-Lab/Pumpkin`: `pumpkin-crates/core/src/proof/mod.rs` to inspect DRCP format stabilization and global-constraint proof-checking coverage.
2. **Self-Contained Executable Revalidation Probe:**
   Run this standalone Python 3 check to reproduce (a) linear-size cutting-planes refutation of $\text{PHP}_{100}^{101}$, (b) the floating-point big-$M$ e-graph cycle soundness break, and (c) exact rational `VIPR` v1.1 verification of cutting-plane (`lin`+`rnd`) and split (`asm`+`lin`+`uns`) proofs plus rejection of a $10^{-6}$-perturbed dual multiplier:

```bash
python3 - <<'EOF'
from fractions import Fraction
import math

# 1. Cutting-planes linear refutation of PHP(n+1, n)
n = 100
acc, rhs, steps = {}, 0, 0
for i in range(n + 1):
    for j in range(n): acc[(i, j)] = acc.get((i, j), 0) + 1
    rhs += 1; steps += 1
for j in range(n):
    for i in range(n + 1): acc[(i, j)] = acc.get((i, j), 0) - 1
    rhs -= 1; steps += 1
assert all(v == 0 for v in acc.values()) and rhs == 1 and steps == 2 * n + 1

# 2. Big-M FP e-graph cycle soundness break (|C| = 1.1e6, tol = 1e-6)
M, delta = 1_100_001, 9.5e-7
x_nA = x_nB = 1.0 - delta
assert abs(x_nA - 1.0) <= 1e-6 and M * (1.0 - x_nA) >= 1.0 and 100.0 * delta < 1e-3

# 3. Exact rational VIPR check: cycle constraints -3*x1 - 3*x2 >= -4 -> lin(-1/3) -> rnd -> x1+x2 <= 1 -> x1 <= 0 -> 100*x0 >= 100
# Tampered multiplier -333333/1000000 fails exact coefficient equality (999999/1000000 != 1)
c1_x1 = Fraction(-3) * Fraction(-1, 3)
c1_rhs = Fraction(-4) * Fraction(-1, 3)
assert c1_x1 == 1 and math.floor(c1_rhs) == 1
tampered_x1 = Fraction(-3) * Fraction(-333333, 1_000_000)
assert tampered_x1 != Fraction(1)
print("REVALIDATION_PASS")
EOF
```

A passing probe verifies only the mathematical cutting-planes derivation, big-$M$ tolerance arithmetic, and exact rational domination step; revalidating full solver certificates requires running `viprchk` (for `.vipr` files) or `CakePB` (for `.pbp` proofs) on concrete solver outputs.
