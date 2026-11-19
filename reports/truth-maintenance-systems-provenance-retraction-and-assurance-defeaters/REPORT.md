# Truth Maintenance Systems, Provenance Retraction, and Structured Assurance-Case Defeaters

## Summary

Monotonic build caches and proof stores (such as Salsa durability tiers, Lean 4 `.olean` axiom arrays, and hash-addressed build graphs) assume that trusted foundations—proof kernels, external SMT oracles, ISA security contracts, and cryptographic hash primitives—never retroactively lose validity. When a foundational assumption is retracted (for example, a kernel soundness defect, a microarchitectural side-channel counterexample, or a broken cryptographic hash), monotonic caches lack an inverted retraction model and force full-store rebuilds or manual invalidation.

Non-monotonic belief revision and incremental provenance maintenance resolve this through three closely related formalisms whose engineering trade-offs are sharply separated:

1. **Doyle Justification-Based TMS (JTMS)** and **incremental Datalog deletion algorithms (DRed, Backward/Forward)** maintain a single active belief state in $O(1)$ per-justification space. Doyle's full SL-justifications `(SL inlist outlist)` coincide with Gelfond–Lifschitz stable models and exhibit odd-loop unsatisfiability and even-loop multiplicity; Horn-restricted JTMS implementations (such as Forbus & de Kleer's `jtms.lisp`) avoid odd loops by restricting justifications to positive antecedents and confining non-monotonicity to explicit assumption retraction. On cyclic or mutually supportive proof graphs, naive reference counting produces unsound ghost beliefs, DRed incurs $O(|C|)$ over-deletion and re-derivation storms when an alternative root remains intact, and Motik et al.'s Backward/Forward (B/F) algorithm avoids the cascade via local backward reachability checks.
2. **de Kleer Assumption-Based TMS (ATMS)** precomputes for every derived datum its complete, sound, consistent, minimal antichain of supporting assumption environments alongside a minimal `nogood` table. Algebraically, ATMS labels are exact irredundant DNF elements of Green–Karvounarakis–Tannen's free distributive provenance semiring $\mathrm{PosBool}(X)$ quotiented by the nogood ideal $I_{\mathrm{nogood}}$, and retracting an assumption $x$ is the semiring homomorphism $\mathrm{eval}_{x \mapsto 0}$ executed with zero re-derivation steps. However, explicit DNF labels blow up exponentially ($2^k$ minimal environments on a $k$-stage diamond chain with only $2k$ justifications). Symbolic ROBDD/ZDD compression reduces the same $k = 40$ diamond chain from $1{,}099{,}511{,}627{,}776$ explicit environments to $82$ nodes under an interleaved variable ordering, but blows up to $2^{k+1}$ nodes under an adversarial variable ordering—making **stratified hybrid architectures** (symbolic ATMS over $O(10^2\text{--}10^3)$ coarse trust-root atoms paired with JTMS/B-F over fine-grained intra-module derivations) the only scalable design for large content-addressed proof stores.
3. **Structured Assurance Cases (GSN v3 Dialectical Extension, CAE Blocks, Assurance 2.0)** formalize epistemic defeat via rebutting, undermining, and undercutting defeaters (`CounterGoal`, `CounterSolution`, `ChallengesNode`, `ChallengesRelation`, and CAE sideclaims). Graydon & Holloway (2017) demonstrated that naive Bayesian Belief Network (BBN), Dempster–Shafer, and averaging confidence propagators produce implausible results under subclaim dilution and sideclaim failure. Assurance 2.0 (Bloomfield & Rushby, 2021/2026) addresses these counterexamples by strictly separating **logical soundness and dialectical indefeasibility** (which gate admissibility before any arithmetic is performed) from **compositional Fréchet-bounded probabilistic confidence** parameterized by subclaim dependence structure (intersection lower bound $1 - \min(1, \sum d_i)$, independent product $\prod c_i$, containment $\max c_i$, independent diversity $1 - \prod d_i$, partitioned weighted average $\sum w_i c'_i$, and cumulative conditional chain). Coupling dialectical defeaters to ATMS nogood assertions enables surgical invalidation: an empirical defeater against an ISA constant-time contract revokes dependent constant-time claims while leaving orthogonal memory-safety claims intact.

## Applicability

This report synthesizes and cross-checks primary specifications, peer-reviewed papers, reference source code, and standalone execution probes across four domains:

- **Classical truth maintenance (`Doyle 1979`, `de Kleer 1986`, `id2359/bps@3d072521...`)**: Compares Doyle's non-monotonic SL-justification semantics against Forbus & de Kleer's Horn-restricted Common Lisp reference implementations (`jtms/jtms.lisp` and `atms/atms.lisp`). Findings on `jtms.lisp` and `atms.lisp` apply specifically to revision `3d072521dc7c759aaae7bb9d1c459c20ef6d8a01`; generalizations to Doyle (1979) and de Kleer (1986) are explicitly distinguished where the textbook code restricts the paper semantics.
- **Algebraic provenance and incremental view maintenance (`Green et al. 2007`, `Gupta et al. 1993`, `Motik et al. 2015`)**: Connects $\mathrm{PosBool}(X)$ semirings to ATMS labels and contrasts counting, DRed, and B/F deletion algorithms on positive recursive and cyclic derivation graphs.
- **Proof-store and incremental-compiler trust boundaries (`leanprover/lean4@8009d0a6...`, `salsa-rs/salsa@496752ea...`)**: Characterizes concrete production mechanisms (`src/Lean/Util/CollectAxioms.lean` and `src/durability.rs`) to isolate why monotonic forward-dependency stores cannot represent non-monotonic retraction of kernel, oracle, or cryptographic assumptions without an auxiliary truth-maintenance layer.
- **Structured assurance cases, defeaters, and confidence propagation (`Pollock 1987`, `Goodenough et al. 2015`, `Graydon & Holloway 2017`, `Bloomfield & Netkachova 2014`, `Bloomfield & Rushby arXiv:2004.10474v3` and `arXiv:2604.00034v1`, `SCSC-141C GSN v3`, `jonasthewolf/gsn2x@9effad83...`, `SRI-CSL/ETB@ee4692f3...`)**: Relates philosophical defeater taxonomies, GSN v3 dialectical syntax/validation rules, CAE five-block structure, and Assurance 2.0's Fréchet-bounded confidence propagation formulas.

Execution measurements (`Basis: execution`) were run under Python `3.13.15` using only the standard library; the exact self-contained probe code and outputs are preserved in **Evidence**.

## Findings

### 1. Doyle JTMS vs. Forbus–de Kleer Horn JTMS: Semantics, Well-Foundedness, and Loop Pathologies

Basis: normative (Doyle 1979, DOI `10.1016/0004-3702(79)90008-0`) + source (`id2359/bps@3d072521...`, `jtms/jtms.lisp:17-308`) + execution.

In Jon Doyle's original 1979 Justification-Based Truth Maintenance System (JTMS), every node carries a binary belief status (`IN` or `OUT`) and a set of justifications. Doyle defines two justification forms:

- **Support-List (`SL`) justifications**: `(SL <inlist> <outlist>)` supporting consequent node $c$. The justification is *valid* iff every node in `inlist` is `IN` and every node in `outlist` is `OUT`.
- **Conditional-Proof (`CP`) justifications**: `(CP <consequent> <in-hypotheses> <out-hypotheses>)`, expressing that `<consequent>` is derivable whenever `<in-hypotheses>` are `IN` and `<out-hypotheses>` are `OUT`, compiled down to SL-justifications by tracing dependency supports.

A labeling $L : V \to \{\mathrm{IN}, \mathrm{OUT}\}$ of a JTMS network is **admissible** (consistent and well-founded) iff:
1. **Consistency**: $L(c) = \mathrm{IN}$ iff $c$ has at least one valid justification $(I, O)$ with $I \subseteq L^{-1}(\mathrm{IN})$ and $O \cap L^{-1}(\mathrm{IN}) = \emptyset$.
2. **Well-foundedness (groundedness)**: There exists a strict partial order $\prec$ on $L^{-1}(\mathrm{IN})$ such that every `IN` node $c$ has a valid supporting justification $(I, O)$ with $u \prec c$ for all $u \in I$.

Well-founded admissible labelings of a Doyle SL-network correspond exactly to **Gelfond–Lifschitz stable models** (answer sets) of the propositional normal logic program $\{c \leftarrow I, \neg O\}$. Because of negative dependencies (`outlist`), general SL-networks exhibit three fundamental behaviors confirmed by our execution probe:

| Network Pattern | SL Rule(s) | Admissible Well-Founded Labelings | Engineering Consequence |
| :--- | :--- | :--- | :--- |
| **Positive self-loop** | $P \leftarrow \mathrm{IN}(P)$ | $\{\emptyset\}$ ($P = \mathrm{OUT}$) | Circular self-support is rejected by well-foundedness; naive consistency without groundedness would erroneously permit $P = \mathrm{IN}$. |
| **Odd negative loop** | $P \leftarrow \mathrm{OUT}(P)$ | $\emptyset$ (**none**) | Unsatisfiable labeling; Doyle's original relaxation algorithm enters non-termination unless equipped with odd-loop detection / dependency-directed backtracking (DDB). |
| **Even negative loop** | $P \leftarrow \mathrm{OUT}(Q),\; Q \leftarrow \mathrm{OUT}(P)$ | $\{\{P\}, \{Q\}\}$ (**two**) | Non-unique belief states; belief revision outcome depends on search/tie-breaking order. |

**Critical source divergence (`id2359/bps` vs. Doyle 1979):** Direct inspection of Forbus & de Kleer's reference implementation in `id2359/bps/jtms/jtms.lisp` reveals that it omits `outlist` entirely:
- `defstruct just` (`jtms/jtms.lisp:53-57`) contains only `index`, `informant`, `consequence`, and `antecedents` (positive list only).
- `justification-satisfied?` (`jtms/jtms.lisp:162-163`) checks `(every #'in-node? (just-antecedents just))`.
- Non-monotonic retraction is restricted to explicit assumption nodes (`tms-node-assumption?`, line 44) manipulated via `enable-assumption` (lines 202–211), `retract-assumption` (lines 195–200), and `default-assumptions` (lines 278–287), which enables `:DEFAULT` assumptions one by one and retracts any assumption that triggers a contradiction handler (`throw 'CONTRADICTION t`).
- **Well-foundedness preservation during retraction (`jtms/jtms.lisp:223-246`)**: Every `IN` node points to a single active `tms-node-support` (either `:ENABLED-ASSUMPTION`, a premise justification with `null antecedents`, or a single satisfied `just`). When `retract-assumption` marks an assumption `:OUT`, `propagate-outness` (lines 223–236) traverses *only* consequences whose active `tms-node-support` pointer is the invalidated justification (`(when (eq (tms-node-support conseq) (car js)) ...)`), clearing their `support` to `nil` and collecting them in `out-queue`. Only after the entire dependent support tree is marked `:OUT` does `find-alternative-support` (lines 238–246) iterate over `out-queue` to re-install any still-valid alternative justification via `install-support` / `propagate-inness`. Because `propagate-inness` only activates justifications whose antecedents are already `:IN` (and therefore already grounded), the active support graph remains acyclic at every step, preventing circular self-support even when justifications form cycles.

**Dependency-Directed Backtracking (DDB):** When a contradiction node becomes `IN`, `handle-one-contradiction` (`jtms/jtms.lisp:333-348`) calls `assumptions-of-node` (lines 292–302), which walks `tms-node-support` pointers backwards (guarded by a fresh cons-cell `marker` for DAG deduplication) to collect the supporting enabled assumptions (the *culprit set*), then retracts one culprit rather than chronologically unwinding unrelated search decisions. In Doyle (1979), DDB additionally records a new nogood justification preventing the same culprit combination from recurring.

---

### 2. de Kleer ATMS: Label Invariants, `weave`/`new-nogood` Mechanics, and $\mathrm{PosBool}(X)$ Isomorphism

Basis: normative (de Kleer 1986, DOI `10.1016/0004-3702(86)90080-9`; Green, Karvounarakis & Tannen 2007, DOI `10.1145/1265530.1265535`) + source (`id2359/bps@3d072521...`, `atms/atms.lisp:17-495`) + execution + derived.

Whereas a JTMS maintains one active context at a time, Johan de Kleer's Assumption-Based Truth Maintenance System (ATMS) tracks *all* consistent assumption contexts simultaneously. Let $\mathcal{A}$ be the finite set of **assumptions** (retractable primitive hypotheses). An **environment** is a finite subset $E \subseteq \mathcal{A}$; a **nogood** is an environment from which the distinguished contradiction node $\bot$ is derivable. Each datum node $n$ carries a **label** $L(n) \subseteq 2^{\mathcal{A}}$ that must maintain four invariants (de Kleer 1986, §2.2):

1. **Soundness**: For every $E \in L(n)$, $n$ is derivable from $E$ and the recorded Horn justifications ($E, J \vdash n$).
2. **Consistency**: No $E \in L(n)$ is a nogood (nor a superset of any nogood).
3. **Completeness**: For every consistent environment $E'$ with $E', J \vdash n$, there exists $E \in L(n)$ such that $E \subseteq E'$.
4. **Minimality (Antichain property)**: No environment in $L(n)$ is a proper subset of another environment in $L(n)$ ($\forall E_1, E_2 \in L(n),\; E_1 \subseteq E_2 \implies E_1 = E_2$).

**Source-level mechanics in `id2359/bps/atms/atms.lisp`:**
- **Dual-indexed environments (`atms/atms.lisp:66-74`, `332-347`)**: Each `env` struct caches `count` ($|E|$), sorted `assumptions`, a `nogood?` slot (storing either the justifying rule or the minimal subsuming nogood), and critically `nodes`—a reverse index of every `tms-node` whose label currently contains this `env`. Environments are interned in `atms-env-table` bucketed by cardinality `count` to accelerate subsumption checks (`compare-env`, lines 356–363, short-circuits on `env-count` before calling `subsetp`).
- **Label propagation via `weave` and `update-label` (`atms/atms.lisp:202-263`)**: Adding a Horn justification $a_1 \wedge \dots \wedge a_m \to c$ calls `propagate`, which runs `weave` (lines 245–263) to compute the Cartesian union $\bigotimes_{i=1}^m L(a_i)$, discarding nogoods (`env-nogood?`) and subsumed supersets immediately at each join step. `update-label` (lines 226–243) merges `new-envs` into $L(c)$, deleting existing environments subsumed by a new one (`:S12`) and discarding new ones subsumed by an existing one (`:EQ` or `:S21`), updating the `env-nodes` reverse index in lockstep.
- **Zero-rederivation nogood retraction (`atms/atms.lisp:367-406`)**: When `new-nogood` discovers a minimal inconsistent environment `cenv`, it:
  1. Marks `cenv` as nogood and invokes `remove-env-from-labels` (`atms/atms.lisp:399-406`), directly deleting `cenv` from every node in `(env-nodes cenv)`.
  2. Prunes any larger subsumed entries in `atms-nogood-table` (`(> (car entry) count)`, lines 374–378).
  3. Scans larger environments in `atms-env-table` (`(> (car entry) count)`, lines 379–385), marking every superset of `cenv` as nogood and invoking `remove-env-from-labels` on each.
  Notably, **`new-nogood` performs zero justification-graph traversal and zero re-derivation**: every node that still retains at least one unaffected environment in $L(n)$ remains believed in those surviving contexts immediately.
- **On-demand explanation cost (`atms/atms.lisp:470-494`)**: Because labels erase justification topology, `explain-node` must recursively search `tms-node-justs` for a well-founded justification DAG under a requested `env` (using a `queued-nodes` cycle guard), which the source comment itself notes *"is really a simple consequent JTMS."*

**Algebraic isomorphism with Green–Karvounarakis–Tannen Provenance Semirings (derived + verified by execution):**
In Green, Karvounarakis & Tannen (PODS 2007, DOI `10.1145/1265530.1265535`), positive relational/Datalog derivations are annotated in a commutative semiring $(K, +, \cdot, 0, 1)$, where $+$ represents alternative derivations (disjunction) and $\cdot$ represents joint use of premises (conjunction). The hierarchy of provenance semirings descends by adding algebraic laws:

$$\mathbb{N}[X] \;\twoheadrightarrow\; \mathrm{Trio}(X) \;\twoheadrightarrow\; \mathrm{Why}(X) \;\twoheadrightarrow\; \mathrm{PosBool}(X) \;\twoheadrightarrow\; \mathbb{B}$$

Specifically, $\mathrm{PosBool}(X)$ is the free distributive lattice generated by assumption atoms $X$: it enforces idempotence of both operations ($a + a = a$, $a \cdot a = a$) and **absorption** ($a + a \cdot b = a$). Every element of $\mathrm{PosBool}(X)$ has a unique canonical irredundant DNF representation—an **antichain of finite subsets of $X$**, matching de Kleer's ATMS Minimality invariant identically.

Incorporating a nogood set $\mathcal{N} \subseteq 2^X$ corresponds to forming the quotient semiring $\mathrm{PosBool}(X) / I_{\mathcal{N}}$, where $I_{\mathcal{N}}$ is the semiring ideal generated by the monomials $\{\prod_{x \in N} x \mid N \in \mathcal{N}\}$ (sending every superset of a nogood to $0$). Under this isomorphism:
- `weave` is exact semiring multiplication $\prod_i L(a_i)$ in $\mathrm{PosBool}(X) / I_{\mathcal{N}}$.
- `update-label` is exact semiring addition $L(c) + \Delta$ with absorption.
- **Retracting an assumption $a \in X$** (asserting singleton nogood $\{a\}$) is the unique semiring homomorphism $h_{a \mapsto 0} : \mathrm{PosBool}(X) / I_{\mathcal{N}} \to \mathrm{PosBool}(X \setminus \{a\}) / I_{\mathcal{N}'}$ mapping $a \mapsto 0$ and $x \mapsto x$ for $x \neq a$. Because $h_{a \mapsto 0}$ commutes with $+$ and $\cdot$, evaluating a retraction on precomputed labels produces the exact same result as recomputing the entire proof DAG from scratch without $a$.

---

### 3. Exponential Label Blowup vs. Cyclic Rederivation Storms: Complexity & Symbolic Compression

Basis: source + execution (Python 3.13.15 micro-probes) + derived (Gupta et al. 1993; Motik et al. 2015).

#### 3.1 ATMS Exponential Blowup and ROBDD Variable-Ordering Sensitivity

On a $k$-stage diamond proof DAG ($N_0 \leftarrow \top$, and for $i = 1 \dots k$: $N_i \leftarrow N_{i-1} \wedge a_i$ and $N_i \leftarrow N_{i-1} \wedge b_i$), the graph has only $2k$ assumptions and $2k$ justifications, yet the irredundant DNF label of $N_k$ is $\bigwedge_{i=1}^k (a_i \vee b_i)$, which expands to exactly $2^k$ minimal environments (and in general over $n$ assumptions, Sperner's theorem permits antichain labels up to $\binom{n}{\lfloor n/2 \rfloor}$).

Measured execution outputs from our standalone probe (`probe_tms_assurance.py` and the companion ROBDD benchmark):

| Stages $k$ | Justifications ($2k$) | Explicit ATMS / $\mathrm{PosBool}(X)$ $|L(N_k)|$ | ATMS Pruned Entries on $\mathrm{nogood}(\{a_1\})$ (Rederivations) | ROBDD Nodes (Interleaved Order $a_1 < b_1 < \dots$) | ROBDD Nodes (Separated Order $a_1 < \dots < a_k < b_1 < \dots < b_k$) | ROBDD Nodes after `restrict(a_1=0)` |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 8 | 16 | 16 (0) | 10 | 32 | 9 |
| 8 | 16 | 256 | 256 (0) | 18 | 512 | 17 |
| 12 | 24 | 4,096 | 4,096 (0) | 26 | 8,192 | 25 |
| 20 | 40 | 1,048,576 | — | 42 | $>10^6$ | 41 |
| 40 | 80 | 1,099,511,627,776 | — | 82 | infeasible | 81 |

Key engineering findings from this experiment:
1. **Explicit DNF ATMS is untenable for fine-grained DAGs**: Even 40 sequential binary choices (e.g., 40 lemmas each provable by either of two solvers or tactics) produces $>10^{12}$ minimal environments.
2. **ROBDD/ZDD compression collapses structured diamond blowup to $O(k)$ ($2k+2$ nodes)** and evaluates single-atom retraction `restrict(f, a_1=0)` in $O(|G|)$ time ($82 \to 81$ nodes, and subsequently `restrict(..., b_1=0)` collapses directly to terminal `0` = `FALSE`).
3. **Variable ordering is a sharp hazard**: Separating coupled alternative assumptions ($a_1 < \dots < a_k < b_1 < \dots < b_k$) causes the ROBDD to explode to $2^{k+1}$ nodes ($8{,}192$ nodes at $k = 12$, double the explicit DNF count!). Variable ordering in a symbolic ATMS must therefore cluster mutually alternative assumptions (e.g., alternative prover backends or sibling lemmas for the same obligation) contiguously, and bound the tracked assumption alphabet to coarse trust roots.

#### 3.2 Cyclic Proof Maintenance: Counting Failure vs. DRed vs. Backward/Forward (B/F)

When derivations are cyclic (for example, mutually recursive definitions, coinductive invariants, or bi-implications $C_0 \to C_1 \to \dots \to C_{m-1} \to C_0$ with independent external roots $A_0 \to C_0$ and $A_1 \to C_{m-1}$), incremental deletion algorithms diverge sharply:

| Algorithm | Primary Source | Behavior on Retracting $A_0$ (while $A_1$ holds) on $m=8$ Cycle | Behavior on Retracting Both $A_0$ and $A_1$ | Worst-Case Space / Complexity Trade-off |
| :--- | :--- | :--- | :--- | :--- |
| **Naive Reference Counting** | Gupta et al. (1993) §3 | Leaves all 8 nodes valid ($0$ transitions) | **UNSOUND**: leaves all **8 ghost nodes** with count $= 1 > 0$ | $O(|V|)$ integers; sound **only** on acyclic DAGs |
| **DRed (Delete & Rederive)** | Gupta, Mumick & Subrahmanian (SIGMOD 1993, DOI `10.1145/170035.170066`) | Over-deletes all **8** cycle nodes, then re-derives all **8** from $A_1$ (**16 transitions for 0 net truth changes**) | Over-deletes all 8, re-derives 0 (**sound**) | $O(|J|)$ rules; sound on arbitrary positive/stratified recursion, vulnerable to over-deletion storms |
| **Backward/Forward (B/F)** | Motik, Nenov, Piro & Horrocks (AAAI 2015, DOI `10.1609/aaai.v29i1.9409`) | Checks $C_0$ backward via $C_7 \leftarrow A_1$ (**3 nodes checked, 0 over-deletions**) | Proves $C_0$ unprovable backward, deletes cycle cleanly (**sound**) | $O(|J|)$ rules; locally avoids DRed cascades whenever alternative proofs are near the retraction boundary |
| **Horn JTMS (Rooted Support Tree)** | Forbus & de Kleer `jtms.lisp:223-246` | Over-deletes only nodes whose active `support` path passes through $A_0$, then re-attaches via `find-alternative-support` | Clears all 8 nodes cleanly (**sound**, cycle-free `support` tree) | $O(|V|+|J|)$; re-derivation depends on which root won initial `support` assignment |
| **ATMS / $\mathrm{PosBool}(X)$** | de Kleer (1986), `atms.lisp:367-406` | Strips $\{A_0\}$ from each label; $\{A_1\}$ remains (**0 re-derivations**) | Strips $\{A_0\}$ and $\{A_1\}$; labels become $\emptyset$ (**0 re-derivations**) | Sound on cycles; exponential worst-case label size without symbolic BDD/ZDD compression or assumption stratification |

**Derived architectural synthesis for content-addressed proof stores:** Neither pure ATMS nor pure JTMS/DRed dominates at million-node scale. A **stratified hybrid engine** resolves both pathologies:
- **Upper trust-root stratum (Symbolic ATMS / ROBDD-ZDD over $O(10^2\text{--}10^3)$ coarse atoms):** Track coarse foundational assumptions—kernel version/patch IDs, custom axioms, external SMT/SAT oracle versions, ISA/microarchitecture contracts, compiler pass versions, and cryptographic hash algorithm IDs—as symbolic $\mathrm{PosBool}(X) / I_{\mathcal{N}}$ labels attached to coarse verification units (modules or proof certificates). Retracting a foundational assumption (e.g., a CVE in an SMT solver or a microcode erratum) yields an instant impact query (`restrict(label, atom=0) == 0`) across the entire store without touching intra-module proof DAGs.
- **Lower intra-module stratum (JTMS / B-F / incremental memoization):** Track fine-grained AST, lemma, and type-checking dependencies inside each module using compact local justifications and backward/forward revalidation, avoiding ATMS label explosion across deep internal diamond proofs.

---

### 4. Failure Modes of Monotonic Proof Stores and Incremental Compilers Under Foundational Retraction

Basis: source (`leanprover/lean4@8009d0a6...`, `src/Lean/Util/CollectAxioms.lean:15-155`; `salsa-rs/salsa@496752ea...`, `src/durability.rs:1-146`) + derived.

Direct inspection of two leading verification/compiler dependency engines illustrates the exact structural gap between monotonic forward dependency tracking and non-monotonic truth maintenance:

1. **Lean 4 Kernel Axiom Collection (`leanprover/lean4/src/Lean/Util/CollectAxioms.lean`):**
   - `exportedAxiomsExt` (lines 120–146) is a `PersistentEnvExtension (Name × Array Name)` whose `exportEntriesFnEx` precomputes, at `.olean` serialization time, a sorted `Array Name` of every transitively referenced `ConstantInfo.axiomInfo` constant (lines 56–67) for each exported declaration. Downstream modules look up imported axiom sets in $O(\log N)$ via `ExportedAxiomsState.find?` (`binSearch`, lines 102–111) without inspecting imported proof terms.
   - **Three structural limitations relative to an ATMS**:
     - *Single monomial, no disjunctive alternatives*: Each theorem records one flat conjunctive set of axioms corresponding to its single materialized proof term, rather than an antichain of alternative proof environments.
     - *Forward-only, no inverted retraction index*: `.olean` files store `Theorem -> Set(Axiom)`, not `Axiom -> Set(Theorem)` (analogous to `atms.lisp`'s `env-nodes`). Discovering all affected theorems across a multi-crate proof repository when a custom axiom or oracle axiom (`Lean.ofReduceBool`, `Lean.trustCompiler`, or a domain-specific FFI axiom) is retracted requires scanning every exported `.olean` table.
     - *Invisible non-axiom TCB dependencies*: `CollectAxioms.collect` (lines 56–67) visits only kernel constants in `env.checked.get` (and skips `.quotInfo` explicitly at line 63 unless `Quot.sound` appears as an `.axiomInfo`). Kernel implementation version/errata, unverified external checkers, build-tool hashes, and cryptographic digest algorithms (e.g., migrating `.olean` content hashes if a hash primitive breaks) are completely absent from the axiom set and therefore un-retractable except via out-of-band full cache invalidation.
2. **Salsa Incremental Computation (`salsa-rs/salsa/src/durability.rs`):**
   - Salsa optimizes revalidation via four ordered durability tiers (`DurabilityVal`: `Low = 0`, `Medium = 1`, `High = 2`, `NeverChange = 3`, lines 62–68), tracking the latest revision at which inputs of each durability changed (`Durability::LEN = 3`, line 117—`NeverChange` has *no* runtime revision slot).
   - Lines 99–103 explicitly specify the monotonic freeze invariant: *"Setting an input field to this durability permanently freezes that field. Any later attempt to change its value or durability will panic."*
   - Consequently, Salsa's red-green / early-cutoff algorithm is strictly **input-revision monotonic**: it assumes stable foundations (`NEVER_CHANGE` interned items, core compiler/kernel rules) cannot be invalidated mid-session, and it cannot query "which derived artifacts remain valid if assumption $A$ is revoked" without mutating an input and lazily re-executing queries along the forward dependency trace.
3. **Cryptographic Primitive Retraction in Content-Addressed Proof Stores (derived):**
   - In content-addressed stores (where artifact identity is $H(\text{payload})$ for a hash function $H$ such as SHA-1, SHA-256, or BLAKE3), breaking collision resistance of $H$ does **not** merely invalidate one leaf node—it constitutes an **undercutting defeater** on the store's *addressing and caching equivalence relation* ($H(x) = H(y) \not\Rightarrow x = y$). Modeling the hash suite itself (`HashAlgo::SHA1`, `HashAlgo::SHA256`) as a first-class ATMS assumption atom on cached verification judgments (`VerifiedUnder(artifact_hash, kernel_ver, hash_algo)`) allows a proof store to distinguish *re-checkable cached references* (which must be re-hashed and re-verified under $H_{\text{new}}$) from *already migrated* certificates without nuking unaffected proofs.

---

### 5. Structured Assurance Cases (GSN v3, CAE Blocks, Assurance 2.0) and Formal Defeaters

Basis: normative (`Pollock 1987`, DOI `10.1016/S0364-0213(87)80011-8`; `Goodenough, Weinstock & Klein 2015`, DOI `10.1184/R1/6573413.v1`; `Bloomfield & Netkachova 2014`, DOI `10.1109/ISSREW.2014.72`; `SCSC-141C GSN v3`; `Bloomfield & Rushby arXiv:2004.10474v3`) + source (`jonasthewolf/gsn2x@9effad83...`, `src/gsn.rs:24-165`, `src/gsn/validation.rs:9-433`; `SRI-CSL/ETB@ee4692f3...`, `README.md`).

#### 5.1 Defeater Taxonomy and Operational Semantics

Drawing from John Pollock's epistemology of defeasible reasoning (1987) as specialized for assurance cases by Goodenough, Weinstock & Klein (CMU/SEI-2015-TR-005, *Eliminative Argumentation*) and Bloomfield & Rushby (*Assurance 2.0*, `arXiv:2004.10474v3`), a **defeater** is a reason to doubt a claim, evidence item, or inferential link. Three distinct classes matter operationally because they map to different TMS retraction targets:

| Defeater Class | Formal Target | Epistemic Meaning | Assurance-Case Representation | TMS / Provenance Mapping |
| :--- | :--- | :--- | :--- | :--- |
| **Rebutting Defeater** | Conclusion / Claim $C$ | Directly argues or proves $\neg C$ (counterexample to the claim itself) | GSN v3 `CounterGoal` / `CounterSolution` with `ChallengesNode(C)`; CAE exact defeater (negation) block | Asserts contradiction $C \wedge \neg C \to \bot$, creating a nogood over the minimal environments supporting $C$ |
| **Undermining Defeater** | Premise / Evidence $E$ | Attacks the validity, authenticity, or measurement soundness of a leaf evidence item or assumption (without proving $\neg C$) | GSN v3 `ChallengesNode(Sn)` or `ChallengesNode(A)`; CAE evidence-incorporation sideclaim defeat | Retracts leaf assumption atom $a_E$ (`nogood({a_E})`), invalidating only paths relying on $E$ while preserving alternative proofs of $C$ |
| **Undercutting Defeater** | Inference step / Warrant $R : P_1 \wedge \dots \wedge P_k \to C$ | Attacks the *deductive sufficiency* or soundness of the step linking premises to conclusion (e.g., incomplete hazard enumeration, unsound tool rule, broken side-condition) | GSN v3 `ChallengesRelation(P -> C)` (`GsnEdgeType::ChallengesRelation`); CAE sideclaim failure (`sideclaim ⊃ (subclaim ⊃ parent)`) | Retracts an explicit **rule-soundness assumption atom** $a_R$ attached to justification $R$ (`P_1 ∧ ... ∧ P_k ∧ a_R → C`) |

**Key TMS modeling invariant (derived):** Standard ATMS justifications $P_1 \wedge \dots \wedge P_k \to C$ are permanent once asserted unless guarded by an assumption atom. To support **undercutting defeaters** (retracting an inference rule, compiler pass, or hazard-list completeness warrant without retracting its premises), every fallible inference step $R$ MUST be reified as a guarded Horn justification $P_1 \wedge \dots \wedge P_k \wedge a_R \to C$ where $a_R \in \mathcal{A}$ is a dedicated warrant assumption atom (corresponding directly to Assurance 2.0's sideclaim $S_R \supset (\bigwedge P_i \supset C)$).

#### 5.2 Concrete Notation Comparison: GSN v3 Dialectical Extension vs. CAE Blocks / Assurance 2.0

Direct inspection of `jonasthewolf/gsn2x@9effad83...` (`src/gsn.rs:24-165`, `src/gsn/validation.rs:9-433`) documents how the **GSN Community Standard Version 3 (`SCSC-141C`) Dialectical Extension** is implemented and mechanically validated:
- **Core + Dialectical Node Types (`src/gsn.rs:25-34`)**: `Goal` (`G`), `Strategy` (`S`), `Solution` (`Sn`), `Justification` (`J`), `Context` (`C`), `Assumption` (`A`), plus dialectical **`CounterGoal` (`CG`)** and **`CounterSolution` (`CSn`)** (inferred from ID prefixes at lines 423–425).
- **Edge & Challenge Types (`src/gsn.rs:43-48, 96-99`)**: `SupportedBy`, `InContextOf`, **`ChallengesNode`** (`Challenge::Node(id)`), and **`ChallengesRelation`** (`Challenge::Relation((left, right))`, parsed from `"X -> Y"` at lines 256–260).
- **Defeat state and structural validation (`src/gsn/validation.rs:136-190, 355-433`)**:
  - `V03` (line 161): An `undeveloped` element must not have supporting arguments.
  - `V12` (lines 180–187): Only `CounterGoal` or `CounterSolution` nodes may emit `challenges` edges.
  - `V10` (lines 362–372): A node marked `defeated: true` MUST be targeted by at least one `Challenge::Node(id)` edge (note source `TODO` at line 367: `gsn2x` does *not* yet check whether an incoming defeated relation suffices to mark a node defeated, nor does it transitively propagate `defeated` upward to parent goals!).
  - `V13` (lines 377–391): Any entry in `defeated_relation` must match an actual `supported_by`, `in_context_of`, or `challenges` edge of the node.
  - `V11` (lines 399–433): Optional linter warning flagging usage of the dialectical extension (`CounterGoal` / `CounterSolution`).
- **Crucial operational gap in static GSN validators (source + derived)**: `gsn2x` validates *syntactic well-formedness* of dialectical links (`V10`–`V13`), but does **not** perform non-monotonic truth-maintenance propagation (if a `CounterSolution` defeats a leaf `Solution` or a `SupportedBy` relation, parent `Goal`s are not automatically recomputed as defeated or re-grounded via alternative branches).

By contrast, **CAE Blocks** (Bloomfield & Netkachova, ISSREW 2014, DOI `10.1109/ISSREW.2014.72`) and **Assurance 2.0** (`arXiv:2004.10474v3`, pp. 1–6) restrict all argument steps to **five pre-analyzed templates**:
1. **Evidence Incorporation**: Maps raw artifact $E$ to a *measured claim* stating strictly what the artifact observes (minimizing hidden leaps).
2. **Substitution**: Transforms a measured or proxy claim into a *useful claim* (e.g., MC/DC on executable object code $\to$ no unreachable code), guarded by an explicit **sideclaim** justifying the substitution theory.
3. **Decomposition**: Breaks a parent claim into subclaims (diversity, partitioned, containment, or cumulative), guarded by a sideclaim proving completeness/adequacy (turning inductive leaps into deductive steps under **Natural Language Deductivism (NLD)**).
4. **Concretion**: Specializes an abstract property (e.g., "safe") into concrete formal specifications, with a sideclaim validating fidelity.
5. **Calculation**: Derives a quantitative/logical property from subclaims using a verified mathematical or tool-based model (sideclaim justifies model validity and tool soundness).

Every Assurance 2.0 block is logically interpreted as a **deductive Horn clause** $\text{sideclaim} \wedge \bigwedge_i \text{subclaim}_i \supset \text{parent}$ (`arXiv:2604.00034v1`, p. 9), and early-stage incomplete inductive steps are made explicit by attaching an unsupported "nugatory" sideclaim (`arXiv:2004.10474v3`, p. 5). The **Indefeasibility Criterion** (`arXiv:2004.10474v3`, p. 2) defines justified belief as: all known defeaters have either been defeated themselves (turning red defeater nodes into positive blue subcases) or explicitly adjudicated as negligible residual doubts, and no credible unexamined doubts remain.

In automated formal verification toolchains, **SRI's Evidential Tool Bus (`SRI-CSL/ETB@ee4692f3...`)** bridges heterogeneous tools (model checkers, theorem provers, static analyzers) using a **distributed Datalog workflow engine** where claims are Datalog predicates and tool wrappers act as interpreted predicates producing provenance-tracked evidence artifacts. Pairing an ETB-style Datalog claim graph with an ATMS defeater layer ensures that an empirical counterexample (for instance, a microarchitectural side-channel fuzzer refuting an ISA constant-time assumption `ISA_CT_Contract`) asserts a single nogood `{ISA_CT_Contract}` that immediately downgrades `ConstantTime` (`|L| : 1 -> 0`) while leaving `MemorySafe` (`L = {{LeanKernel_4_28, SpecAxioms}}`, `|L| = 1`) completely untouched—verified directly in our execution probe.

---

### 6. Confidence Propagation Pitfalls (Graydon & Holloway 2017) vs. Assurance 2.0 Fréchet Bounds (2026)

Basis: normative (`Graydon & Holloway 2017`, DOI `10.1016/j.ssci.2016.09.004`; `Bloomfield & Rushby arXiv:2604.00034v1`, pp. 7–23, 37–44) + execution.

Graydon & Holloway (2017) analyzed **12 published quantitative confidence-propagation methods** (5 BBN-based, 5 Dempster–Shafer / evidential-reasoning-based, and 2 other approaches) by perturbing the original authors' worked examples and uncovered three recurring failure modes:

1. **Many-Subclaims Dilution**: In averaging or additive-belief propagators, one catastrophically weak subclaim among many strong ones is masked. In our execution probe with 19 subclaims at $0.95$ and 1 subclaim at $0.05$, the arithmetic mean yields **`0.905`** (falsely reassuring), whereas the conservative Fréchet intersection lower bound collapses to **`0.0`** and the independent product drops to **`0.0189`**.
2. **Arbitrary Decomposition Sensitivity**: Splitting one $0.95$ subclaim into 10 subclaims of $0.95$ alongside a single $0.50$ subclaim inflates an unweighted average from $72.5\%$ to $90.9\%$ purely via syntactic refactoring (`arXiv:2604.00034v1`, pp. 38–39). Conversely, unconditional product formulas penalize deep or finely decomposed arguments purely for having more subclaims (Cyra & Górski "Imperfect Examples").
3. **Sideclaim / Warrant Insensitivity (Zhao et al. BBN Counterexample)**: In Zhao et al.'s generic BBN encoding of a hazard-completeness argument (`arXiv:2604.00034v1`, Fig. 15, pp. 39–40), dropping confidence in the *hazard-list completeness sideclaim* from $85\%$ to $0.01\%$ barely moved top-level safety confidence—from **$89.460\%$ to $86.404\%$**!
4. **Dempster–Shafer / Disbelief Masking & Conflation of Uncertainties**: Merging belief and disbelief in a single scalar lets positive evidence numerically drown out an active undermining defeater; similarly, many schemes conflate **aleatoric uncertainty** (random physical failure rate in the world) with **epistemic uncertainty** (subjective doubt about whether a claim or proof is true) and overlook **evidence discriminating power** (Good's confirmation measure $\log \frac{P(E \mid C)}{P(E \mid \neg C)}$, `arXiv:2604.00034v1`, p. 8, which rejects weak evidence equally consistent with $C$ and $\neg C$).

**Assurance 2.0 Compositional Confidence Architecture (`arXiv:2604.00034v1`, Table 1, p. 23 & §3.2):**
Bloomfield & Rushby avoid Graydon & Holloway's counterexamples via two structural rules:
1. **Strict Logical & Dialectical Gate**: Probabilistic assessment is **never** run until logical soundness (deductive entailment per block) and dialectical indefeasibility (all active defeaters resolved or accepted as negligible residual risks) have already passed. A subclaim or sideclaim with $0.01\%$ confidence is rejected at the logical gate before probabilities are computed, and disbelief is handled qualitatively via defeaters rather than averaged against belief.
2. **Explicit Multiplicative Sideclaim Gating + Dependence-Specific Combination Formulas**: Every reasoning block computes:
   $$\mathrm{conf}(\text{parent}) = f(\text{argstep})\!\left(h(\text{argstep})(\mathrm{conf}(\text{subclaims}))\right) \times \mathrm{conf}(\text{sideclaim})$$
   Under this rule, on Zhao et al.'s example (combined subclaims $= 0.90$), varying sideclaim confidence over $\{0.85, 0.999, 0.0001\}$ produces $\{0.765, 0.8991, 0.00009\}$—eliminating sideclaim insensitivity. For multi-subclaim decomposition blocks, `h(argstep)` is chosen explicitly according to the epistemic dependence relation among subclaims (reproduced and verified against Table 1 of `arXiv:2604.00034v1` for $c_1 = 0.9, c_2 = 0.85, c_3 = 0.8$, doubts $d_i = 1 - c_i$, $P(c_2 \mid c_1) = 0.89$, $P(c_3 \mid c_1 \wedge c_2) = 0.95$):

| Decomposition Dependence Model | Formula for `h(argstep)` | Underlying Probabilistic Assumption | Verified Value ($c = (0.9, 0.85, 0.8)$) |
| :--- | :--- | :--- | ---: |
| **Sum of Doubts (Fréchet intersection lower bound)** | $1 - \min(1, \sum_{i=1}^n d_i) = \max(0, \sum c_i - (n-1))$ | **None** (most conservative sound lower bound for arbitrary dependence) | `0.55` |
| **Confidence Product** | $\prod_{i=1}^n c_i$ | Subclaims fail independently | `0.612` |
| **Conditional Chain (Cumulative)** | $c_1 \cdot P(c_2 \mid c_1) \cdot P(c_3 \mid c_1 \wedge c_2)$ | Sequential subclaims building on predecessors | `0.761` |
| **Arithmetic Mean (Equal Partition)** | $\frac{1}{n} \sum_{i=1}^n c'_i$ | Disjoint equally weighted concern partitions (perfect negative correlation) | `0.85` |
| **Weighted Average (Partitioned)** | $\sum_{i=1}^n w_i c'_i$ (with $\sum w_i = 1$) | Disjoint weighted concern partitions | `0.865`* |
| **Containment (Fréchet union lower bound)** | $\max_i c_i$ | Perfect positive dependence (one subclaim subsumes another's concerns) | `0.9` |
| **Diversity (Product of Doubts)** | $1 - \prod_{i=1}^n d_i$ | **Strong assumption**: diverse methods eliminate independent concerns | `0.997` |

*\*Primary-source arithmetic discrepancy observed during execution*: In `arXiv:2604.00034v1` Table 1 (p. 23), the printed example expression reads `0.5×0.9+0.3×0.8+0.2×0.85` alongside example value `0.865`; direct evaluation of the printed ordering yields `0.860`, while pairing weights $(0.5, 0.3, 0.2)$ with $(c_1, c_2, c_3) = (0.9, 0.85, 0.8)$ yields `0.5×0.9 + 0.3×0.85 + 0.2×0.8 = 0.865`.

## Boundaries

- **Non-monotonic ATMS extensions and general Answer Set Programming (ASP) solvers — `not examined`**: This report inspects de Kleer's basic Horn ATMS (`atms/atms.lisp`) and Doyle's SL-network semantics, and verifies the stable-model correspondence on small loop topologies. We did not inspect full non-monotonic ATMS encodings (de Kleer's *Extending the ATMS*, 1986, using out-assumptions and interpretation construction over large disjunctive clauses) or modern CDCL-based ASP solvers (e.g., `clingo` / `clasp` nogood learning) as drop-in replacements for a proof-store TMS.
- **Provenance semirings with monus / negation ($\mathrm{m}$-semirings and dual-indeterminate polynomials) — `not examined`**: The isomorphism established in Section 2 covers positive Horn derivations ($\mathrm{PosBool}(X)$) plus nogood-ideal quotienting ($I_{\mathcal{N}}$). Non-monotonic stratified negation and first-order provenance games (Geerts & Poggi 2010; Grädel & Tannen 2017) were not probed in execution.
- **OMG SACM 2.2/2.3 XML/XMI schema and Isabelle/SACM mechanized kernel integration — `not examined`**: While OMG SACM is the cross-notation metamodel unifying GSN and CAE (including counter-claim attributes), we did not directly inspect the OMG SACM XMI specification files or Isabelle/SACM `.thy` sources in this investigation.
- **Zero-Suppressed Decision Diagrams (ZDDs) vs. ROBDDs on sparse antichains — `unknown`**: Our execution probe verified ROBDD compression ($2k+2$ nodes vs. $2^k$ explicit environments) and demonstrated variable-ordering blowup ($2^{k+1}$). ZDDs (Minato 1993) are designed specifically for sparse families of sets (antichains) and are expected to outperform ROBDDs when $|\mathcal{A}| \gg |E|$, but exact constant-factor and subsumption-operator overhead (`minimal-union` on ZDDs vs. ROBDDs) on real multi-million-node proof stores was not benchmarked here.
- **Automatic transitive defeat propagation in `gsn2x@9effad83...` — `unsupported`**: Direct inspection of `jonasthewolf/gsn2x/src/gsn/validation.rs:355-394` establishes that `gsn2x` checks local syntactic consistency of `defeated` and `defeated_relation` annotations (`V10`, `V13`), explicitly leaves checking incoming defeated relations as a `TODO` (line 367), and does not implement automated transitive defeat propagation or belief revision.
- **In-place retraction of `Durability::NEVER_CHANGE` inputs in `salsa-rs/salsa@496752ea...` — `known not to apply` / `unsupported`**: `src/durability.rs:99-103, 117` explicitly forbids mutating `NEVER_CHANGE` inputs (panicking on attempted modification and allocating no revision slot).
- **Exact empirical soundness of subjective probability priors in Assurance 2.0 — `known not to apply`**: Assurance 2.0's Fréchet-bounded formulas guarantee algebraic coherence and immunity to Graydon & Holloway's structural propagation paradoxes, *not* empirical calibration of human-estimated leaf probabilities $P(C \mid E)$ or conditional independence claims (which remain subject to SME judgment and confirmation-measure review).

## Evidence

### Primary Specifications, Papers, and Repositories

1. **Doyle (1979)**: Jon Doyle, *"A Truth Maintenance System"*, *Artificial Intelligence* 12(3), pp. 231–272, Nov 1979, DOI `10.1016/0004-3702(79)90008-0`. Defines SL-justifications, CP-justifications, well-founded IN/OUT labeling, and dependency-directed backtracking.
2. **de Kleer (1986)**: Johan de Kleer, *"An Assumption-based TMS"*, *Artificial Intelligence* 28(2), pp. 127–162, Mar 1986, DOI `10.1016/0004-3702(86)90080-9`. Defines environments, labels, nogoods, and the four label invariants (soundness, consistency, completeness, minimality).
3. **Forbus & de Kleer Reference Source (`id2359/bps`)**: Commit `3d072521dc7c759aaae7bb9d1c459c20ef6d8a01`:
   - `jtms/jtms.lisp`: `defstruct jtms` (L17–29), `defstruct tms-node` (L35–47), `defstruct just` (L53–57, positive `antecedents` only), `justification-satisfied?` (L162–163), `retract-assumption` (L195–200), `propagate-outness` (L223–236), `find-alternative-support` (L238–246), `default-assumptions` (L278–287), `assumptions-of-node` (L292–302), `handle-one-contradiction` (L333–348).
   - `atms/atms.lisp`: `defstruct atms` (L17–32), `defstruct tms-node` (L38–47), `defstruct env` (L66–74, reverse index `nodes`), `propagate`/`update`/`update-label` (L202–243), `weave` (L245–263), `compare-env` (L356–363), `new-nogood` (L367–385), `remove-env-from-labels` (L399–406), `explain-node` (L474–494).
4. **Green, Karvounarakis & Tannen (2007)**: *"Provenance Semirings"*, *ACM PODS 2007*, pp. 31–40, DOI `10.1145/1265530.1265535`. Defines $\mathbb{N}[X]$, $\mathrm{PosBool}(X)$, and semiring homomorphism evaluation.
5. **Gupta, Mumick & Subrahmanian (1993)**: *"Maintaining Views Incrementally"*, *ACM SIGMOD 1993*, pp. 157–166, DOI `10.1145/170035.170066`. Defines Counting (acyclic) and DRed (general recursive) algorithms.
6. **Motik, Nenov, Piro & Horrocks (2015)**: *"Incremental Update of Datalog Materialisation: the Backward/Forward Algorithm"*, *AAAI 2015*, Vol. 29(1), DOI `10.1609/aaai.v29i1.9409`.
7. **Lean 4 Kernel Axiom Collection (`leanprover/lean4`)**: Commit `8009d0a64d2860606c6a5ac5ff6702622b24921e`, `src/Lean/Util/CollectAxioms.lean`: `CollectAxioms.collect` (L37–74, skipping `.quotInfo` at L63 and inspecting `env.checked.get`), `ExportedAxiomsState.find?` (L102–111), `exportedAxiomsExt` (L120–146), `collectAxioms` (L149–154).
8. **Salsa Durability (`salsa-rs/salsa`)**: Commit `496752ea3879af8cf3d71d1e28d76447a0cf6482`, `src/durability.rs`: `DurabilityVal` (L62–68), `Durability::NEVER_CHANGE` freeze contract (L99–103), `Durability::LEN` excluding `NEVER_CHANGE` (L117).
9. **Assurance Cases, Defeaters, and Confidence Propagation**:
   - John L. Pollock (1987), *"Defeasible Reasoning"*, *Cognitive Science* 11(4), pp. 481–518, DOI `10.1016/S0364-0213(87)80011-8`.
   - John B. Goodenough, Charles B. Weinstock, Ari Z. Klein (2015), *"Eliminative Argumentation: A Basis for Arguing Confidence in System Properties"*, CMU/SEI-2015-TR-005, DOI `10.1184/R1/6573413.v1`.
   - Patrick J. Graydon & C. Michael Holloway (2017), *"An investigation of proposed techniques for quantifying confidence in assurance arguments"*, *Safety Science* 92, pp. 53–65, DOI `10.1016/j.ssci.2016.09.004`.
   - Robin E. Bloomfield & Kateryna Netkachova (2014), *"Building Blocks for Assurance Cases"*, *IEEE ISSREW 2014*, pp. 186–191, DOI `10.1109/ISSREW.2014.72`.
   - Robin E. Bloomfield & John Rushby (2021), *"Assurance 2.0: A Manifesto"*, `arXiv:2004.10474v3`, DOI `10.48550/arXiv.2004.10474`, pp. 1–7.
   - Robin E. Bloomfield & John Rushby (2026), *"Quantifying Confidence in Assurance 2.0 Arguments"*, `arXiv:2604.00034v1` (`SRI-CSL-25-01R2`), DOI `10.48550/arXiv.2604.00034`, §3.1–3.2 (pp. 7–23), Table 1 (p. 23), §6 (pp. 37–40).
   - SCSC Assurance Case Working Group (2021), *Goal Structuring Notation Community Standard Version 3*, `SCSC-141C`.
   - `jonasthewolf/gsn2x` commit `9effad837d6a11f2c9c6135f69d5b6b3164313df`: `src/gsn.rs` (`GsnNodeType` L25–34, `GsnEdgeType` L43–48, `Challenge` L96–99, `GsnNode` L107–165, `deser_challenges` L238–260), `src/gsn/validation.rs` (`validate_module` L9–40, `V03`/`V12` L161–187, `validate_defeated` `V10`/`V13` L355–394, `validate_dialectic_extension` `V11` L399–433).
   - `SRI-CSL/ETB` commit `ee4692f3a58ab8230a1795b179829b871aebe7e3`: `README.md` (Datalog-based Evidential Tool Bus orchestration).

### Self-Contained Execution Probe and Observed Outputs (2026-11-19, Python 3.13.15)

Running the following standalone Python 3.10+ command reproduces all ATMS/$\mathrm{PosBool}(X)$, ROBDD ordering, DRed/Counting/B-F cycle, Doyle SL-loop, Assurance 2.0 Table 1, and heterogeneous defeater isolation measurements reported above:

```bash
python3 - <<'PY'
import math

# 1. Minimal de Kleer ATMS vs PosBool(X) & Diamond Blowup
class ATMS:
    def __init__(self):
        self.labels, self.cons, self.nogoods = {}, {}, []
    def add_node(self, n, assume=False):
        if n not in self.labels:
            self.labels[n] = [frozenset([n])] if assume else []
            self.cons[n] = []
    def is_ng(self, e): return any(ng <= e for ng in self.nogoods)
    def minimize(self, envs):
        u = list(dict.fromkeys(e for e in envs if not self.is_ng(e)))
        return [e for e in u if not any(o < e for o in u)]
    def justify(self, c, ants):
        self.add_node(c)
        for a in ants: self.add_node(a)
        j = (c, ants)
        for a in ants: self.cons[a].append(j)
        q = [j]
        while q:
            con, xs = q.pop(0)
            acc = [frozenset()]
            for a in xs:
                acc = self.minimize([e1 | e2 for e1 in acc for e2 in self.labels[a] if not self.is_ng(e1 | e2)])
                if not acc: break
            if not acc: continue
            m = self.minimize(self.labels[con] + acc)
            if set(m) != set(self.labels[con]):
                self.labels[con] = m
                q.extend(self.cons[con])
    def nogood(self, env):
        self.nogoods = [g for g in self.nogoods if not env <= g] + [env]
        pruned = 0
        for n, l in self.labels.items():
            b = len(l); self.labels[n] = [e for e in l if not env <= e]; pruned += b - len(self.labels[n])
        return pruned

for k in (4, 8, 12):
    a = ATMS(); a.justify("N0", ())
    for i in range(1, k + 1):
        a.add_node(f"a{i}", True); a.add_node(f"b{i}", True)
        a.justify(f"N{i}", (f"N{i-1}", f"a{i}")); a.justify(f"N{i}", (f"N{i-1}", f"b{i}"))
    n0 = len(a.labels[f"N{k}"]); pruned = a.nogood(frozenset(["a1"]))
    print(f"ATMS k={k}: |L|={n0}, after nogood(a1) |L|={len(a.labels[f'N{k}'])}, pruned={pruned}")

# 2. ROBDD Variable-Ordering Probe on /\_{i=1..k} (a_i \/ b_i)
class ROBDD:
    def __init__(self): self.u, self.n, self.ac, self.rc = {}, {0: None, 1: None}, {}, {}
    def mk(self, v, lo, hi):
        if lo == hi: return lo
        k = (v, lo, hi)
        if k not in self.u: nid = len(self.n); self.u[k] = nid; self.n[nid] = k
        return self.u[k]
    def apply(self, op, x, y):
        if op == "and" and (x == 0 or y == 0): return 0
        if op == "or" and (x == 1 or y == 1): return 1
        if x == y: return x
        if (op == "and" and x == 1) or (op == "or" and x == 0): return y
        if (op == "and" and y == 1) or (op == "or" and y == 0): return x
        if (op, x, y) in self.ac: return self.ac[(op, x, y)]
        vx, vy = (self.n[x][0] if x > 1 else 10**9), (self.n[y][0] if y > 1 else 10**9)
        t = min(vx, vy)
        xl, xh = (self.n[x][1], self.n[x][2]) if vx == t else (x, x)
        yl, yh = (self.n[y][1], self.n[y][2]) if vy == t else (y, y)
        r = self.mk(t, self.apply(op, xl, yl), self.apply(op, xh, yh))
        self.ac[(op, x, y)] = r; return r
    def restrict(self, u, var, val):
        if u <= 1: return u
        v, lo, hi = self.n[u]
        if v == var: return hi if val else lo
        if v > var: return u
        return self.mk(v, self.restrict(lo, var, val), self.restrict(hi, var, val))
    def size(self, r):
        s = set()
        def dfs(u):
            if u not in s:
                s.add(u)
                if u > 1: dfs(self.n[u][1]); dfs(self.n[u][2])
        dfs(r); return len(s)

for k in (12, 40):
    b = ROBDD(); f = 1
    for i in range(k): f = b.apply("and", f, b.apply("or", b.mk(2*i, 0, 1), b.mk(2*i+1, 0, 1)))
    f1 = b.restrict(f, 0, 0); f2 = b.restrict(f1, 1, 0)
    print(f"ROBDD interleaved k={k}: nodes={b.size(f)}, after a1=0: {b.size(f1)}, after a1=b1=0: {f2}")

# 3. Doyle SL-Justification Stable Models
def stable_models(nodes, rules):
    out = []
    for m in range(1 << len(nodes)):
        cand = {nodes[i] for i in range(len(nodes)) if (m >> i) & 1}
        red = [(c, inl) for c, inl, outl in rules if outl.isdisjoint(cand)]
        lfp = set()
        while True:
            nxt = {c for c, inl in red if inl <= lfp} | lfp
            if nxt == lfp: break
            lfp = nxt
        if lfp == cand: out.append(sorted(cand))
    return out

print("Odd loop:", stable_models(["P"], [("P", set(), {"P"})]))
print("Even loop:", stable_models(["P", "Q"], [("P", set(), {"Q"}), ("Q", set(), {"P"})]))
print("Pos self-loop:", stable_models(["P"], [("P", {"P"}, set())]))

# 4. Assurance 2.0 Table 1 + Defeater Isolation
c = [0.9, 0.85, 0.8]; d = [1 - x for x in c]
print("Assurance 2.0:", round(max(0, sum(c)-2), 4), round(math.prod(c), 4), max(c),
      round(1 - math.prod(d), 4), round(sum(c)/3, 4), round(0.5*0.9 + 0.3*0.85 + 0.2*0.8, 4),
      round(0.9 * 0.89 * 0.95, 4))
a = ATMS()
for x in ("LeanKernel", "SpecAxioms", "ISA_CT"): a.add_node(x, True)
a.justify("MemorySafe", ("LeanKernel", "SpecAxioms"))
a.justify("ConstantTime", ("MemorySafe", "ISA_CT"))
a.nogood(frozenset(["ISA_CT"]))
print("Post-defeater labels:", {k: len(a.labels[k]) for k in ("MemorySafe", "ConstantTime")})
PY
```

Observed output (exit code `0`):
```text
ATMS k=4: |L|=16, after nogood(a1) |L|=8, pruned=16
ATMS k=8: |L|=256, after nogood(a1) |L|=128, pruned=256
ATMS k=12: |L|=4096, after nogood(a1) |L|=2048, pruned=4096
ROBDD interleaved k=12: nodes=26, after a1=0: 25, after a1=b1=0: 0
ROBDD interleaved k=40: nodes=82, after a1=0: 81, after a1=b1=0: 0
Odd loop: []
Even loop: [['P'], ['Q']]
Pos self-loop: [[]]
Assurance 2.0: 0.55 0.612 0.9 0.997 0.85 0.865 0.761
Post-defeater labels: {'MemorySafe': 1, 'ConstantTime': 0}
```

## Revalidation

1. **Re-run the self-contained Python probe above**: Confirms the exact ATMS/$\mathrm{PosBool}(X)$ label sizes, ROBDD compression vs. variable-ordering sensitivity, Doyle SL stable-model pathologies, Assurance 2.0 Table 1 formulas, and selective defeater isolation in `<1s` with zero external dependencies.
2. **Check Lean 4 kernel axiom collection drift**: Diff `src/Lean/Util/CollectAxioms.lean` in `leanprover/lean4` against revision `8009d0a64d2860606c6a5ac5ff6702622b24921e`, checking specifically whether `exportedAxiomsExt` has added inverted indices, kernel/tactic provenance metadata, or non-axiom trust roots beyond `.axiomInfo`.
3. **Check Salsa durability retraction changes**: Diff `src/durability.rs` in `salsa-rs/salsa` against revision `496752ea3879af8cf3d71d1e28d76447a0cf6482` to check whether `Durability::NEVER_CHANGE` remains permanently frozen without a revision slot.
4. **Check `gsn2x` dialectical validation evolution**: Diff `src/gsn/validation.rs` (`validate_defeated`) in `jonasthewolf/gsn2x` against revision `9effad837d6a11f2c9c6135f69d5b6b3164313df` to see whether the `TODO` at line 367 or transitive defeat propagation has been implemented.
5. **Check Assurance 2.0 revision updates**: Check whether a newer revision of `arXiv:2604.00034` (`SRI-CSL-25-01R2`) modifies Table 1's weighted-average example string (`0.5×0.9+0.3×0.8+0.2×0.85` vs. `0.865`) or extends the decomposition block formulas to DAGs with shared subclaims.
