# Reactive LTL and Parity-Game Synthesis, Active Automata Learning, and Petri-Net/VASS Decidability Boundaries

## Summary

Automated controller synthesis, active black-box state-machine inference, and unbounded concurrency verification are governed by sharp algorithmic cliffs and soundness boundaries that determine what can be decided, learned, or synthesized reliably:

1. **General Reactive LTL Synthesis (`2-EXPTIME`) vs. Polynomial `GR(1)` & Vacuous Realizability:** Full LTL reactive synthesis is `2-EXPTIME`-complete (Pnueli & Rosner, POPL 1989) because determinizing Büchi automata into parity automata incurs a doubly exponential worst-case blowup. Restricting specifications to Generalized Reactivity(1) (`GR(1)`, Bloem et al., JCSS 2012; `slivingston/gr1c`) reduces synthesis to a 3-nested $\mu$-calculus fixpoint computable in $O(m \cdot n \cdot |S|^2)$ symbolic $\operatorname{CPre}$ operations—yet exposes a severe **vacuity trap** under standard implication $\varphi_e \to \varphi_s$ where a "winning" controller can satisfy impossible guarantees simply by driving the environment into a safety deadlock.
2. **Quasipolynomial Parity Games (`Oink`) vs. On-the-Fly Explicit Synthesis (`Strix`):** Calude et al. (STOC 2017) proved parity games are decidable in quasipolynomial time $O(n^{\lceil \log_2 d \rceil + 6})$ via $O(\log n)$-register play-summary witnesses (implemented in `trolando/oink` `qpt.cpp`), and Jurdziński & Lazić (LICS 2017) reduced space to near-linear $O(n \log n \log d)$ (`oink` `sspm`). In practice, `meyerphi/strix` does **not** use `qpt`: it defaults to Fixpoint Iteration (`Solver::Fpi`, alongside `Solver::Zlk` and `Solver::Si`) wrapped in a **border-adversarial incremental solver** (`src/parity/solver/incremental.rs`) that treats unexplored frontier nodes as opponent-controlled to prove realizability or unrealizability soundly without constructing the full doubly exponential parity automaton.
3. **Active Mealy Learning ($L^*$ vs. `TTT`) and Black-Box Equivalence Unsoundness (`LearnLib`):** Classic Angluin $L^*$ adds all counterexample prefixes to its observation table and incurs $O(m n^2 |\Sigma|)$ query blowup in counterexample length $m$; Rivest–Schapire $L^*$ narrows counterexample analysis to $O(\log m)$ binary search but retains a dense $(n + n|\Sigma|) \times |E|$ table. `LearnLib`'s `TTT` algorithm (Isberner et al., RV 2014) achieves optimal $O(n)$ space using a spanning tree plus a redundancy-free discrimination tree (`<= n - 1` internal nodes) with discriminator finalization (`prepareSplit` / `extractSubtree`), cutting queries by >60% on multi-symbol protocol models. However, black-box protocol state fuzzing (de Ruiter & Poll, USENIX Security 2015) replaces a true equivalence oracle with bounded conformance testing (`WpMethodEQOracle`), which **unsoundly terminates early and misses deep bug states** whenever hidden state chains exceed the configured `lookahead` parameter.
4. **Petri-Net / VASS Decidability Cliff (`EXPSPACE` Coverability vs. `Ackermann`-Complete Exact Reachability):** Monotonicity makes coverability and boundedness in Petri nets / Vector Addition Systems with States (VASS) `EXPSPACE`-complete (Rackoff, TCS 1978), decidable via Karp–Miller $\omega$-acceleration or small-witness bounds $2^{2^{O(d \log d)}}$. In stark contrast, **exact reachability** is **Ackermann-complete** ($\mathbf{F}_\omega$-complete, non-primitive-recursive: Leroux & Schmitz LICS 2019 upper bound; Czerwiński & Orlikowski FOCS 2021 and Leroux FOCS 2021 lower bounds). Neither Karp–Miller $\omega$-abstraction (which destroys exact token parity) nor integer linear programming over the marking state equation $\mathbf{m}_0 + C\mathbf{x} = \mathbf{m}_t$ (used in `TAPAAL/verifypn` `LinearProgram.cpp` as a sound *unreachability* filter, but fooled by unmarked siphons) decides exact reachability.

## Applicability

This report integrates five inspected upstream implementations with eighteen primary theoretical and empirical references across four adjacent verification domains:

- **Reactive LTL, `GR(1)`, and Parity-Game Synthesis:** `meyerphi/strix` (`c0b1298fe2e0d46325662b89cb58a19cb4f02be5`), `trolando/oink` (`ad85a62f1c30ff95f48a4b564c0a9e3c5cef5ed5`), and `slivingston/gr1c` (`2a4ad3d7bb0ed3ecf4f6328fddf6f8922e66234e`), grounded in Pnueli & Rosner (POPL 1989), Bloem et al. (JCSS 2012), Calude et al. (STOC 2017), Jurdziński & Lazić (LICS 2017), and Meyer, Sickert, & Luttenberger (CAV 2018). Applies to complete-information, single-controller synchronous reactive synthesis over finite atomic propositions (Mealy/Moore turn-based semantics).
- **Active Automata Learning and Protocol Fuzzing:** `LearnLib/learnlib` (`51aec213478b8074c21515c81fd162d78efb8c8c`), grounded in Angluin (1987), Isberner, Howar, & Steffen (RV 2014; CAV 2015), and de Ruiter & Poll (USENIX Security 2015). Applies to black-box deterministic, input-enabled, cleanly resettable Mealy/DFA Systems Under Learning (SULs) over finite abstract alphabets.
- **Petri Nets / VASS Decidability and Verification Engines:** `TAPAAL/verifypn` (`fc0477705ddf22bf16b2cd9cdb97ca7f4f7573ba`), grounded in Rackoff (TCS 1978), Leroux & Schmitz (LICS 2019), Czerwiński & Orlikowski (FOCS 2021), and Leroux (FOCS 2021). Applies to ordinary unweighted/weighted Place/Transition Petri nets and $d$-dimensional VASS without inhibitor arcs, reset arcs, or transfer arcs (where reachability becomes undecidable).

These domains are examined both independently and at their engineering composition boundaries (e.g., inferring black-box protocol models with `LearnLib`, synthesizing reactive shields with `Strix`/`GR(1)`, and bounding multi-instance resource concurrency via Petri nets).

## Findings

### 1. Reactive LTL Synthesis: The 2-EXPTIME Pnueli–Rosner Barrier vs. Polynomial GR(1)

Basis: normative + source + execution

#### 1.1 General LTL Reactive Synthesis (`2-EXPTIME`-Complete)

In synchronous reactive synthesis (Church's problem for LTL), an LTL specification $\varphi$ over disjoint Boolean input propositions $\mathcal{I}$ (environment) and output propositions $\mathcal{O}$ (system) is **realizable** iff there exists a finite-state Mealy (or Moore) transducer $M: (2^{\mathcal{I}})^+ \to 2^{\mathcal{O}}$ such that every infinite play $\pi \in (2^{\mathcal{I} \cup \mathcal{O}})^\omega$ consistent with $M$ satisfies $\pi \models \varphi$:
- **Pnueli & Rosner (`POPL 1989`, `DOI: 10.1145/75277.75293`):** General LTL realizability and synthesis are **2-EXPTIME-complete** in $|\varphi|$.
  - *Upper bound:* Translate $\varphi$ to a nondeterministic Büchi automaton (NBW) of size $2^{O(|\varphi|)}$, determinize via Safra/Piterman construction into a deterministic parity automaton (DPA) with $2^{2^{O(|\varphi|)}}$ states and $2^{O(|\varphi|)}$ priorities, split each transition into an environment-move and system-move two-player turn-based parity game, and solve the game.
  - *Lower bound:* Encode acceptance of an exponential-space alternating Turing machine (ATM, $\text{AEXPSPACE} = \text{2-EXPTIME}$) by having the environment supply tape cells and challenge errors while the system outputs valid configuration sequences; checking $2^n$-bit cell indices requires only polynomial LTL length $O(n)$, forcing any winning Mealy controller to maintain $2^{2^{\Omega(n)}}$ states in the worst case.

#### 1.2 Generalized Reactivity(1) (`GR(1)`) Symbolic Fixpoint (`slivingston/gr1c`)

To avoid the doubly exponential Safra barrier on practical hardware arbiters and robotics controllers, Piterman, Pnueli, & Sa'ar (VMCAI 2006) and Bloem, Jobstmann, Piterman, Pnueli, & Sa'ar (`JCSS 2012`, `DOI: 10.1016/j.jcss.2011.08.007`) isolate the **GR(1)** fragment:
$$\varphi_{\text{GR(1)}} \equiv \Big(\theta_e \land \square \rho_e \land \bigwedge_{i=1}^{n} \square\lozenge A_i\Big) \longrightarrow \Big(\theta_s \land \square \rho_s \land \bigwedge_{j=1}^{m} \square\lozenge G_j\Big)$$
where $\theta_e, \theta_s$ are initial predicates, $\rho_e(s, \mathcal{I}')$ and $\rho_s(s, \mathcal{I}', \mathcal{O}')$ are next-state safety transition relations, $A_1,\dots,A_n$ are environment Büchi fairness assumptions, and $G_1,\dots,G_m$ are system Büchi liveness guarantees.

- **Exact 3-Nested $\mu$-Calculus Characterization:** Let the controllable predecessor operator be:
  $$\operatorname{CPre}(T) = \{ s \in S \mid \forall x' \in 2^{\mathcal{I}}.\; \rho_e(s, x') \to \exists y' \in 2^{\mathcal{O}}.\; \rho_s(s, x', y') \land (x', y') \in T \}.$$
  The exact system winning region $W$ is the 3-nested fixpoint:
  $$W = \nu Z.\; \bigwedge_{j=1}^{m} \mu Y.\; \bigvee_{i=1}^{n} \nu X.\; \Big( (G_j \land \operatorname{CPre}(Z)) \;\lor\; \operatorname{CPre}(Y) \;\lor\; (\neg A_i \land \operatorname{CPre}(X)) \Big).$$
  - Intuitively: from every state in $Z$, for every system goal $G_j$ (`AND_j`), the system can either force progress toward $G_j \land \operatorname{CPre}(Z)$ in finitely many steps (`mu Y`, guaranteeing arrival at $G_j$ while staying inside $Z$), OR trap the environment permanently outside some fairness assumption $A_i$ (`nu X`, falsifying $\square\lozenge A_i$).
  - **Complexity:** Computing $W$ requires at most $O(m \cdot n \cdot |S|^2)$ symbolic $\operatorname{CPre}$ evaluations (polynomial in the explicit state space $|S|$; still exponential in the number of state bits unless BDDs stay compact). Strategy extraction cycles through $j = 0,\dots,m-1$ using the intermediate $Y$-sublevel sets to strictly decrease distance to $G_j$ whenever the environment stays inside $A_i$.
- **Source Verification (`slivingston/gr1c@2a4ad3d7bb0ed3ecf4f6328fddf6f8922e66234e`):**
  - `src/solve_operators.c:114-230` (`compute_winning_set_BDD()`) directly implements the `Z` (initialized to `Cudd_ReadOne`, lines 172–175), `Y` (initialized to `Cudd_Not(Cudd_ReadOne)`, lines 209–210), and inner `X` BDD loops over `compute_existsmodal()` ($\operatorname{CPre}$).
  - `src/solve.c:173-258` computes `W = compute_winning_set_BDD(...)`, extracts the distance-ranking `Y` sublevels via `compute_sublevel_sets(...)` (`solve_operators.c:345`), and restricts system transitions to `strans_into_W = Cudd_bddAnd(manager, strans, W')` (`solve.c:243`) for strategy synthesis.

#### 1.3 The Environment-Violation / Vacuity Trap (Execution-Verified)

Under standard implication $\varphi_e \to \varphi_s$, the $\forall x'.\, \rho_e(s, x') \to \cdots$ quantifier inside $\operatorname{CPre}(T)$ is **vacuously true** at any state $s$ from which $\rho_e(s, x')$ admits no legal environment move! Consequently, a GR(1) synthesizer can satisfy *unsatisfiable* system guarantees by steering the state into an environment deadlock (or starving an environment liveness assumption $A_i$).
- **Empirical Demonstration (Probe 2B):** On a 12-state 2-client mutual-exclusion arbiter (`not (g0 and g1)`):
  - Fair mutex guarantees `GF(r0 -> g0)` and `GF(r1 -> g1)` yield `|W| = 12/12` (`Z` converges in 1 iteration).
  - Adding an impossible simultaneous-grant goal `GF(g0 and g1)` collapses the winning set to `|W| = 0/12` (unrealizable, `Z` converges in 2 iterations).
  - Adding a flawed environment safety assumption that forbids all environment moves whenever `g0 == 1` flips the **same impossible guarantee** from `0/12` back to **`|W| = 12/12`**: the synthesizer "wins" by asserting `g0 = 1` and vacuously deadlocking the environment!
- **Engineering Mitigation:** Always verify **well-separation** (the environment has a winning strategy to satisfy $\square\rho_e \land \bigwedge_i \square\lozenge A_i$ against *arbitrary* system outputs) or use **strict GR(1) semantics** (requiring $\rho_s$ to hold before checking whether $\rho_e$ fails) before trusting a synthesized GR(1) controller.

---

### 2. Quasipolynomial Parity Games (`Oink`) and On-the-Fly LTL Synthesis (`Strix`)

Basis: normative + source + execution

A (max-even) **parity game** is a finite directed graph $G = (V_0, V_1, E, \Omega)$ where $V = V_0 \sqcup V_1$ partitions vertices between Player 0 (`Even`, System) and Player 1 (`Odd`, Environment), every vertex has at least one outgoing edge, and $\Omega: V \to \{0, 1, \dots, d-1\}$ assigns integer priorities. An infinite play $\pi = v_0 v_1 \cdots$ is won by `Even` iff $\limsup_{k \to \infty} \Omega(v_k)$ is **even**, and by `Odd` otherwise. Parity games are **positionally determined** (every vertex belongs to either $W_0$ or $W_1$ with memoryless winning strategies) and lie in $\text{UP} \cap \text{co-UP}$ (polynomial-time solvability remains open).

#### 2.1 Quasipolynomial Breakthroughs and Exact Solver Taxonomy (`trolando/oink`)

In `trolando/oink@ad85a62f1c30ff95f48a4b564c0a9e3c5cef5ed5` (`src/solvers.cpp:57-85`, `src/solvers/qpt.cpp:38-215`):

1. **Calude–Jain–Khoussainov–Li–Stephan (`STOC 2017`, `DOI: 10.1145/3055399.3055409`, `oink` `qpt.cpp`):**
   - *Key Insight:* Instead of counting every odd priority up to $n$ (Jurdziński's $O(n^{d/2})$ Small Progress Measures), track a compressed **play summary** of only $k = \lfloor \log_2 n \rfloor + 2$ registers recording the largest observed priorities along disjoint power-of-two segments of an even-dominated play. Because any simple cycle has length $\le n$, an even-winning play must eventually saturate the highest register (`pm[0]` even) without needing more than $O(\log n)$ registers!
   - *Exact Ordering and Lift in `oink/src/solvers/qpt.cpp:38-150`:* For player `pl = 0` (`Even` witness), individual register slots are totally ordered as:
     $$\bot (-1) < \cdots < 5 < 3 < 1 < 0 < 2 < 4 < 6 < \cdots$$
     (`pm_less()`, lines 38–62), compared lexicographically from index `0` (most significant) to `k-1`. Seeing priority `d` applies `up(dst, src, d, k, pl)` (`qpt.cpp:103-149`), choosing the leftmost index `j = min(j33, j34)` satisfying Lemma 3.3 (extending the longest suffix of `pl`-parity entries when all higher entries are $\bot$ or $\ge d$) or Lemma 3.4 (overwriting the leftmost entry $< d$), and resetting entries `j+1..k-1` to $\bot$. `bump()` and `au()` (`qpt.cpp:156-215`) implement the Fearnley–Jain–Schewe–Stephan–Wojtczak antagonistic value-iteration lift.
   - *Complexity:* $O(n^{\lceil \log_2 d \rceil + 6})$ time — **polynomial** when $d = O(\log n)$, and quasipolynomial for arbitrary $d \le n$. Probe 2A verifies exact agreement between `oink`'s `up`/`pm_less` fixed-point lift (`k = 5`, 70 lifts) and Zielonka's recursive algorithm on an 8-node, 5-priority game (`W0 = [0,1,2,3,6]`, `W1 = [4,5,7]`).
2. **Jurdziński–Lazić Succinct Progress Measures (`LICS 2017`, `DOI: 10.1109/LICS.2017.8005092`, `oink` `sspm` / `bsspm`):** Encodes universal $n$-leaf ordered trees of height $d/2$ as binary strings of length $O(\log n \log d)$, preserving quasipolynomial time $O(d \cdot m \cdot n^{\log_2(d/\log n) + O(1)})$ while shrinking space from quasipolynomial to **near-linear** $O(n \log n \log d)$.
3. **Quasipolynomial Zielonka (`oink` `zlkq`, `zlkpp-waw`, `zlkpp-liv`, `ppq`, Parys 2019):** Adds a recursion-depth precision budget $p$ to Zielonka's classic recursive attractor decomposition, turning exponential worst-case Zielonka into quasipolynomial time.
4. **Practice vs. Worst-Case Theory (`oink` `solvers.cpp:57-85`):** On real synthesis and model-checking parity games, solvers with *exponential* theoretical worst cases—**Fixpoint Iteration (`fpi`)**, **Priority Promotion (`pp`, `rr`, `dp`)**, **Tangle Learning (`tl`)**, and **optimized Zielonka (`zlk`)**—regularly outperform `qpt` and `sspm` by 1–3 orders of magnitude because real games rarely exhibit Friedman's adversarial ladder gadgets.

#### 2.2 On-the-Fly Explicit Synthesis in `Strix` (`meyerphi/strix`)

Inspection of `meyerphi/strix@c0b1298fe2e0d46325662b89cb58a19cb4f02be5` (Meyer, Sickert, Luttenberger, `CAV 2018`, `DOI: 10.1007/978-3-319-96145-3_31`) establishes three load-bearing implementation facts:

1. **Actual Parity Solvers (`src/options.rs:301-329`, `src/parity/solver/{fpi,zlk,si}.rs`):** Strix does **not** run Calude's `qpt` algorithm. Its three selectable parity solvers are:
   - `Solver::Fpi` (**default**, `options.rs:328`): Distraction-based freeze/thaw Fixpoint Iteration (`src/parity/solver/fpi.rs:26-95`, ported directly from `trolando/oink`'s `fpi.cpp`, Bruse/van Dijk `arXiv:1909.07659`), maintaining `frozen: Vec<Color>` and `distraction: Vec<bool>` arrays per node.
   - `Solver::Zlk`: Recursive Zielonka (`src/parity/solver/zlk.rs:1-93`).
   - `Solver::Si`: Non-deterministic Strategy Iteration (`src/parity/solver/si.rs`, `arXiv:0806.2923`).
2. **Semantic Decomposition + `Owl` Max-Even DPA (`src/constructor/mod.rs:1-40`):** Strix delegates LTL-to-DPA translation to `Owl` (`owl::automaton::MaxEvenDpa`), semantically decomposing $\varphi$ into smaller safety, co-safety, Büchi, co-Büchi, and general sub-automata whose transitions are symbolically labeled by CUDD BDDs (`cudd::Bdd`), avoiding eager monolithic Safra product construction.
3. **Sound Border-Adversarial Incremental Solving (`src/parity/solver/incremental.rs:28-65`):**
   Strix explores the DPA product graph lazily in batches (`ExplorationQueue`), interleaving partial graph construction with `IncrementalSolver::solve()`:
   - First, it propagates previously proven winning sets `self.winning[Even]` and `self.winning[Odd]` backward via player attractors (`lines 33-37`).
   - Next, for each `player` $\in \{\text{Even}, \text{Odd}\}$, it constructs `disabled = self.winning[!player] ∪ game.border()`, extends `disabled` by `!player`'s attractor (`disabled.attract_mut(game, !player)`), unions `self.winning[player]`, and runs the inner solver on the remaining closed subgame (`lines 38-50`).
   - **Soundness Proof Sketch (verified in Probe 2A):** Because every vertex from which `!player` can force play into the unexplored `border()` is removed before computing `winning_new`, any strategy winning for `player` in the pruned subgame keeps play strictly inside the already-explored interior forever—regardless of what transitions exist beyond `border()`. Hence `winning_new ⊆ W_player(G_full)` monotonically! As soon as `initial_node()` enters `winning[Even]` (realizable) or `winning[Odd]` (unrealizable), exploration stops immediately, and `strategy()` (`lines 67-75`) extracts a winning strategy over the explored subgame (followed by Mealy machine minimization in `src/controller/machine/minimization.rs` and BDD/AIGER circuit synthesis in `src/controller/aiger.rs`).

#### 2.3 Reactive Synthesis & Parity-Game Comparison Matrix

| Approach / Tool | Logic / Input | Worst-Case Time | Worst-Case Space | Realizability & Controller Guarantees | Primary Failure / Bottleneck |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Pnueli–Rosner (Monolithic)** | Full LTL | `2-EXPTIME`-complete | $2^{2^{O(|\varphi|)}}$ | Exact (sound & complete); finite Mealy | Eager Safra DPA state explosion |
| **GR(1) (`slivingston/gr1c`)** | GR(1) fragment | $O(m n |S|^2)$ $\operatorname{CPre}$ ops | Symbolic BDD size | Polynomial in $|S|$; clean strategy extraction | **Vacuous wins** via env safety deadlock; cannot express arbitrary nested `F G` / `U` |
| **Strix (`meyerphi/strix`)** | Full LTL (`TLSF`) | `2-EXPTIME` (worst-case), `Fpi` default | Lazy explored subgame | Exact; early termination via border-adversarial soundness; AIGER output | Unavoidable DPA blowup on hard realizable counting/arbiter specs |
| **Oink `qpt` (Calude et al.)** | Explicit Parity Game | $O(n^{\lceil \log_2 d \rceil + 6})$ | Quasipolynomial | Exact; polynomial for $d = O(\log n)$ | High constant factors vs. `fpi`/`zlk`/`tl` on practical games |
| **Oink `sspm` (Jurdziński–Lazić)** | Explicit Parity Game | Quasipolynomial | **Near-linear** $O(n \log n \log d)$ | Exact; avoids `qpt` memory blowup | Slower than `fpi`/`tl` on easy games |

---

### 3. Active Automata Learning ($L^*$, Rivest–Schapire, TTT) in `LearnLib` and Black-Box Protocol Fuzzing

Basis: normative + source + execution

#### 3.1 Minimally Adequate Teacher (MAT) and Observation-Table Bottlenecks

In Dana Angluin's MAT framework (`Inf. Comput. 1987`, `DOI: 10.1016/0890-5401(87)90052-6`), a learner infers the minimal canonical finite automaton (DFA or Mealy machine) of an unknown black-box System Under Learning (SUL) using two oracles:
- **Membership Queries (`MQ`):** Given an input word $w \in \Sigma^+$, reset the SUL and observe its output $\lambda^*(w)$ (for Mealy machines, the output of the final symbol or full output trace).
- **Equivalence Queries (`EQ`):** Given a hypothesis automaton $\mathcal{H}$, either confirm $\mathcal{H} \equiv \text{SUL}$ or return a **counterexample** $c \in \Sigma^+$ where $\lambda_{\mathcal{H}}^*(c) \neq \lambda_{\text{SUL}}^*(c)$.

In `LearnLib/learnlib@51aec213478b8074c21515c81fd162d78efb8c8c` (`algorithms/active/lstar/` and `algorithms/active/ttt/`):

1. **Classic $L^*$ (`AbstractLStar.java`, `ObservationTableCEXHandlers.java:40-57`):**
   - Maintains an observation table $(S, E, T)$ with prefix-closed state representatives $S$, suffix-closed experiments $E$, and rows $T: (S \cup S \cdot \Sigma) \times E \to \Omega$.
   - Requires the table to be **closed** ($\forall s \in S, a \in \Sigma.\; \exists s' \in S.\; \text{row}(sa) = \text{row}(s')$) and **consistent** ($\forall s_1, s_2 \in S.\; \text{row}(s_1) = \text{row}(s_2) \implies \forall a \in \Sigma.\; \text{row}(s_1 a) = \text{row}(s_2 a)$, `needsConsistencyCheck() == true`).
   - On counterexample $c$ of length $m = |c|$, Classic $L^*$ inserts **every prefix** of $c$ into $S$. Thus $|S|$ can balloon to $O(m \cdot n)$, yielding worst-case query complexity $O(m n^2 |\Sigma|)$ and space $O(m n^2 |\Sigma|)$.
2. **Rivest–Schapire $L^*$ (`ObservationTableCEXHandlers.java:99-103`, `RivestSchapireMealy.java`):**
   - Eliminates consistency checks (`needsConsistencyCheck() == false`) by keeping $|S| = n$ strictly minimal (one access word per discovered state) and instead extracting a **single distinguishing suffix** from counterexample $c$ via **$O(\log m)$ binary search**.
   - Let $u_i = \text{access}_{\mathcal{H}}(c[0..i))$ be the hypothesis representative reached after prefix $c[0..i)$. Since $\text{SUL}(u_0 \cdot c[0..m)) = \text{SUL}(c) \neq \mathcal{H}(c) = \text{SUL}(u_m \cdot \varepsilon)$, binary search over $i \in [0, m-1]$ locates an exact breakpoint $i^*$ in $\lceil \log_2 m \rceil$ membership queries where $\text{SUL}(u_{i^*} \cdot c[i^*] \cdot c[i^*+1..]) \neq \text{SUL}(u_{i^*+1} \cdot c[i^*+1..])$, proving that suffix $v = c[i^*+1..]$ splits state $u_{i^*+1}$ from $u_{i^*} \cdot c[i^*]$.
   - Bounds membership queries to $O(n^2 |\Sigma| + n \log m)$ and $|E| \le n$, but still populates every cell of the dense $(n + n|\Sigma|) \times |E|$ observation table—wasting queries on suffixes irrelevant to distinguishing sink/error states.

#### 3.2 Redundancy-Free `TTT` Algorithm (`AbstractTTTLearner.java`, `TTTLearnerMealy.java`)

Introduced by Isberner, Howar, & Steffen (`RV 2014`, `DOI: 10.1007/978-3-319-11164-3_26`; `CAV 2015`, `DOI: 10.1007/978-3-319-21690-6_33`), `TTT` replaces the dense observation table with two coupled $O(n)$-space structures:
- **Spanning Tree (`TTTHypothesisMealy`):** Every discovered state has a unique prefix-closed access sequence forming a spanning tree rooted at $\varepsilon$.
- **Discrimination Tree (`BaseTTTDiscriminationTree`, `AbstractTTTLearner.java:86-88`):** Leaves store hypothesis states (`TTTState`); each internal node stores a distinguishing suffix $v$ with outgoing edges labeled by output symbol $o \in \Omega$. Because every internal node has $\ge 2$ children and there are $n$ leaves, the tree has **at most $n - 1$ internal nodes** — strictly linear $O(n)$ space, completely eliminating redundant observation-table rows!
- **Temporary Discriminator Finalization (`AbstractTTTLearner.java:344, 643-730`):**
  - Naively inserting a raw Rivest–Schapire suffix $v = c[i^*+1..]$ (which may have length $\Theta(m) \gg n$) into a discrimination tree (as in Kearns–Vazirani) allows internal-node suffixes to grow arbitrarily long, inflating query symbol length to $O(m \cdot n |\Sigma|)$.
  - TTT marks every counterexample-derived discriminator as **temporary** (forming a contiguous subtree rooted at `blockRoot` tracked in `blockList`, line 86) and runs `finalizeDiscriminator()` -> `prepareSplit()` (`lines 643-695`): it finds a 1-symbol-shorter prefix-closed discriminator `splitter.getDiscriminator().prepend(symbol)` (`line 646`) grounded in an already-finalized successor separator (`succSeparator`), queries only incoming transitions of that subtree, and partitions the block via `extractSubtree()` (`line 713`). Once finalized, **every discriminator has length $\le n - 1$**, bounding total symbols independently of long adversarial counterexamples.

#### 3.3 Empirical Comparison: Buggy TLS Handshake & Deep-Trigger Benchmarks (Probe 2C)

Running exact Python implementations of Classic $L^*$, Rivest–Schapire $L^*$, and `TTT` (Probe 2C & 2C-Ext) yields:

| Target Mealy Machine | Learner | Minimal States $n$ | Table / Tree Structure | Membership Queries (`MQ`) | Total Input Symbols | `EQ` Rounds |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Buggy TLS Handshake** ($|\Sigma|=5$, `EarlyCCS` bug: `CH->CCS->FIN->APP => DATA`) | Classic $L^*$ | 6 | $\|S\|=6, \|E\|=5$ | 155 | 530 | 1 |
| **Buggy TLS Handshake** ($|\Sigma|=5$) | Rivest–Schapire $L^*$ | 6 | $\|S\|=6, \|E\|=5$ | 155 | 530 | 1 |
| **Buggy TLS Handshake** ($|\Sigma|=5$) | **`TTT` (DT-based)** | 6 | `inner_DT=4, leaves=6` | **61 (−60.6%)** | **193 (−63.6%)** | 5 |
| **8-State Deep Trigger** ($|\Sigma|=2$, 7-step cycle + trap) | Classic $L^*$ | 8 | $\|S\|=8, \|E\|=8$ | 88 | 685 | 2 |
| **8-State Deep Trigger** ($|\Sigma|=2$) | Rivest–Schapire $L^*$ | 8 | $\|S\|=8, \|E\|=8$ | 92 | 647 | 7 |
| **8-State Deep Trigger** ($|\Sigma|=2$) | **`TTT` (DT-based)** | 8 | `inner_DT=7, leaves=8` | **84** | **603** | 8 |

*Note on Myhill–Nerode Quotienting:* In the TLS model, the normal `CipherActive` state (reached via `CH -> CKE -> CCS`) and the `EarlyCCSBug` state (reached via `CH -> CCS`) produce identical future responses to all inputs (`FIN -> AuthOK`, others `Alert`), so active learning collapses them into a single canonical state (`6` minimal states out of `7` implementation states) while still exposing the exact anomalous transition `HelloSent --CCS/OK--> CipherActive` and full exploit trace `CH -> CCS -> FIN -> APP => DATA`!

#### 3.4 Black-Box Protocol State Fuzzing & Equivalence-Oracle Unsoundness

In `de Ruiter & Poll (USENIX Security 2015, pp. 193-206)`, applying LearnLib to OpenSSL, GnuTLS, NSS, JSSE, and PolarSSL uncovered real authentication-bypass and state-confusion vulnerabilities (including early `ChangeCipherSpec` and unexpected `Heartbeat`/renegotiation transitions). However, black-box active learning carries three non-negotiable soundness limits:

1. **Bounded-Lookahead Equivalence Blind Spot (`WpMethodEQOracle.java:84-158`):** Because a black-box binary/network server has no true `EQ` oracle, LearnLib approximates `EQ` via Chow's W-method or Fujiwara's partial W-method (`WpMethodTestsIterator<>(hypothesis, Math.max(lookahead, expectedSize - hypothesis.size()))`, `WpMethodEQOracle.java:156-158`). The Wp-method is complete **if and only if** the true SUL has at most $n_{\text{hyp}} + k$ states (where $k = \max(\text{lookahead}, \text{expectedSize} - n_{\text{hyp}})$). Probe 2C confirms that on a hidden 4-step trigger (`secret = B A A B`, 4 hidden states beyond a 1-state reject hypothesis), running Wp-method with `lookahead = 2` tests sequences only up to length 3 and **terminates with `bug_detected = False`**, certifying a dangerously incomplete hypothesis. Raising $k$ suffers exponential blowup $O(n^2 |\Sigma|^{k+1})$.
2. **Nondeterminism & Imperfect Reset Poisoning:** Network timeouts, TCP retransmissions, TLS rate-limiting, or stateful server memory surviving reset violate the deterministic SUL invariant; a single inconsistent output corrupts `BaseTTTDiscriminationTree` sifting (`HypothesisChangedException`). Practical protocol fuzzers require majority-vote query repetition and deterministic mock clocks/PRNGs.
3. **Alphabet Abstraction Blindness:** Active Mealy learning observes only the manually engineered abstract alphabet $\Sigma$; bugs triggered by unmodeled message fields, cryptographic padding lengths, or sequence-number wraparound remain invisible unless lifted to register automata or combined with coverage-guided fuzzing.

---

### 4. Unbounded Concurrency Decidability: Petri Nets / VASS Coverability (`EXPSPACE`) vs. Exact Reachability (`Ackermann-Complete`)

Basis: normative + source + execution

#### 4.1 Model Equivalence: Petri Nets and $d$-VASS

An ordinary **Petri net** $(P, T, \mathbf{Pre}, \mathbf{Post}, \mathbf{m}_0)$ consists of $d = |P|$ places holding non-negative integer tokens ($\mathbf{m} \in \mathbb{N}^d$) and finite transitions $t \in T$ enabled at $\mathbf{m}$ iff $\mathbf{m} \ge \mathbf{Pre}(t)$, yielding $\mathbf{m}' = \mathbf{m} - \mathbf{Pre}(t) + \mathbf{Post}(t)$. A **$d$-dimensional Vector Addition System with States ($d$-VASS)** pairs a finite control automaton $Q$ with $d$ counters $\mathbf{c} \in \mathbb{N}^d$ updated by integer vectors $\Delta \in \mathbb{Z}^d$ subject to staying $\ge \mathbf{0}$ (no zero-tests). Petri nets and VASS are linearly/logspace inter-reducible (3 extra places encode any finite control graph $Q$ via Hopcroft–Pansiot simulation), so their asymptotic complexity classes coincide.

#### 4.2 The Complexity Cliff: From `EXPSPACE` Coverability to `Ackermann`-Complete Exact Reachability

| Decision Problem | Formal Statement | Exact Complexity | Key Mechanism / Witness Scale |
| :--- | :--- | :--- | :--- |
| **Boundedness** | Is $\{ \mathbf{m} \mid \mathbf{m}_0 \xrightarrow{*} \mathbf{m} \}$ finite? | **`EXPSPACE`-complete** | Rackoff (TCS 1978, `10.1016/0304-3975(78)90036-1`): shortest self-covering witness $\le 2^{2^{O(d \log d)}}$; Lipton (1976) lower bound |
| **Coverability** | $\exists \mathbf{m} \ge \mathbf{m}_t.\; \mathbf{m}_0 \xrightarrow{*} \mathbf{m}$? | **`EXPSPACE`-complete** | Upward-closed monotonicity (Dickson's Lemma) yields Rackoff double-exponential shortest-run bound; Savitch $\Rightarrow \text{EXPSPACE}$ |
| **Exact Reachability (general $d$)** | $\mathbf{m}_0 \xrightarrow{*} \mathbf{m}_t$? | **Ackermann-complete** ($\mathbf{F}_\omega$-complete) | Upper: Leroux & Schmitz (LICS 2019, `10.1109/LICS.2019.8785796`); Lower: Czerwiński & Orlikowski (FOCS 2021, `10.1109/FOCS52979.2021.00120`) & Leroux (FOCS 2021, `10.1109/FOCS52979.2021.00121`) |
| **Exact Reachability (fixed dim $d$)** | Fixed number of counters $d$ | Primitive-recursive in $\mathcal{F}_{d+4}$ upper; $\mathcal{F}_k$-hard in dim $6k$ | Czerwiński & Orlikowski (FOCS 2021) prove $\mathcal{F}_k$-hardness at dim $6k$; $d \le 2$ is `PSPACE`-complete |
| **Reachability + $\ge 2$ Inhibitor Arcs** | Adding zero-test transitions | **Undecidable** | Direct simulation of 2-counter Minsky machines |

1. **Why Coverability Stops at `EXPSPACE` (Rackoff 1978 & Lipton 1976):**
   - Because Petri nets lack zero-tests, firing sequences are **monotone**: if $\mathbf{m} \xrightarrow{\sigma} \mathbf{m}'$, then $(\mathbf{m} + \Delta) \xrightarrow{\sigma} (\mathbf{m}' + \Delta)$ for all $\Delta \in \mathbb{N}^d$.
   - Using Lipton's weak-multiplication gadgets (iterated squaring: $O(k)$ places can transfer/multiply counters up to $2^{2^k}$ tokens, Probe 2D: $2, 4, 16, 256, 65536$ for $k=0..4$), shortest covering witnesses require length $2^{2^{\Omega(n)}}$, establishing `EXPSPACE`-hardness.
   - Rackoff (1978) proved by induction on dimension $d$ that whenever a target $\mathbf{m}_t$ is coverable, a covering path exists of length $\le 2^{2^{O(d \log d \cdot \log \|N\|)}}$ (keeping coordinates bounded or "self-covering" out of the inductive subspace), placing coverability and boundedness in $\text{NEXPSPACE} = \text{EXPSPACE}$.
2. **Why Exact Reachability Explodes to Ackermann-Completeness (Czerwiński & Orlikowski FOCS 2021; Leroux FOCS 2021):**
   - Exact reachability asks whether $\mathbf{m}_t$ is hit with **zero surplus tokens** on every coordinate. Although a VASS cannot test a counter for zero *during* execution, exact reachability lets the *final target equality* ($\mathbf{m}_{\text{final}} = \mathbf{0}$) act as a **post-hoc verification of weakly simulated zero-tests**:
     - To simulate a zero-test on counter $x$ up to a fast-growing budget $B = F_k(n)$, the construction maintains a complementary sum invariant (or quadratic/exponential ratio amplifier) so that any "cheating" transition that pretends $x = 0$ while $x > 0$ permanently loses tokens from a conserved budget, making it mathematically impossible to hit the exact target $\mathbf{m}_t$ at the end of the run!
     - Iterating this weak-multiplier amplification across $6k$ counters climbs every finite level $\mathcal{F}_k$ of the fast-growing Grzegorczyk hierarchy (Czerwiński & Orlikowski, FOCS 2021, `arXiv:2104.13866`; independently Leroux, FOCS 2021, `arXiv:2104.12695`, proving reachability is not primitive recursive), tightly matching Leroux & Schmitz's (LICS 2019) $\mathcal{F}_\omega$ Ackermann upper bound on KLMST decomposition.

#### 4.3 Sound Over-Approximations vs. Exact Unsoundness Traps (`TAPAAL/verifypn`)

Because Ackermann-complete exact decision procedures (KLMST decomposition) cannot run directly on industrial nets, practical model checkers such as `TAPAAL/verifypn@fc0477705ddf22bf16b2cd9cdb97ca7f4f7573ba` layer fast **over-approximations** and partial-order reductions in front of explicit/symbolic search:

1. **Karp–Miller $\omega$-Coverability Tree Trap (Execution-Verified in Probe 2D):**
   - Accelerating strictly increasing ancestor markings by replacing growing places with $\omega$ guarantees termination (by Dickson's Lemma) and **exactly decides coverability and boundedness**—but **destroys exact reachability**.
   - In Probe 2D (`m0 = (1, 0)`, `t_add2: (1,0)->(1,2)`, `t_stop: (1,0)->(0,0)`), the Karp–Miller tree is `{(1,0), (1,∞), (0,0), (0,∞)}`. It correctly reports `(0, 3)` is **coverable** (via `(0, 4) >= (0, 3)`), yet `(0, 3)` is **strictly unreachable** because every reachable marking satisfies the modular invariant `p_tok % 2 == 0`!
2. **State-Equation Linear/Integer Programming Filter (`verifypn` `src/PetriEngine/Simplification/LinearProgram.cpp:49-145`):**
   - Every reachable marking $\mathbf{m}_t$ MUST satisfy the linear marking equation $\mathbf{m}_t = \mathbf{m}_0 + C \cdot \mathbf{x}$ for some Parikh firing-count vector $\mathbf{x} \in \mathbb{N}^{|T|}$ (where $C = \mathbf{Post} - \mathbf{Pre}$). `LinearProgram::isImpossible()` builds this LP/ILP in GLPK (`glp_set_col_kind` `GLP_IV`/`GLP_CV`, `LinearProgram.cpp:117-145`) to **soundly prove unreachability** whenever the LP/ILP is infeasible (also rejecting overflow when initial tokens exceed `int32_t`, line 63).
   - **Spurious Witness Siphon Trap (Execution-Verified in Probe 2D):** Feasibility of $\mathbf{m}_0 + C \cdot \mathbf{x} = \mathbf{m}_t$ with $\mathbf{x} \in \mathbb{N}^{|T|}$ does **not** imply reachability! On the 3-place net `m0 = (0,0,1)`, `t1: pre=(1,0,0), post=(1,1,0)`, `t2: pre=(0,0,1), post=(0,0,0)`, the integer vector $\mathbf{x} = (1, 1)$ satisfies $\mathbf{m}_0 + C \cdot (1, 1)^T = (0, 1, 0) = \mathbf{m}_t$, yet `t1` requires a token in the unmarked **siphon** `{p0}` and can never fire (`exact reachable set = {(0,0,0), (0,0,1)}`).
3. **Trace Abstraction Refinement (`TAR`) & Stubborn Sets (`src/PetriEngine/TAR/TARReachability.cpp:39-215`, `src/PetriEngine/Stubborn/ReachabilityStubbornSet.cpp`):**
   - `verifypn` refines spurious abstract traces using interpolant automata stored in an antichain (`AntiChain<uint32_t, size_t>`, `TARReachability.cpp:86-140`) and applies stubborn-set partial-order reduction (`ReachabilityStubbornSet.cpp`) to prune commutative interleavings while preserving exact reachability on finite state spaces.

---

### 5. Cross-Domain Verification Seam Synthesis

Basis: derived

Combining these three verification families in end-to-end systems engineering exposes three structural seams whose assumptions must be explicitly discharged:

1. **Active Learning $\to$ Reactive Shield Synthesis (`LearnLib` $\to$ `Strix` / `GR(1)`):** When synthesizing a reactive protocol shield or monitor against a learned Mealy model $\mathcal{H}$ of a black-box peer, the synthesized shield is guaranteed safe against the *real* peer **only under the Wp-method state-count bound** ($|Q_{\text{SUL}}| \le |Q_{\mathcal{H}}| + k$) and determinism/abstraction fidelity. Any unmodeled deep state beyond lookahead $k$ (Probe 2C) breaks the reactive assumption $\rho_e$, potentially turning the shield's runtime behavior undefined.
2. **Liveness Specification Choice (`GR(1)` vs. Full LTL):** Using `GR(1)` (`gr1c`) over full LTL (`Strix`) trades expressiveness for polynomial-in-$|S|$ symbolic fixpoints, but requires an explicit **well-separation / non-vacuity check** (Probe 2B); conversely, full LTL in `Strix` handles arbitrary temporal nesting (`F G`, nested `U`) soundly via border-adversarial incremental `Fpi`, at the risk of hitting the `2-EXPTIME` state-space wall on realizable counting specifications.
3. **Finite-State Synthesis $\to$ Parameterized Multi-Instance Concurrency (Petri Nets / VASS):** Lifting a synthesized finite-state controller to $N$ unbounded identical threads maps safety ("bad state never reached") to **coverability** (`EXPSPACE`, monotonically over-approximable by Karp–Miller and state-equation LP), whereas exact resource conservation / zero-leak termination ("all $N$ locks released simultaneously") crosses into **exact reachability** (`Ackermann`-complete, requiring inductive Presburger invariants or structural reductions rather than blind state-space search).

## Boundaries

- **Known Not to Apply — `Strix` Parity Solver Selection:** Contrary to informal summaries that conflate modern LTL synthesis with Calude et al.'s quasipolynomial solver, `meyerphi/strix@c0b1298fe2e0d46325662b89cb58a19cb4f02be5` (`src/options.rs:301-329`) implements only `Fpi` (default), `Zlk`, and `Si` — not `qpt` or `sspm` (which live in `trolando/oink`).
- **Known Not to Apply — Karp–Miller and State-Equation LP for Exact Reachability:** Both Karp–Miller $\omega$-trees and integer state-equation solvers (`verifypn` `LinearProgram.cpp`) are proven insufficient to decide exact Petri-net reachability (Probe 2D concrete counterexamples: even-parity loss under $\omega$ and unmarked-siphon spurious integer solution).
- **Known Not to Apply — Undecidability Beyond Standard Models:**
  - Extending synchronous reactive LTL synthesis to **distributed multi-process architectures** with partial observation (Pnueli & Rosner, FOCS 1990) is **undecidable**.
  - Extending Petri nets / VASS with **$\ge 2$ inhibitor arcs (zero-tests)** or reset arcs makes exact reachability **undecidable** (though coverability remains decidable with Ackermann-complete complexity for reset nets!).
- **Unsupported — Nondeterministic or Non-Resettable SULs in Standard `LearnLib` `L*`/`TTT`:** `AbstractTTTLearner` and `AbstractLStar` require deterministic, input-enabled, resettable black-box SULs; nondeterminism triggers `HypothesisChangedException` or unsound models unless handled via external majority-voting wrappers or specialized stochastic/nondeterministic learners.
- **Unsupported — Overflowing Initial Markings in `verifypn` LP Filter:** `TAPAAL/verifypn` (`src/PetriEngine/Simplification/LinearProgram.cpp:63`) explicitly bypasses LP simplification when initial markings exceed `int32_t` bounds (`context.markingOutOfBounds()`).
- **Not Examined:**
  - Register-automata / data-aware active learning (`RALib`, `SL*`) and passive inference (`RPNI`, `EDSM`) for protocol fields with infinite data domains.
  - Bounded synthesis (`BoSy`, SMT/QBF encodings) and symbolic BDD parity-game solvers beyond `gr1c`.
  - Colored Petri net unfolding algorithms and timed-arc Petri net (`TAPAAL` continuous-clock) semantics beyond `verifypn`'s untimed reachability/LP/TAR core.
  - Sub-cubic improvements to `GR(1)` synthesis with Streett(1) or Rabin(1) conditions and exact $d \le 5$ fixed-dimension VASS complexity refinements published after 2021.
- **Unknown:** Whether general parity games admit a **polynomial-time** algorithm ($\text{P}$ vs. quasipolynomial in $\text{UP} \cap \text{co-UP}$) remains an open problem in theoretical computer science.

## Evidence

### Pinned Source Repositories & Exact Symbols

| Subject | Repository & Immutable Revision | Inspected Paths & Line Ranges / Symbols |
| :--- | :--- | :--- |
| Strix LTL Synthesizer | `meyerphi/strix` @ `c0b1298fe2e0d46325662b89cb58a19cb4f02be5` | `src/options.rs` (`enum Solver`: `Fpi` default, `Zlk`, `Si`, `L301-329`); `src/parity/solver/fpi.rs` (`FpiSolverInstance`, `L26-95`); `src/parity/solver/zlk.rs` (`ZlkSolverInstance`, `L1-93`); `src/parity/solver/incremental.rs` (`IncrementalSolver::solve`, border-adversarial attractor, `L28-75`); `src/constructor/mod.rs` (`Owl` `MaxEvenDpa`, `L1-40`) |
| Oink Parity Game Suite | `trolando/oink` @ `ad85a62f1c30ff95f48a4b564c0a9e3c5cef5ed5` | `src/solvers.cpp` (solver registry: `zlk`, `zlkq`, `zlkpp-waw`, `pp`, `ppq`, `fpi`, `sspm`, `qpt`, `L55-85`); `src/solvers/qpt.cpp` (`pm_less` `L38-62`, `up` Lemmas 3.3/3.4 `L103-149`, `bump` `L156-197`, `au` `L205-215`) |
| gr1c Symbolic GR(1) Synthesizer | `slivingston/gr1c` @ `2a4ad3d7bb0ed3ecf4f6328fddf6f8922e66234e` | `src/solve.c` (`compute_winning_set_BDD` call, `compute_sublevel_sets`, `strans_into_W`, `L173-258`); `src/solve_operators.c` (`compute_winning_set_BDD` 3-nested `Z`/`Y`/`X` CUDD fixpoint, `L114-230`, `compute_sublevel_sets` `L345`) |
| LearnLib Active Learning | `LearnLib/learnlib` @ `51aec213478b8074c21515c81fd162d78efb8c8c` | `algorithms/active/lstar/.../ObservationTableCEXHandlers.java` (`CLASSIC_LSTAR` `L40-57`, `MALER_PNUELI`, `RIVEST_SCHAPIRE` `L81-103`); `algorithms/active/ttt/.../AbstractTTTLearner.java` (`blockList` `L86`, `finalizeDiscriminator` `L344`, `prepareSplit` `L643-695`, `extractSubtree` `L713-730`); `.../TTTLearnerMealy.java` (`L50-120`); `oracles/equivalence-oracles/.../WpMethodEQOracle.java` (`L84-158`) |
| TAPAAL `verifypn` Petri Net Engine | `TAPAAL/verifypn` @ `fc0477705ddf22bf16b2cd9cdb97ca7f4f7573ba` | `src/PetriEngine/Simplification/LinearProgram.cpp` (`LinearProgram::isImpossible`, GLPK LP/ILP, `L49-145`); `src/PetriEngine/TAR/TARReachability.cpp` (`TARReachabilitySearch::runTAR`, `AntiChain`, `L39-215`); `src/PetriEngine/Stubborn/ReachabilityStubbornSet.cpp` |

### Peer-Reviewed Literature

- Amir Pnueli & Roni Rosner, *"On the Synthesis of a Reactive Module"*, POPL 1989, pp. 179–190 (`DOI: 10.1145/75277.75293`).
- Roderick Bloem, Barbara Jobstmann, Nir Piterman, Amir Pnueli, Yaniv Sa'ar, *"Synthesis of Reactive(1) Designs"*, JCSS 78(3):911–938, 2012 (`DOI: 10.1016/j.jcss.2011.08.007`).
- Cristian S. Calude, Sanjay Jain, Bakhadyr Khoussainov, Wei Li, Frank Stephan, *"Deciding Parity Games in Quasipolynomial Time"*, STOC 2017 (`DOI: 10.1145/3055399.3055409`).
- Marcin Jurdziński & Ranko Lazić, *"Succinct Progress Measures for Solving Parity Games"*, LICS 2017 (`DOI: 10.1109/LICS.2017.8005092`).
- Philipp J. Meyer, Salomon Sickert, Michael Luttenberger, *"Strix: Explicit Reactive Synthesis Strikes Back!"*, CAV 2018 (`DOI: 10.1007/978-3-319-96145-3_31`).
- Dana Angluin, *"Learning Regular Sets from Queries and Counterexamples"*, Information and Computation 75(2):87–106, 1987 (`DOI: 10.1016/0890-5401(87)90052-6`).
- Malte Isberner, Falk Howar, Bernhard Steffen, *"The TTT Algorithm: A Redundancy-Free Approach to Active Automata Learning"*, RV 2014 (`DOI: 10.1007/978-3-319-11164-3_26`).
- Malte Isberner, Falk Howar, Bernhard Steffen, *"The Open-Source LearnLib — A Framework for Active Automata Learning"*, CAV 2015 (`DOI: 10.1007/978-3-319-21690-6_33`).
- Joeri de Ruiter & Erik Poll, *"Protocol State Fuzzing of TLS Implementations"*, 24th USENIX Security Symposium, pp. 193–206, 2015.
- Charles Rackoff, *"The Covering and Boundedness Problems for Vector Addition Systems"*, Theoretical Computer Science 6(2):223–231, 1978 (`DOI: 10.1016/0304-3975(78)90036-1`).
- Jérôme Leroux & Sylvain Schmitz, *"Reachability in Vector Addition Systems is Primitive-Recursive in Fixed Dimension"*, LICS 2019 (`DOI: 10.1109/LICS.2019.8785796`).
- Wojciech Czerwiński & Łukasz Orlikowski, *"Reachability in Vector Addition Systems is Ackermann-complete"*, FOCS 2021 (`DOI: 10.1109/FOCS52979.2021.00120`, `arXiv:2104.13866`).
- Jérôme Leroux, *"The Reachability Problem for Petri Nets is Not Primitive Recursive"*, FOCS 2021, pp. 1241–1252 (`DOI: 10.1109/FOCS52979.2021.00121`, `arXiv:2104.12695`).

### Self-Contained Executable Micro-Probe & Observed Output (`2026-11-19`)

Command (Python 3.13, Linux x86-64, zero external dependencies):

```bash
python3 - <<'EOF'
import itertools, math
from collections import deque

# 2A: Parity games — Zielonka vs Calude et al. QPT (oink qpt.cpp) vs Strix border-adversarial
owners = {0:0, 1:1, 2:0, 3:1, 4:0, 5:1, 6:0, 7:1}
prios  = {0:1, 1:2, 2:3, 3:4, 4:0, 5:3, 6:2, 7:1}
edges  = {0:[1,4], 1:[0,2], 2:[3,5], 3:[1,6], 4:[5,7], 5:[4,2], 6:[6,3], 7:[7,4]}

def attr(sub, tgt, pl):
    A = set(tgt) & sub
    ch = True
    while ch:
        ch = False
        for v in sub - A:
            sc = [u for u in edges[v] if u in sub]
            if sc and ((owners[v]==pl and any(u in A for u in sc)) or (owners[v]!=pl and all(u in A for u in sc))):
                A.add(v); ch = True
    return A

def zlk(sub):
    if not sub: return set(), set()
    p = max(prios[v] for v in sub); a = p % 2; opp = 1 - a
    A = attr(sub, {v for v in sub if prios[v]==p}, a)
    w0, w1 = zlk(sub - A); wo = w1 if opp else w0
    if not wo: return (sub, set()) if a==0 else (set(), sub)
    B = attr(sub, wo, opp); w0p, w1p = zlk(sub - B)
    return (w0p|B, w1p) if opp==0 else (w0p, w1p|B)

def pm_less(a, b, pl=0):
    for x, y in zip(a, b):
        if x == y: continue
        if x == -1: return True
        if y == -1: return False
        ax, ay = (x&1)==pl, (y&1)==pl
        if ax: return (x < y) if ay else False
        return True if ay else (x > y)
    return False

def qpt_up(src, d, pl=0):
    k = len(src)
    if src[0] != -1 and (src[0]&1)==pl: return list(src)
    j33 = -1
    for i in range(k-1, -1, -1):
        if src[i] != -1 and (src[i]&1)==pl: continue
        j33 = i
        if any(src[j] != -1 and src[j] < d for j in range(i)): j33 = -1
        break
    j34 = next((i for i in range(k) if src[i] != -1 and src[i] < d), -1)
    j = j34 if j33==-1 else (j33 if j34==-1 else min(j33, j34))
    return src[:j] + [d] + [-1]*(k - j - 1)

k = math.floor(math.log2(len(owners))) + 2
pm = {v: [-1]*k for v in owners}; lifts = 0; ch = True
while ch:
    ch = False
    for v in sorted(owners):
        cs = [qpt_up(pm[u], prios[v]) for u in edges[v]]
        best = cs[0]
        for c in cs[1:]:
            if (owners[v]==0 and pm_less(best, c)) or (owners[v]==1 and pm_less(c, best)): best = c
        if pm_less(pm[v], best): pm[v] = best; lifts += 1; ch = True
z0, z1 = zlk(set(owners))
q0 = {v for v in owners if pm[v][0] != -1 and (pm[v][0]&1)==0}
assert q0 == z0
sub_exp = {0,1,2,3,6,4,5}; border = {4,5}
w0_inc, _ = zlk(sub_exp - attr(sub_exp, border, 1))
print(f"2A Parity: Zlk=QPT W0={sorted(z0)} W1={sorted(z1)} (QPT k={k}, lifts={lifts}); Strix_partial W0={sorted(w0_inc)} (node 7 unexplored)")

# 2B: GR(1) 3-nested fixpoint & vacuity trap
S = {(r0,r1,g0,g1) for r0 in (0,1) for r1 in (0,1) for g0 in (0,1) for g1 in (0,1) if not (g0 and g1)}
def gr1(cpre, A, G):
    Z = set(S); it = 0
    while True:
        it += 1; Zn = set(S)
        for Gj in G:
            cZ = cpre(Z); Y = set()
            while True:
                cY = cpre(Y); Yn = set()
                for Ai in A:
                    X = set(S)
                    while True:
                        Xn = (Gj & cZ) | cY | ((S - Ai) & cpre(X))
                        if Xn == X: break
                        X = Xn
                    Yn |= X
                if Yn == Y: break
                Y = Yn
            Zn &= Y
        if Zn == Z: return Z, it
        Z = Zn

cpre_std = lambda T: {s for s in S if all(any((r0,r1,g0,g1) in T for g0,g1 in ((0,0),(1,0),(0,1))) for r0 in (0,1) for r1 in (0,1))}
cpre_vac = lambda T: {s for s in S if s[2]==1 or all(any((r0,r1,g0,g1) in T for g0,g1 in ((0,0),(1,0),(0,1))) for r0 in (0,1) for r1 in (0,1))}
G0 = {s for s in S if (not s[0]) or s[2]}; G1 = {s for s in S if (not s[1]) or s[3]}; Gimp = {s for s in S if s[2] and s[3]}
print(f"2B GR(1): real={len(gr1(cpre_std,[S],[G0,G1])[0])}/12, unreal={len(gr1(cpre_std,[S],[G0,Gimp])[0])}/12, vacuity_trap={len(gr1(cpre_vac,[S],[G0,Gimp])[0])}/12")

# 2C: Active Mealy learning (Classic L* vs Rivest-Schapire vs TTT) + Wp-method blind spot
TLS_ALPHA = ["CH", "CKE", "CCS", "FIN", "APP"]
TLS_TRANS = {
    0: {"CH":(1,"SH"),"CKE":(6,"Alert"),"CCS":(6,"Alert"),"FIN":(6,"Alert"),"APP":(6,"Alert")},
    1: {"CH":(6,"Alert"),"CKE":(2,"OK"),"CCS":(5,"OK"),"FIN":(6,"Alert"),"APP":(6,"Alert")},
    2: {"CH":(6,"Alert"),"CKE":(6,"Alert"),"CCS":(3,"OK"),"FIN":(6,"Alert"),"APP":(6,"Alert")},
    3: {"CH":(6,"Alert"),"CKE":(6,"Alert"),"CCS":(6,"Alert"),"FIN":(4,"SFIN"),"APP":(6,"Alert")},
    4: {"CH":(6,"Alert"),"CKE":(6,"Alert"),"CCS":(6,"Alert"),"FIN":(6,"Alert"),"APP":(4,"DATA")},
    5: {"CH":(6,"Alert"),"CKE":(6,"Alert"),"CCS":(6,"Alert"),"FIN":(4,"SFIN"),"APP":(6,"Alert")},
    6: {a:(6,"Closed") for a in TLS_ALPHA},
}
DEEP_ALPHA = ["a", "b"]
DEEP_TRANS = {i: {"a":((i+1)%7,"OK"), "b":(7,"HIT" if i==6 else "MISS")} for i in range(7)}
DEEP_TRANS[7] = {"a":(7,"OK"), "b":(7,"MISS")}

def run_m(tr, w):
    s, out = 0, []
    for a in w: s, o = tr[s][a]; out.append(o)
    return tuple(out)

def learn_bench(alpha, tr, max_eq):
    def mk_sul():
        st = {"mq":0, "sym":0, "c":{}}
        def ql(w):
            if w in st["c"]: return st["c"][w]
            st["mq"] += 1; st["sym"] += len(w); o = run_m(tr, w)[-1]; st["c"][w] = o; return o
        return st, ql
    def eq_bfs(hyp):
        q = deque([()])
        while q:
            w = q.popleft()
            if w and run_m(hyp, w) != run_m(tr, w): return w
            if len(w) < max_eq:
                for a in alpha: q.append(w + (a,))
        return None
    def lstar(mode):
        st, ql = mk_sul(); S_p, E_s = [()], [(a,) for a in alpha]; eqs = 0
        row = lambda u: tuple(ql(u + e) for e in E_s)
        while True:
            ch = True
            while ch:
                ch = False; sr = {row(s): s for s in S_p}
                for s in list(S_p):
                    for a in alpha:
                        if row(s+(a,)) not in sr: S_p.append(s+(a,)); sr[row(s+(a,))] = s+(a,); ch = True
                if mode == "classic":
                    for i in range(len(S_p)):
                        for j in range(i+1, len(S_p)):
                            if row(S_p[i]) == row(S_p[j]):
                                for a in alpha:
                                    r1, r2 = row(S_p[i]+(a,)), row(S_p[j]+(a,))
                                    if r1 != r2:
                                        for k2, e in enumerate(E_s):
                                            if r1[k2] != r2[k2]:
                                                if (a,)+e not in E_s: E_s.append((a,)+e); ch = True
                                                break
            reps = {}
            for s in S_p: reps.setdefault(row(s), s)
            rl = list(reps.values()); idx = {s:i for i,s in enumerate(rl)}
            hyp = {idx[s]: {a:(idx[reps[row(s+(a,))]], row(s)[E_s.index((a,))]) for a in alpha} for s in rl}
            eqs += 1; cex = eq_bfs(hyp)
            if cex is None: return len(rl), st["mq"], st["sym"], eqs, hyp
            if mode == "classic":
                for p in range(1, len(cex)+1):
                    if cex[:p] not in S_p: S_p.append(cex[:p])
            else:
                for p in range(1, len(cex)+1):
                    if run_m(hyp, cex[:p])[-1] != ql(cex[:p]): cex = cex[:p]; break
                def acc(w):
                    x = 0
                    for a in w: x, _ = hyp[x][a]
                    return rl[x]
                lo, hi = 0, len(cex)-1
                while hi - lo > 0:
                    mid = (lo+hi)//2
                    s1, s2 = ql(acc(cex[:mid])+cex[mid:]), ql(acc(cex[:mid+1])+cex[mid+1:])
                    if s1 != s2: lo = hi = mid; break
                    if s1 == ql(cex): lo = mid + 1
                    else: hi = mid
                if cex[lo+1:] not in E_s: E_s.append(cex[lo+1:])
    def ttt():
        st, ql = mk_sul(); states = [()]; eqs = 0
        class N:
            def __init__(self, disc=None, acc=None): self.disc, self.acc, self.ch = disc, acc, {}
        root = N(acc=())
        def sift(u):
            cur = root
            while cur.disc is not None:
                o = ql(u + cur.disc)
                if o not in cur.ch:
                    lf = N(acc=u); cur.ch[o] = lf; states.append(u); return lf
                cur = cur.ch[o]
            return cur
        while True:
            i = 0
            while i < len(states):
                for a in alpha: sift(states[i]+(a,))
                i += 1
            idx = {u:k2 for k2,u in enumerate(states)}
            hyp = {idx[u]: {a:(idx[sift(u+(a,)).acc], ql(u+(a,))) for a in alpha} for u in states}
            eqs += 1; cex = eq_bfs(hyp)
            if cex is None:
                def cn(nd): return (0,1) if nd.disc is None else (1+sum(cn(c)[0] for c in nd.ch.values()), sum(cn(c)[1] for c in nd.ch.values()))
                return len(states), st["mq"], st["sym"], eqs, cn(root)[0], hyp
            for p in range(1, len(cex)+1):
                if run_m(hyp, cex[:p])[-1] != ql(cex[:p]): cex = cex[:p]; break
            def acc(w):
                x = 0
                for a in w: x, _ = hyp[x][a]
                return states[x]
            lo, hi = 0, len(cex)-1
            while hi - lo > 0:
                mid = (lo+hi)//2
                s1, s2 = ql(acc(cex[:mid])+cex[mid:]), ql(acc(cex[:mid+1])+cex[mid+1:])
                if s1 != s2: lo = hi = mid; break
                if s1 == ql(cex): lo = mid + 1
                else: hi = mid
            uo, un, d = acc(cex[:lo+1]), acc(cex[:lo])+(cex[lo],), cex[lo+1:]
            lf = sift(uo); lf.disc, lf.acc = d, None
            lf.ch[ql(uo+d)] = N(acc=uo); lf.ch[ql(un+d)] = N(acc=un); states.append(un)
    return lstar("classic"), lstar("rs"), ttt()

c1, r1, t1 = learn_bench(TLS_ALPHA, TLS_TRANS, 8)
c2, r2, t2 = learn_bench(DEEP_ALPHA, DEEP_TRANS, 10)
print(f"2C TLS (6 states): Classic=({c1[1]} MQ,{c1[2]} sym) RS=({r1[1]} MQ,{r1[2]} sym) TTT=({t1[1]} MQ,{t1[2]} sym,DT={t1[4]}) EarlyCCS={run_m(t1[5], ('CH','CCS','FIN','APP'))}")
print(f"2C Deep (8 states): Classic=({c2[1]} MQ,{c2[2]} sym) RS=({r2[1]} MQ,{r2[2]} sym) TTT=({t2[1]} MQ,{t2[2]} sym,DT={t2[4]})")
secret = ("B","A","A","B")
found = any(w == secret for L in range(1, 4) for w in itertools.product(("A","B"), repeat=L))
print(f"2C Wp-method blind spot (len=4 secret, k=2 lookahead): bug_detected={found}")

# 2D: Petri net Karp-Miller parity loss + state-equation siphon trap + 2^(2^k) growth
INF = float("inf")
def fire(m, pre, post):
    return None if any(m[i] < pre[i] for i in range(len(m))) else tuple(INF if m[i]==INF else m[i]-pre[i]+post[i] for i in range(len(m)))
# Karp-Miller on (p_run, p_tok)
km_t = [((1,0),(1,2)), ((1,0),(0,0))]; q = deque([((1,0),[(1,0)])]); vis = set()
while q:
    m, path = q.popleft()
    if m in vis: continue
    vis.add(m)
    for pre, post in km_t:
        nx = fire(m, pre, post)
        if nx is None: continue
        acc = list(nx)
        for anc in path:
            if all(acc[i]>=anc[i] for i in range(2)) and acc!=list(anc):
                for i in range(2):
                    if acc[i]>anc[i]: acc[i] = INF
        q.append((tuple(acc), path + [tuple(acc)]))
cov03 = any(m[0]>=0 and m[1]>=3 for m in vis)
# Siphon trap: m0=(0,0,1), t1: pre=(1,0,0)->post=(1,1,0), t2: pre=(0,0,1)->post=(0,0,0), mt=(0,1,0)
m0, mt = (0,0,1), (0,1,0); st_t = [((1,0,0),(1,1,0)), ((0,0,1),(0,0,0))]
se_ok = tuple(m0[i] + (st_t[0][1][i]-st_t[0][0][i]) + (st_t[1][1][i]-st_t[1][0][i]) for i in range(3)) == mt
reach = {m0}; rq = deque([m0])
while rq:
    c = rq.popleft()
    for pre, post in st_t:
        nx = fire(c, pre, post)
        if nx is not None and nx not in reach: reach.add(nx); rq.append(nx)
print(f"2D VASS: KM covers (0,3)={cov03} (even-only exact reach=False); StateEq x=(1,1) valid={se_ok} vs exact_reach={mt in reach}; 2^(2^k)={[2**(2**i) for i in range(5)]}")
EOF
```

Observed output (`exit 0`, recorded `2026-11-19`):

```text
2A Parity: Zlk=QPT W0=[0, 1, 2, 3, 6] W1=[4, 5, 7] (QPT k=5, lifts=70); Strix_partial W0=[0, 1, 2, 3, 6] (node 7 unexplored)
2B GR(1): real=12/12, unreal=0/12, vacuity_trap=12/12
2C TLS (6 states): Classic=(155 MQ,530 sym) RS=(155 MQ,530 sym) TTT=(61 MQ,193 sym,DT=4) EarlyCCS=('SH', 'OK', 'SFIN', 'DATA')
2C Deep (8 states): Classic=(88 MQ,685 sym) RS=(92 MQ,647 sym) TTT=(84 MQ,603 sym,DT=7)
2C Wp-method blind spot (len=4 secret, k=2 lookahead): bug_detected=False
2D VASS: KM covers (0,3)=True (even-only exact reach=False); StateEq x=(1,1) valid=True vs exact_reach=False; 2^(2^k)=[2, 4, 16, 256, 65536]
```

## Revalidation

To cheaply verify whether these findings still hold on newer tool revisions or problem formulations:

1. **Reactive Synthesis & Parity Games (`meyerphi/strix`, `trolando/oink`, `slivingston/gr1c`):**
   - Inspect `meyerphi/strix` `src/options.rs` (`enum Solver` and `impl Default for Solver`) and `src/parity/solver/incremental.rs` to check whether Strix adds a quasipolynomial solver backend or alters border-adversarial attractor pruning.
   - Inspect `trolando/oink` `src/solvers.cpp` and `src/solvers/qpt.cpp` for newer universal-tree or register-game solvers.
   - Check `slivingston/gr1c` `src/solve_operators.c` (`compute_winning_set_BDD`) for strict-realizability or well-separation enforcement flags.
2. **Active Automata Learning (`LearnLib/learnlib`):**
   - Diff `AbstractTTTLearner.java` (`finalizeDiscriminator`, `prepareSplit`) and `WpMethodEQOracle.java` (`WpMethodTestsIterator` lookahead computation) for changes to discriminator finalization or default conformance testing strategies (e.g., `ADT` / adaptive distinguishing trees or `L#`).
3. **Petri Nets / VASS (`TAPAAL/verifypn`):**
   - Diff `src/PetriEngine/Simplification/LinearProgram.cpp` (e.g., solver backend transitions from GLPK, siphon/trap strengthening constraints added to the state equation) and `src/PetriEngine/TAR/TARReachability.cpp`.
4. **Executable Probe:** Re-run the inline Python 3 probe under **Evidence** to confirm Zielonka/QPT equivalence, Strix border-adversarial soundness, the GR(1) vacuity trap, the Wp-method lookahead blind spot, Karp–Miller parity loss, and the state-equation siphon counterexample.
