# Decidable Distributed Protocol Verification and Formally Safe Live Consensus Migration

## Summary

Verifying unbounded-node distributed consensus protocols and live cluster/protocol migrations splits cleanly along two axes: **what makes inductive invariant checking decidable** (avoiding SMT quantifier-instantiation divergence) and **what quorum-intersection and state-transfer invariants prevent split-brain during live membership or protocol transitions**.

1. **Decidability Razor in First-Order Verification (`Ivy` / `FEU` / `FAU` / `EPR`):** Unbounded-node Paxos safety is decidable (and yields finite counter-models on invariant failure) not merely in pure Bernays–Schönfinkel–Ramsey EPR (`∃*∀*` without functions), but in the **Finite Almost Uninterpreted (`FAU`)** fragment enforced statically by `kenmcmil/ivy` (`ivy/ivy_fragment.py`). `FAU` builds a union-find **stratification graph** over universal variables `S_v`, uninterpreted argument positions `A_{f,j}`, uninterpreted-sort equality classes `S_σ`, and Skolem dependencies from `∀u. ∃w` quantifier alternations, permitting interpreted integer operators *only* in positive arithmetic literals (`X < Y`, `X < t`, `t < X`, `X = t` with ground `t`). A single cyclic function symbol (such as `next_round : round -> round`), a dual `∀∃` sort cycle (`quorum -> node -> quorum`), or an arithmetic offset (`R + 1`) under a universal quantifier immediately breaches `FAU` and reintroduces unbounded Herbrand instantiation.
2. **Threshold Automata & Cutoff Theorems (`ByMC` / `Marić–Sprenger–Basin`):** When protocols rely on arithmetic message-count quorums (`t < n/3`, `≥ n - t`, `≥ 2t + 1`) that cannot stay in uninterpreted `FAU`, **threshold automata (`ByMC`)** achieve decidable parameterized safety and liveness verification via a **short counterexample property** (Konnov et al., POPL 2017) bounding counterexample schema length by the number of threshold guards rather than process count `n`. Independently, consensus-specific cutoff theorems (Marić, Sprenger, Basin, CAV 2017) reduce parameterized safety for round-based Heard-Of algorithms to finite `n`-process checks, though only for restricted synchronization structures.
3. **Interactive Refinement vs. Proof-Assistant Composition (`IronFleet` vs. `Verdi`):** End-to-end executable implementations cross outside decidable fragments into arithmetic, serialization, and concrete I/O. `IronFleet` (`microsoft/Ironclad`) bridges this in Dafny/Z3 via three refinement layers (TLA-style high-level spec → distributed protocol → verified imperative implementation) plus explicit real-time TLA fairness assumptions for liveness, accepting brittle SMT trigger tuning. `Verdi` (`uwplse/verdi`, `uwplse/verdi-raft`) avoids SMT instability in Coq by factoring fault-model proofs through **Verified System Transformers (VSTs)** and proving Raft end-to-end linearizability via ~90 modular invariant interfaces, trading SMT automation for manual proof engineering.
4. **Live Consensus Reconfiguration & Protocol Migration Safety:** Changing voting quorums or consensus algorithms without stop-the-world quiescence requires preserving quorum intersection across **every pair of concurrently active configurations or epochs**, plus transferring all previously committed decisions across the boundary:
   - **Raft Single-Server Bug (Ongaro 2015):** Effective-on-append single-server membership changes (`|C_new Δ C_old| = 1`) still violate **Election Safety** and **Leader Completeness** in a 4-server cluster (`C_0 = {0,1,2,3}`) if two leaders in different terms append conflicting single-server removals (`{0,2,3}` vs. `{1,2,3}`) before committing an entry in their current terms—reproduced in 6 steps / 3,941 BFS states (`Basis: execution`). Requiring a leader to commit at least one entry in its current term (or activating configuration changes only at apply time with `pendingConfIndex`, as in `etcd-io/raft`) eliminates the violation across all 59,617 explored states.
   - **Joint Consensus (`etcd-io/raft`), Logless Decoupling (`MongoRaftReconfig`), and Auxiliary Masters (`Vertical Paxos` / `Matchmaker Paxos`):** Arbitrary multi-server changes (including disjoint cluster migration `{0,1,2} → {3,4,5}`) require either two-phase joint quorums (`C_{old,new}` requiring simultaneous majorities in both `Voters[0]` and `Voters[1]`, with `LearnersNext` staging to prevent voter/learner overlap in `etcd-io/raft`), a decoupled Config State Machine synchronized with the Oplog State Machine at election and guarded by `OplogCommitment(s)` (`will62794/logless-reconfig`), or an external auxiliary master / matchmaker quorum performing explicit **wedge → state transfer → activate** across heterogeneous epochs (`Vertical Paxos`, `Stoppable Paxos`, `Matchmaker Paxos`, `Abstract` abortable BFT switching).

---

## Applicability

This report synthesizes, compares, and cross-checks two coupled domains across 14 durable upstream subjects:

1. **Decidable and End-to-End Distributed Verification Frameworks (comparison & boundary characterization):**
   - `kenmcmil/ivy` (`257e3da96557df04303ccb38e80b5da1cd16cbae`) and `aman-goel/ivybench` (`d2c9298fdd099001c71a34bc2e118db6f07d8404`, `paxos/ivy/oopsla17_paxos.ivy`), grounded normatively in Padon et al. (OOPSLA 2017, `DOI: 10.1145/3140568`; PLDI 2016, `DOI: 10.1145/2908080.2908118`; POPL 2018, `DOI: 10.1145/3158114`; CAV 2020, `DOI: 10.1007/978-3-030-53291-8_12`). Applies to safety and liveness-to-safety verification of unbounded-state relational protocol models compiled to first-order verification conditions (VCs) discharged by SMT solvers with Model-Based Quantifier Instantiation (MBQI).
   - `konnov/bymc` (`266366f738bce9dbd5d04336fd9123d85ae2bca1`) and Konnov, Lazić, Veith, Widder (POPL 2017, `DOI: 10.1145/3009837.3009860`). Applies to parameterized threshold-guarded fault-tolerant distributed algorithms (crash, omission, Byzantine) expressible as counter/threshold automata with linear resilience conditions over parameters `(n, t, f)`.
   - `microsoft/Ironclad` (`2fe4dcdc323b92e93f759cc3e373521366b7f691`, `ironfleet/src/Dafny/Distributed/Protocol/RSL/`). Applies to verified executable Multi-Paxos (`IronRSL`) and sharded KV (`IronSHT`) in Dafny under crash-stop / asynchronous UDP network assumptions with eventual partial synchrony for liveness.
   - `uwplse/verdi` (`7e1641b758d8f0032aa7de63620bc115330e0a6b`) and `uwplse/verdi-raft` (`a3375e867326a82225e724cc1a7b4758b029376f`). Applies to Coq-verified distributed state machines extracted to OCaml, under network fault models (reordering, duplication, drop, crash-recovery) constructed compositionally via VSTs.

2. **Live Consensus Reconfiguration and Cross-Protocol Migration (comparison & executable counterexample validation):**
   - `etcd-io/raft` (`99f9ffb3d19c2dee73cc802737cd7e1e5f008986`, `confchange/confchange.go`, `quorum/joint.go`, `raft.go`). Applies to production Raft clusters using apply-time configuration activation and `ConfChangeV2` joint consensus (`EnterJoint` / `LeaveJoint` / `Simple`).
   - `will62794/logless-reconfig` (`05178a700a05e3a3e7f1808c39a5f61f2e6cece0`) and Schultz, Dardik, Tripakis (CPP 2022, `DOI: 10.1145/3497775.3503688`, `arXiv:2102.11960`). Applies to Raft-derived replication protocols that decouple configuration metadata from the data oplog.
   - Normative protocol-switching literature: `Vertical Paxos` (Lamport, Malkhi, Zhou, PODC 2009, `DOI: 10.1145/1582716.1582783`), `Stoppable Paxos` (Lamport, Malkhi, Zhou, `MSR-TR-2008-192`), `Flexible Paxos` (Howard, Malkhi, Spiegelman, OPODIS 2016, `DOI: 10.4230/LIPIcs.OPODIS.2016.25`), `Matchmaker Paxos` (Whittaker et al., `arXiv:2007.09468v2`), `SmartMerge` (Jehl, Vitenberg, Meling, DISC 2015, `DOI: 10.1007/978-3-662-48653-5_11`), and `Abstract` / *The Next 700 BFT Protocols* (Aublin et al., ACM TOCS 2015, `DOI: 10.1145/2658994`).

3. **Executable Micro-Probes:** The two standalone Python 3.13 probes recorded under **Findings** and **Revalidation** directly validate (a) Ivy's `FAU` stratification-graph cycle/arithmetic rules and (b) bounded-horizon Raft reconfiguration safety (`C_0 = {0,1,2,3}` single-server bug vs. current-term commit barrier, and 6-node disjoint cluster jump vs. joint consensus). Their results apply strictly to the modeled transition rules and state bounds; generalization to arbitrary cluster sizes rests on the referenced mechanized proofs.

---

## Findings

### 1. Decidable Fragments for Infinite-State Distributed Protocol Verification

#### 1.1 From Bernays–Schönfinkel–Ramsey (`EPR`) to Ivy's `FEU` and `FAU` Fragments

`Basis: normative + source + documentation + execution`

Classical **Effectively Propositional Logic (`EPR`)**—the Bernays–Schönfinkel–Ramsey class—consists of first-order formulas in prenex normal form `∃x_1 … x_m. ∀y_1 … y_n. φ(x̄, ȳ)` with equality and predicate/relation symbols, **zero non-constant function symbols**, and **zero background theories**. Satisfiability is `NEXPTIME`-complete and enjoys the **finite-model property**: the Herbrand universe consists solely of the finitely many Skolem constants `x_1, …, x_m`, so grounding every universal quantifier over those constants is both sound and complete.

In practice, distributed protocol specifications require both uninterpreted functions (e.g., mapping rounds to proposals, or Skolem functions from `∀∃` quorum-intersection axioms) and limited arithmetic (timestamps, sequence numbers, ballot comparisons). Direct inspection of `kenmcmil/ivy` (`ivy/ivy_fragment.py:17-605`, `doc/decidability.md:250-600`) reveals that Ivy does **not** restrict VCs to raw EPR; instead, it statically enforces the strictly larger **Finite Almost Uninterpreted (`FAU`)** fragment, extending Ge & de Moura's **Finite Essentially Uninterpreted (`FEU`)** complete-instantiation fragment:

1. **Polarity-Aware Negated-VC Extraction (`ivy/ivy_fragment.py:322-377`, `doc/decidability.md:201-245`):**
   - For inductive invariant checking (`I → wlp(action, I)`), the negated VC is `I ∧ Trans(s, s') ∧ ¬I(s')`.
   - Assumptions (axioms, preconditions, transition equations, and the pre-state invariant `I`) occur **positively**; guarantees (assertions and the post-state invariant `I(s')`) occur **negatively**. Because `I` occurs both positively and negatively, every `∀` in `I` becomes an `∃` in `¬I(s')` (introducing harmless ground Skolem constants), while every `∃` inside `∀` in `I` becomes a Skolem function in positive position.
2. **Stratification Graph Construction (`ivy/ivy_fragment.py:87-151, 292-320, 441-465`):**
   - Let `U` be the set of universally quantified variables of uninterpreted or infinite-domain sorts occurring in the negated VC.
   - Graph vertices are union-find equivalence classes over:
     - `S_v` for each universal variable `v ∈ U`,
     - `A_{f,j}` for each argument position `j` of each uninterpreted function/predicate symbol `f`,
     - `S_σ` (represented by a sentinel symbol `'='` at sort `σ`, `ivy/ivy_fragment.py:114-119`) for each uninterpreted sort `σ` participating in equality.
   - **Equivalence constraints (union-find `unify`):**
     - `f(…, v, …)` with bare universal `v` at position `j` ⇒ `unify(S_v, A_{f,j})`.
     - `v = e` or `e = v` at uninterpreted sort `σ` ⇒ `unify(S_v, S_σ)`. (Notably, `ivy_fragment.py:55-57` explicitly drops Ge & de Moura's stricter constraint `A_{f,i} = S_σ` when `dom(f, i) = σ`, admitting strictly more stratified formulas.)
     - `ite(c, t_1, t_2)` with bare universals in both branches ⇒ `unify(S_{t_1}, S_{t_2})`.
   - **Directed instantiation-growth arcs:**
     - `f(…, t[…, v, …], …)` where `v` occurs *strictly beneath* the top level of argument `j` ⇒ directed arc `S_v → A_{f,j}`.
     - `t[…, v, …] = e` at uninterpreted sort `σ` ⇒ directed arc `S_v → S_σ`.
     - **Skolemization of `∀∃` alternations (`make_skolems`, lines 292–320):** An existential `∃e` inside positive `∀ū` (or universal `∀e` inside negative `∃ū`) records `macro_dep_map[e] ⊇ {S_u | u ∈ ū ∩ FV(∃e. φ)}`—only universal variables *actually free inside the existential body* induce Skolem arcs (`doc/decidability.md:414-421`).
     - **Non-recursive macro over-approximation (`create_macro_maps`, lines 227–277):** Non-recursive definitions (`f(x̄) = rhs`) are memoized once rather than exponentially expanded, propagating `macro_var_map` (exact parameter substitutions) and `macro_dep_map` (strictly nested universal dependencies) in reverse dependency order.
   - **Acyclicity Gate (`ivy/ivy_fragment.py:464`):** The formula lies in `FEU` iff the quotient graph of `arcs` under union-find representatives contains **no directed cycle** (checked via Tarjan SCC / cycle finder). Any cycle implies an unbounded chain of ground term instantiations `t, f(t), f(f(t)), …`.
3. **The `FAU` Arithmetic Boundary (`check_interpreted` & `is_arithmetic_literal`, `ivy/ivy_fragment.py:162-195`):**
   - A universal variable of an interpreted integer sort (`thy.has_integer_interp`) may appear inside an interpreted symbol **if and only if** the atom is a positive **arithmetic literal** of the form `X < Y` (strict inequality under current polarity `pol`, which additionally performs `unify(S_X, S_Y)`), `X < t`, `t < X`, or `X = t` where `t` is strictly ground (`nodes[1-pos] is None and not uvs[1-pos]`).
   - **Exact cliff:** Writing `∀R:int. vote(N, R + 1, V)` or `∀R1,R2:int. R1 + 1 < R2 → …` fails `is_arithmetic_literal` and aborts with `IvyError("The verification condition is not in the fragment FAU")`. Conversely, replacing integer successor arithmetic with an uninterpreted totally ordered sort `round` (`le(X, Y)` axiomatized by reflexivity, transitivity, antisymmetry, totality) keeps the entire VC inside `EPR`/`FAU`.

#### 1.2 How *Paxos Made EPR* Keeps Unbounded Consensus Decidable

`Basis: normative + source`

Direct inspection of `aman-goel/ivybench` (`paxos/ivy/oopsla17_paxos.ivy:15-185`) and Padon et al. (OOPSLA 2017, `DOI: 10.1145/3140568`) identifies four syntactic transformations that hold Paxos, Multi-Paxos, Flexible Paxos, Fast Paxos, Vertical Paxos, and Stoppable Paxos inside decidable `EPR`/`FAU`:

1. **Abstract Quorum Intersection Without Cardinality Arithmetic (`oopsla17_paxos.ivy:42-43`):** Instead of encoding `|Q| > n / 2` (which requires finite-set cardinality + integer division outside `FAU`), quorums are introduced as an uninterpreted sort `quorum` with membership predicate `member(N:node, Q:quorum)` and the single `∀∃` axiom:
   ```text
   ∀Q1:quorum, Q2:quorum. ∃N:node. member(N, Q1) ∧ member(N, Q2)
   ```
   This introduces a **one-way** Skolem edge `quorum → node` in the stratification graph. As long as no axiom or invariant introduces a reverse `node → quorum` function or `∀N. ∃Q` quantifier alternation, the sort graph remains a DAG.
2. **Derived-Relation Rewrite of History Quantifiers (`oopsla17_paxos.ivy:46-48, 101-103`):** Naive Paxos expresses "node `n` has not joined any round greater than `r`" as `∀r2 > r. ¬one_b(n, r2)`, and the `1b` promise message's "maximum prior vote" requires a nested `∃maxr. … ∧ ∀r'. …` inside `join_round`. Storing `left_rnd(n, R)` as a ghost/derived relation updated via `left_rnd(n, R) := left_rnd(n, R) | ~le(r, R)` eliminates quantifier alternation from action guards and preserves `∀*` inductive invariants (`one_b(N, R2) ∧ ¬le(R2, R1) → left_rnd(N, R1)`).
3. **Invariant Stratification for Choosing Witnesses (`oopsla17_paxos.ivy:174-175`):** The core Paxos safety invariant—that no value `V2 ≠ V1` proposed in a later round `R2 > R1` can coexist with a quorum `Q` having voted for `V1` in `R1`—is written as:
   ```text
   ∀R1, R2:round, V1, V2:value, Q:quorum.
     ¬le(R2, R1) ∧ proposal(R2, V2) ∧ V1 ≠ V2 →
       ∃N:node. member(N, Q) ∧ left_rnd(N, R1) ∧ ¬vote(N, R1, V1)
   ```
   Its Skolem function has signature `sk_N : round × round × value × value × quorum → node`, adding only edges into the sink sort `node` (never out of `node`), keeping the stratification graph strictly acyclic.
4. **Isolate-Level Theory Decoupling (`doc/decidability.md:388-390`):** When an executable implementation requires both `f : t → u` and `g : u → t` (or concrete 64-bit integer arithmetic for ballot numbers / log indices), Ivy's `isolate` abstraction encapsulates concrete arithmetic behind an uninterpreted abstract total-order interface, proving each side inside `FAU` separately.

#### 1.3 Executable Micro-Probe 1A: Stratification Graph & `FAU` Razor

`Basis: execution`

Executing the standalone Python stratification checker implementing `ivy/ivy_fragment.py`'s union-find + Skolem-arc + Tarjan-SCC algorithm produces exact discrimination across the five boundary cases:

```text
[1A] Paxos-EPR (quorum intersection + total order): IN_FAU (DECIDABLE)
[1A] Paxos + next_round(R) successor function: OUTSIDE_FAU (UNDECIDABLE_RISK)
     CYCLE_SCC: ['A_vote,1']
       arc A_vote,1 -> A_vote,1 via [vote(N,next_round(R),V): next_round(R) at vote[1]]
[1A] Dual AE cycle (quorum->node + node->quorum): OUTSIDE_FAU (UNDECIDABLE_RISK)
     CYCLE_SCC: ['A_member,0', 'A_member,1']
       arc A_member,1 -> A_member,0 via [forall Q1,Q2 exists N: skolem sk_N(Q1) at member[0]]
       arc A_member,1 -> A_member,0 via [forall Q1,Q2 exists N: skolem sk_N(Q2) at member[0]]
       arc A_member,0 -> A_member,1 via [forall N exists Q: skolem sk_Q(N) at member[1]]
[1A] FAU positive arithmetic literal (R1 < R2 over int): IN_FAU (DECIDABLE)
[1A] Linear arithmetic breach (R + 1 under universal R): OUTSIDE_FAU (UNDECIDABLE_RISK)
     INTERP_ERR: interpreted op '+' applied to universal var 'R' in R + 1
```

#### 1.4 Liveness-to-Safety Reduction in First-Order Logic (`ivy_l2s.py`)

`Basis: normative + source`

First-order `EPR`/`FAU` checks safety invariants (`□ P`), not liveness (`□◇ Fair → ◇ Goal`). Padon et al. (POPL 2018, `DOI: 10.1145/3158114`) and `kenmcmil/ivy` (`ivy/ivy_l2s.py:1-120`) reduce unbounded-domain temporal liveness to first-order safety via **dynamic abstraction / finite-footprint snapshot reduction**:

- Rather than requiring a finite-state lasso (which fails when unbounded rounds or messages grow monotonically along a counterexample trace), `l2s` tracks a **dynamically growing finite footprint** `d_saved` of domain elements referenced so far, snapshots the system state (`l2s_saved := true`) at a nondeterministic loop-start point, and asserts that the monitor never completes a cycle where every fairness obligation is fulfilled while the snapshot footprint projection repeats.
- Because the reduction adds only monadic footprint predicates (`l2s_d(X)`, `l2s_a(X)`) and boolean monitor flags, the resulting safety VC remains inside `EPR`/`FAU` whenever the underlying protocol does—though the user must supply a ranking/witness invariant over the monitor state, and **dynamic-creation protocols with unboundedly many fairness obligations** require additional **temporal prophecy** witnesses (Padon et al., CAV 2021).

#### 1.5 Threshold Automata (`ByMC`) & Parameterized Cutoff Theorems

`Basis: normative + source`

When protocol correctness fundamentally depends on **quantitative Byzantine/crash thresholds** (e.g., Bracha Reliable Broadcast `≥ n - t` echo vs. `≥ t + 1` ready, BosCo one-step consensus `≥ (n + 3t)/2`, ABA `n > 3t`), abstracting quorums into uninterpreted `FAU` relations loses the arithmetic inequalities between multiple distinct threshold levels (`t + 1`, `n - 2t`, `n - t`).

Direct inspection of `konnov/bymc` (`bymc/src/taIr.ml:6-70`, `bymc/src/symbSkel.ml:20-46`) and Konnov, Lazić, Veith, Widder (POPL 2017, `DOI: 10.1145/3009837.3009860`) establishes how **Threshold Automata (`TA`)** restore decidability:

- **IR Structure (`taIr.ml:53-70`):** A threshold automaton `ta_t` declares `Param` (symbolic integers `n, t, f` constrained by linear resilience `assumptions`, e.g. `n > 3t ∧ t ≥ f ≥ 0`), monotonically non-decreasing `Shared` message counters `x_1, …, x_k`, finite process `locs` (`loc_def_t`), and `rules` `{src_loc, dst_loc, guard, actions}` where each `guard` is a boolean combination of linear threshold comparisons (`x ≥ a·n + b·t + c` or `x < …`) and `actions` increment shared counters (`x' = x + 1`).
- **Short Counterexample Property & Acceleration (POPL 2017):** Because shared variables are monotonic and guards only compare against linear parameter expressions, every guard changes truth value **at most once** along any execution (from false to true for lower thresholds `≥`, or true to false for upper thresholds `<`). Partitioning executions into intervals between guard-flip points (`contexts`) and **accelerating** consecutive executions of identical rules into a single SMT step multiplying rule firing counts `δ_r ≥ 0` proves a **diameter bound independent of `n`**: for safety and `ELTL_FT` liveness, if a counterexample exists for *any* `(n, t, f)` satisfying the resilience condition, a counterexample exists with at most `O(|Guards| · |Rules|)` accelerated schema steps, reducing parameterized verification to **quantifier-free linear integer arithmetic (`QF_LIA`)** SMT queries!
- **Cutoff Theorems vs. Threshold Automata:**
  - **Emerson & Kahlon (CADE 2000, `DOI: 10.1007/10721959_19`):** For conjunctive/disjunctive guarded finite-state protocols without arithmetic thresholds, small exact cutoffs (`c = 2` to `c = 5` processes) reduce parameterized model checking to finite model checking.
  - **Marić, Sprenger, Basin (CAV 2017, `DOI: 10.1007/978-3-319-63390-9_12`):** For round-based **Heard-Of (`HO`)** consensus algorithms (OneThirdRule, Coordinated Consensus, LastVoting), they prove exact small cutoffs (`n_0 ≤ 4` to `7`) by constructing value-oblivious quorum-simulation reductions—strictly bypassing general undecidability of parameterized verification (Suzuki 1988) by exploiting anonymity and round synchronization.
  - **Limitation (`known not to apply`):** Neither canonical `ByMC` threshold automata nor `HO` cutoffs natively handle unboundedly many rounds with persistent per-round logs, dynamic leader identities, or arbitrary state-machine payloads (as in Multi-Paxos/Raft); for multi-round stateful logs, `EPR`/`FAU` (`Ivy`) or interactive theorem proving (`IronFleet`/`Verdi`) is required.

#### 1.6 Cross-Framework Comparison: `Ivy`, `ByMC`, `IronFleet`, and `Verdi`

`Basis: source + normative + derived`

| Dimension | `Ivy` (`kenmcmil/ivy`) | `ByMC` (`konnov/bymc`) | `IronFleet` (`microsoft/Ironclad`) | `Verdi` / `Verdi-Raft` (`uwplse/verdi*`) |
| :--- | :--- | :--- | :--- | :--- |
| **Core Logic / Solver** | First-order `FAU` (`EPR` + acyclic stratification + positive `int` literals) → Z3 MBQI | Threshold Automata (`taIr.ml`) → accelerated `QF_LIA` SMT / NuSMV | Higher-order-style Dafny (Boogie → Z3 E-matching + triggers + LIA/sets/seqs) | Constructive dependent type theory (Coq kernel, zero SMT in TCB) |
| **Decidability of VC Check** | **Decidable** (statically gated by `ivy_fragment.py:check_feu`) | **Decidable** for safety & `ELTL_FT` liveness on canonical `TA` (POPL 2017) | **Undecidable** (manual `{:opaque}` / `{:trigger}` annotations required; see `Refinement.i.dfy:211-231`) | **Not automated** (interactive tactic scripts; kernel type-checking decidable) |
| **Failure Transparency** | Concrete finite counter-models (CTIs) directly guide invariant strengthening | Concrete parameterized `(n, t, f)` + firing-count counterexample traces | Z3 timeouts / uninformative quantifier-instantiation failures (`Mariposa` instability) | Unproven Coq subgoals; zero solver nondeterminism |
| **Arithmetic Quorums (`n > 3t`)** | Must abstract to uninterpreted `quorum` sort (`member(N, Q)`) | **Native** linear threshold guards (`x ≥ n - t`, `x ≥ 2t + 1`) | **Native** finite sets & cardinality (`|q| > |replicas|/2`) | **Native** Coq `NoDup` list cardinalities (`all_names_nodes`, `Net.v:37-39`) |
| **Network Fault Abstraction** | Modeled explicitly as monotonic message relations in protocol state | Implicit in threshold bounds (`f` Byzantine / crash counters) | Explicit `LEnvironment` packet bag + `EnvironmentSynchrony` clocks (`Assumptions.i.dfy:27-37`) | **Compositional Verified System Transformers (VSTs)** (`DupDropReordering.v:11-16`, `SeqNum.v`, `Log.v`) |
| **Liveness Support** | Liveness-to-safety (`ivy_l2s.py`, POPL 2018) with finite-footprint snapshots | Native `ELTL_FT` lasso schemas via accelerated SMT (POPL 2017) | Embedded TLA temporal logic in Dafny (`LivenessProof.i.dfy:38-205`, real-time synchrony bounds) | Safety/linearizability only in `verdi-raft` (`EndToEndLinearizability.v:471-483`); liveness not proven |
| **Executable Extraction** | C++ extraction (`ivy_to_cpp.py`); isolated protocol kernel | Verification-only (model checking abstract Promela/TA) | Compiled C#/.NET executable (`IronRSL` / `IronKV`) with verified UDP marshaling | Extracted OCaml executable (`verdi-raft/extraction`) + verified `Cheerios` serialization |
| **Primary Proof Artifact Shape** | 5–15 inductive `FAU` conjectures (`oopsla17_paxos.ivy:154-185`) | Single threshold automaton skeleton (`symbSkel.ml`) | 3-layer refinement (`IsMaximalQuorumOf2bsSequence`, `Refinement.i.dfy:56-59`) + 36 liveness modules | 90+ modular invariant interfaces + proof modules (`theories/RaftProofs/`, `EndToEndLinearizability.v`) |

Key primary-source architectural details observed in `IronFleet` and `Verdi`:
- **IronFleet (`Refinement.i.dfy:56-97`, `Assumptions.i.dfy:27-160`, `LivenessProof.i.dfy:38-205`):** Safety is proved by constructing an abstract `RSLSystemState` from `IsMaximalQuorumOf2bsSequence(ps, qs)` (`Refinement.i.dfy:58`) and showing stuttering simulation to `RslSystemNext` (`Refinement.i.dfy:219-232`). Crucially, Dafny proofs require explicit `{:opaque}` wrappers and `{:trigger ...}` annotations (`ConvertBehaviorSeqToImap`, `Refinement.i.dfy:211-217`; `MakeRslActionTemporalFromSchedulerFunction`, `Assumptions.i.dfy:60-70`) to prevent Z3 quantifier matching loops. Liveness proves `false` from `LivenessAssumptions(b, asp)` conjoined with `always(not(ReplyDeliveredTemporal))` (`LivenessProof.i.dfy:192-205`), explicitly parameterizing `AssumptionParameters` by `live_quorum`, `synchrony_start`, `latency_bound`, `host_period`, `burst_size`, `persistent_period`, and `max_clock_ambiguity` (`Assumptions.i.dfy:27-37`).
- **Verdi & Verdi-Raft (`Net.v:31-79, 124-183`, `DupDropReordering.v:11-104`, `EndToEndLinearizability.v:466-484`):** Verdi defines `MultiParams` over a finite `NoDup` list of node names (`nodes : list name`) with pure handlers `net_handlers` and `input_handlers`, plus crash-recovery (`FailureParams`, `DiskOpMultiParams`). Network faults are modeled via `dup_drop_step` (`DDS_dup`, `DDS_drop`, proving arbitrary packet reordering as `dup_drop_Permutation` in `DupDropReordering.v:94-104`). A **VST** transforms a protocol verified under a benign network (e.g., no duplication or no crashes) into one verified under adversarial networks (`SeqNum.v` adds sequence numbers to mask duplication; `Log.v` adds write-ahead disk logging to mask crash-reboot). `verdi-raft` proves `Theorem raft_linearizable` (`EndToEndLinearizability.v:471-483`) by wiring ~90 decoupled `Interface` typeclasses (e.g. `OneLeaderPerTermInterface`, `LeaderCompletenessInterface`, `StateMachineSafetyInterface`) so proof modules compile independently and survive protocol changes (Woos et al., CPP 2016, `DOI: 10.1145/2854065.2854081`).

---

### 2. Formally Safe Live Consensus Reconfiguration and Multi-Version Protocol Migration

#### 2.1 The Fundamental Quorum-Continuity Invariant

`Basis: normative + derived`

In any static consensus protocol over a fixed configuration `C`, safety reduces to the **Static Quorum Intersection Invariant**:
$$\forall Q_1 \in \mathcal{Q}_{\text{read}}(C),\; Q_2 \in \mathcal{Q}_{\text{write}}(C).\quad Q_1 \cap Q_2 \neq \emptyset$$
(In Flexible Paxos, Howard et al., OPODIS 2016, `DOI: 10.4230/LIPIcs.OPODIS.2016.25`, only Prepare/Election quorums `Q_1` and Accept/Replication quorums `Q_2` must intersect; Accept quorums `Q_2` need not intersect one another.)

During **live dynamic reconfiguration** (`C_0 → C_1 → … → C_k`) or **live protocol migration** (`(C_e, P_e) → (C_{e+1}, P_{e+1})`), different replicas inevitably observe different configurations concurrently due to asynchronous message delivery. Safety fails whenever two replicas can independently form valid quorums in *non-intersecting* configurations without a causal ordering barrier guaranteeing that every decision committed in `C_i` is visible to every leader/proposer in `C_j` (`j > i`). Formally, live transitions must preserve **Inter-Epoch Causal Quorum Continuity**:

> **Invariant (Cross-Configuration Decision Preservation):** For every decision `(slot, val)` committed in configuration/epoch `(C_i, e_i)` at ballot/term `b_i`, every leader or proposer enabled to decide or commit in any configuration/epoch `(C_j, e_j)` with `(e_j, b_j) > (e_i, b_i)` MUST either (a) intersect at least one quorum of `(C_i, e_i)` holding `(slot, val)` during its view-change/election read, OR (b) obtain a **certified sealed state/prefix** from a completed **wedge barrier** proving no further decisions can ever occur in `(C_i, e_i)`.

Every production reconfiguration mechanism—and every historical split-brain bug—is explained by how it enforces or violates this invariant.

#### 2.2 Raft Single-Server Reconfiguration Bug (Ongaro 2015) vs. Current-Term Barrier vs. Apply-Time Activation (`etcd-io/raft`)

`Basis: normative + source + execution`

In Ongaro's 2014 dissertation (Section 4.1), **single-server membership changes** (`|C_new Δ C_old| = 1`) rely on the combinatorial lemma that for any single-server addition or removal between `C_old` and `C_new`, every majority of `C_old` intersects every majority of `C_new`. Because a server adopts a configuration entry **immediately upon appending it to its log** (before commit) and leaders allow at most one uncommitted configuration entry at a time, single-server changes appeared to avoid two-phase Joint Consensus.

**Why Naive Single-Server Changes Break (Ongaro, July 2015 `raft-dev` erratum):** The single-server overlap lemma holds only between `C_old` and *one* neighbor `C_new`, **not between two distinct single-server neighbors `C_1` and `C_2` of the same even-sized `C_0`**. Specifically, for `C_0 = {0, 1, 2, 3}` (size 4, majority = 3):
- `C_1 = C_0 \ {1} = {0, 2, 3}` (size 3, majority = 2),
- `C_2 = C_0 \ {0} = {1, 2, 3}` (size 3, majority = 2).
Notice `{0, 2}` is a majority of `C_1`, `{1, 3}` is a majority of `C_2`, and **`{0, 2} ∩ {1, 3} = ∅`**.

**Executable Micro-Probe 1B — Exact Minimal Counterexample (`Basis: execution`):** Running our symmetry-reduced BFS Raft model checker on `C_0 = {0, 1, 2, 3}` with effective-on-append single-server changes and `has_uncommitted_conf` enforced, **without** the current-term commit barrier, discovers a **6-step Election Safety violation** after exploring 3,941 states:

```text
enforce_current_term_commit=False (allow_noop=False, max_log=1): ELECTION_SAFETY_VIOLATION after 3941 states
  1. Elect(S0, term=1, voters=[0, 1, 2], cfg=[0, 1, 2, 3])
  2. Elect(S1, term=2, voters=[1, 2, 3], cfg=[0, 1, 2, 3])
  3. AppendConf(S0, term=1, idx=1, remove=S1, new_cfg=[0, 2, 3])
  4. Elect(S0, term=3, voters=[0, 2], cfg=[0, 2, 3])
  5. AppendConf(S1, term=2, idx=1, remove=S0, new_cfg=[1, 2, 3])
  6. Elect(S1, term=3, voters=[1, 3], cfg=[1, 2, 3])
  7. DUAL_LEADERS term=3: [0, 1]
```

Both `S0` and `S1` are legally elected leader in **Term 3** using completely disjoint quorums (`{0, 2}` vs. `{1, 3}`), because neither `S2` nor `S3` holds any log entry blocking the stale Term-1/Term-2 candidate!

**Two Proven Engineering Fixes:**
1. **Ongaro's 2015 Current-Term Commit Barrier (Effective-on-Append):** Prohibit any leader from appending a new configuration entry until it has **committed at least one entry (e.g., its leader no-op) from its current term**. In the counterexample above, before `S1` (Term 2) can append `C_2`, it must commit a Term-2 entry on a 3-of-4 majority of `C_0` (which necessarily stamps Term 2 onto at least one of `{0, 2}`), making `S0`'s Term-1 log strictly stale and preventing `S0` from winning `{0, 2}` in Term 3. Enabling `enforce_current_term_commit=True` in our BFS probe exhausts the entire reachable state space (**59,617 states, queue empty**) with **0 safety violations** (`Basis: execution`).
2. **Apply-Time Activation + `pendingConfIndex` + Joint Consensus (`etcd-io/raft`, `99f9ffb3d19c2dee73cc802737cd7e1e5f008986`):** Direct source inspection of `etcd-io/raft` reveals a **fundamentally different design from Ongaro's thesis**:
   - **Activation at Apply Time, Not Append Time (`raft.go:1943-1977`, `doc.go:93-99`):** A node switches `r.trk.Config` only inside `applyConfChange(cc)` → `switchToConfig(cfg, trk)` *after* the configuration log entry is **committed and applied** by the host state machine. Because uncommitted configuration entries never alter active quorums, uncommitted divergent configs `C_1` and `C_2` cannot create disjoint election quorums!
   - **Conservative `pendingConfIndex` Serialization (`raft.go:386-392, 953-963, 1326-1345`):** On `becomeLeader()`, `etcd-io/raft` conservatively sets `r.pendingConfIndex = r.raftLog.lastIndex()` *before* appending its leader `emptyEnt` no-op (`raft.go:958-962`), and `stepLeader` rejects any proposed `ConfChange` / `ConfChangeV2` while `r.pendingConfIndex > r.raftLog.applied` (`raft.go:1326, 1331-1332`), replacing rejected entries with `EntryNormal` no-ops (`raft.go:1341`). Furthermore, a candidate cannot even start an election while committed configuration changes remain unapplied (`hasUnappliedConfChanges()`, `raft.go:983-1000`).
   - **Arbitrary Multi-Server Changes via `JointConfig` (`quorum/joint.go:19-75`, `confchange/confchange.go:51-145`):**
     - `JointConfig` is literally `[2]MajorityConfig` (`Voters[0]` = incoming `C_new`, `Voters[1]` = outgoing `C_old`). Both `CommittedIndex` (taking `min(c[0].CommittedIndex(l), c[1].CommittedIndex(l))`, `joint.go:49-56`) and `VoteResult` (requiring both majorities to win; loss in either yields `VoteLost`, `joint.go:61-75`) enforce simultaneous dual-majority consensus.
     - `Changer.Simple` (`confchange.go:128-145`) rejects any non-joint change whose symmetric difference `symdiff(Voters[0]_old, Voters[0]_new) > 1` (`confchange.go:140-142`).
     - `Changer.EnterJoint(autoLeave, ccs...)` (`confchange.go:51-78`) copies `Voters[0]` into `Voters[1]`, applies arbitrary additions/removals to `Voters[0]`, and sets `AutoLeave` so `appliedTo()` automatically proposes the empty `LeaveJoint` entry once `newApplied >= r.pendingConfIndex` (`raft.go:742-746`).
     - **Subtle Role-Disjointness Invariant (`LearnersNext`, `confchange.go:191-228, 295-316`):** If a voter in outgoing `Voters[1]` is demoted to a non-voting learner during `EnterJoint`, `etcd-io/raft` cannot place it in `cfg.Learners` immediately because `checkInvariants` forbids any ID from appearing in both `Learners` and `Voters[1]` (`confchange.go:306-316`). Instead, `makeLearner` stages the node in `cfg.LearnersNext`, and `LeaveJoint()` atomically promotes `LearnersNext` into `Learners` when `Voters[1]` is cleared (`confchange.go:103-118`).
   - **Executable Micro-Probe 1B — Disjoint Cluster Migration (`{0,1,2} → {3,4,5}`, `Basis: execution`):** Attempting a direct single-step jump `{0,1,2} → {3,4,5}` produces an **Election Safety violation (`DUAL_LEADERS term=2: [1, 3]`) in 167 BFS states** (5 steps), whereas routing through Joint Consensus `{0,1,2} → ({0,1,2} && {3,4,5}) → {3,4,5}` explores 100,000 states with **0 safety violations**.

#### 2.3 Logless Dynamic Reconfiguration (`MongoRaftReconfig`)

`Basis: normative + source`

Production databases derived from Raft sometimes cannot store configuration transitions inside the replicated data oplog (for instance, due to legacy storage formats or decoupled control planes). Direct inspection of `will62794/logless-reconfig` (`MongoRaftReconfig.tla:35-162`, `MongoLoglessDynamicRaft.tla:26-114`) and Schultz, Dardik, Tripakis (CPP 2022, `DOI: 10.1145/3497775.3503688`, `arXiv:2102.11960`) documents the exact formal architecture that makes **logless** reconfiguration safe:

1. **Product Composition of Two State Machines (`MongoRaftReconfig.tla:38-60, 112-126`):** The system composes a **Config State Machine (`CSM` = `MongoLoglessDynamicRaft`)** maintaining `(configVersion, configTerm, config)` lexicographically ordered by `(configTerm, configVersion)` (`IsNewerConfig`, `MongoLoglessDynamicRaft.tla:26-29`) and an **Oplog State Machine (`OSM` = `MongoStaticRaft`)** maintaining `(log, committed)`. The two machines step asynchronously **except** at `BecomeLeader(i, Q)` and `UpdateTerms(s, t)` (`JointNext`, lines 112–116), which execute atomically across both.
2. **Four Preconditions for Safe `Reconfig(i, newConfig)` (`MongoLoglessDynamicRaft.tla:52-61, 95-104`, `MongoRaftReconfig.tla:73-108`):**
   - `ConfigQuorumCheck(i)`: a quorum of `config[i]` already holds `(configVersion[i], configTerm[i])` (guaranteeing at most one uncommitted configuration in flight, analogous to Raft's single-pending-config rule).
   - `TermQuorumCheck(i)`: a quorum of `config[i]` is at `currentTerm[i]`.
   - `QuorumsOverlap(config[i], newConfig)` (generalizing single-server changes to *any* `newConfig` whose quorums pairwise intersect `config[i]`'s quorums, e.g., replacing 1 node or shrinking/growing arbitrarily within quorum-overlap bounds, with `i ∈ newConfig`).
   - **`OplogCommitment(i)` (`MongoRaftReconfig.tla:96-101`):**
     1. `(committed = {}) ∨ (∃c ∈ committed : c.term = currentTerm[i])` (the exact Ongaro 2015 current-term commitment barrier!), **AND**
     2. `∀c ∈ committed : (c.term = currentTerm[i]) ⇒ IsCommitted(c.entry[1], i)` (every entry committed during `currentTerm[i]` under an earlier configuration must be *re-committed* on a quorum of `config[i]` before transitioning out of `config[i]`!).
3. **Election Rule Coupling (`MongoLoglessDynamicRaft.tla:48-50, 78-92`):** A voter `v` grants a vote to candidate `i` only if `IsNewerOrEqualConfig(i, v)` *and* `i`'s oplog is at least as up-to-date as `v`'s, and on step-up `i` bumps `configTerm[i] := newTerm`, establishing a total order across all committed configurations that TLAPS verifies preserves `OnePrimaryPerTerm`, `LeaderCompleteness`, and `StateMachineSafety` (`MongoRaftReconfig.tla:147-160`).

#### 2.4 Live Cross-Protocol & Multi-Version Migration Without Stop-the-World Downtime

`Basis: normative + derived`

Joint Consensus and `MongoRaftReconfig` reconfigure *membership* inside a **single fixed consensus protocol**. Migrating a live cluster across **incompatible consensus algorithms, wire protocols, log formats, or fault models**—such as rolling upgrades from `Raft_v1` to `Raft_v2` (changing log/quorum semantics), `Multi-Paxos → BFT HotStuff`, or `CFT → CFT` with changed state-machine serialization—introduces a strictly harder hazard: **two heterogeneous protocols cannot share an uncommitted joint log entry if their voting/commit predicates or message types are mutually unintelligible.**

Four primary-source architectures solve cross-protocol and multi-version live migration with formal safety invariants:

| Migration Architecture | Primary Source | Transition Protocol (Mechanism) | Downtime / Availability Cost | Handles Heterogeneous Protocols (`P_1 → P_2`)? | Trust / Auxiliary Dependency |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Stoppable Paxos** | Lamport, Malkhi, Zhou (`MSR-TR-2008-192`) | Propose a special **`Stop` command** in log slot `k`; once `Stop` is chosen at `k`, no slot `> k` may ever be decided in `P_1` (enforced by `1b`/`2a` *voiding* rules). `P_2` initializes its state machine from prefix `0..k-1`. | Pipeline drain (1–2 RTTs while slots `> k` are voided/re-proposed to `P_2`) | **Yes** (`P_2` can be an entirely different SMR protocol or binary version) | Reconfiguration oracle or deterministic chain of `Stop(C_{e+1}, P_{e+1})` commands |
| **Vertical Paxos I & II** | Lamport, Malkhi, Zhou (PODC 2009, `DOI: 10.1145/1582716.1582783`) | An external **Auxiliary Configuration Master** assigns monotonic ballot/epoch numbers `e` to `(C_e, P_e)`. Before activating epoch `e`, the new leader executes **Prepare/Promise (`1a`/`1b` Read/Wedge)** against read-quorums of *all prior active epochs* `e' < e` until reaching a **complete** epoch (VP-I) or the immediately preceding **active** epoch via state transfer (VP-II), wedging old acceptors so they reject writes for `< e`. | Near-zero for steady-state; 1 RTT master + 1 RTT wedge on epoch switch | **Yes** (each epoch `e` can run a distinct replication scheme, e.g., primary-backup `k+1` replicas in VP-II vs. `2f+1` Paxos) | Fault-tolerant external configuration master (itself an SMR cluster) |
| **Matchmaker Paxos** | Whittaker et al. (`arXiv:2007.09468v2`, `mwhittaker/frankenpaxos`) | Decouples **matchmakers** (small metadata quorum storing `(epoch, acceptor_config)` pairs) from **acceptors** (data plane). On reconfiguration, proposer runs a 1-RTT **MatchA/MatchB** round with matchmakers to register `C_{e+1}` and discover all prior configurations `C_{< e+1}` that might have chosen values, then runs garbage collection asynchronously once `C_{e+1}` completes state transfer. | **Zero stall on data-plane reads/writes**; reconfiguration completes in 1 RTT (~ms) without halting concurrent slot decisions | **Yes** (generalizes Vertical Paxos by replacing a separate master SMR with a lightweight Paxos-like matchmaker quorum) | Static (or hierarchically reconfigurable) matchmaker quorum |
| **Abstract (Abortable BFT Switching)** | Aublin et al. (ACM TOCS 2015, `DOI: 10.1145/2658994`) | Wraps each BFT protocol `B_i` (e.g., optimistic `AZyzzyva`, `Aliph`, fallback `Backup/PBFT`) as an **Abortable State Machine Replication** instance (`Abstract`). On fault or upgrade trigger, a replica invokes **`abort()`**, collecting a quorum of signed **abort histories** (`init_hist`) proving an upper bound on all committed client requests in `B_i`, and deterministically bootstraps `B_{i+1}` with the unified safe prefix via a verified **Switching/Init** protocol. | Zero in normal case; 1–2 RTT abort-and-switch on protocol change | **Yes** (specifically designed for live switching across heterogeneous BFT protocols with distinct quorum rules, e.g. `3f+1` optimistic vs. conservative) | Signed abort certificates + common deterministic history-extraction function |

#### 2.5 Formal Invariants Required for Zero-Downtime Rolling Protocol Upgrades (`v1 → v2`)

`Basis: derived + normative`

Synthesizing `Vertical Paxos`, `Stoppable Paxos`, `etcd-io/raft`, and `Abstract` yields the **four mandatory invariants** for a formally safe multi-version rolling upgrade from protocol/binary version `v1` to `v2` without downtime or split-brain:

1. **Decoupled Binary Rollout vs. Protocol-Epoch Activation (Feature-Flag Gate):** Deploying `v2` binaries onto nodes one-by-one MUST NOT activate `v2` consensus semantics locally upon restart. While any quorum can still contain `v1` nodes, `v2` binaries MUST execute in **strict `v1`-wire/semantic compatibility mode** (`P_active = v1`). Violating this (activating `v2` rules locally on upgrade) creates heterogeneous quorum interpretations identical to uncommitted configuration divergence.
2. **Quorum-Committed Epoch Activation Barrier:** Switching `P_active` from `v1` to `v2` MUST be driven by a replicated, totally ordered **epoch/protocol-version transition entry** (or Matchmaker/Vertical-Paxos master record) proposed *only after* all voters in the active configuration advertise `supported_versions ∋ v2`, and activated **uniformly at the exact deterministic log index `k_switch`** (apply-time activation, never append-time!).
   - *Rollback Safety Corollary:* Once `k_switch` is committed, downgrading a voter back to a `v1`-only binary that cannot parse `v2` entries at indices `> k_switch` breaks liveness (and can corrupt state if `v1` ignores unknown entry types). Safe rollback requires a symmetric two-step `v2 → v1` downgrade barrier while all nodes still support both versions.
3. **State-Machine & Log-Lens Determinism (`L_12 : State_v1 → State_v2`):** When `v2` changes replicated state-machine representation, snapshot encoding, or deterministic command semantics, the transition at `k_switch` MUST apply a **total, deterministic migration lens** `L_12` over the exact committed prefix `0..k_switch-1` such that every replica executing `L_12(apply_{v1}(log[0..k_switch-1]))` arrives at bit-identical `State_v2` before applying `log[k_switch + 1]`. Any non-determinism in `L_12` (e.g., hash-map iteration order, local wall-clock reads) causes silent replica state divergence indistinguishable from Byzantine corruption.
4. **Wedge-Before-Switch for Incompatible Quorum/Fault Models:** If `v1` and `v2` have incompatible quorum intersection rules (e.g., `Raft` crash-fault `2f+1` → `HotStuff` BFT `3f+1`, or changing Flexible Paxos `Q_1/Q_2` sizes), `v2` MUST NOT accept slot `k_switch + 1` until a **wedge proof** (Stoppable Paxos `Stop` commit, Vertical Paxos `1b` read-quorum wedge over `v1`, or `Abstract` abort certificate) guarantees `v1` can never commit any slot `≥ k_switch`.

---

## Boundaries

1. **Byzantine Faults in `Raft`, `etcd-io/raft`, `IronRSL`, `Verdi-Raft`, and `MongoRaftReconfig` — `known not to apply`:** All crash-fault-tolerant protocols and proofs examined above assume non-equivocating honest replicas under crash-stop or crash-recovery models. Neither Raft Joint Consensus nor `MongoRaftReconfig`'s `OplogCommitment` preserves safety against even a single Byzantine replica forging votes or equivocating `AppendEntries` payloads; Byzantine live switching requires cryptographic quorum certificates (`3f + 1`) as in `Abstract` (Aublin et al., 2015) or `ByMC` threshold automata.
2. **Full Automatic Invariant Synthesis (`IC3PO` / `SWISS` / `DistAI` / `DuoAI`) — `not examined`:** While `oopsla17_paxos.ivy:179-185` records an `IC3PO`-synthesized inductive invariant certificate and `kenmcmil/ivy` includes `ivy_updr.py` and `ivy_duoai.py`, this report characterizes the *decidable verification-condition checking* boundary (`FAU`, `ByMC`, cutoffs) and did not empirically benchmark automated invariant inference scalability or completeness across protocol families.
3. **Executable Reconfiguration in `Verdi-Raft` and `IronRSL` — `unsupported`:** Direct inspection confirms that neither `uwplse/verdi-raft` (`a3375e867326a82225e724cc1a7b4758b029376f`, fixed static `nodes : list name` in `Verdi` `Net.v:37-39`) nor `microsoft/Ironclad`'s `IronRSL` (`2fe4dcdc323b92e93f759cc3e373521366b7f691`, static `LConstants.config.replica_ids` in `Refinement.i.dfy:31-34`) supports dynamic cluster membership reconfiguration or live protocol migration; their end-to-end linearizability and liveness theorems hold strictly for fixed static cluster memberships.
4. **Live Reconfiguration Liveness (Progress Under Continuous Churn) — `unknown` / `not examined`:** `etcd-io/raft`, `MongoRaftReconfig` (CPP 2022), and our Probe 1B verify **safety** (`Election Safety`, `Leader Completeness`, `State Machine Safety`). Formal liveness guarantees under concurrent crashes during `EnterJoint → LeaveJoint` (for example, when `AutoLeave` fails to commit because a leader steps down immediately after committing `C_{old,new}`, or when rapid overlapping `Reconfig` requests starve `ConfigQuorumCheck`) were not mechanically verified in this investigation.
5. **Unbounded-Size Completeness of Probe 1B — `known not to apply` beyond modeled bounds:** Probe 1B's exhaustive BFS check (`59,617` states for `single_fixed`, `100,000`-state bounded check for `joint_consensus`) applies strictly to the finite parameters `(N=4, max_term=3, max_log=2)` and `(N=6, max_term=2, max_log=2)` under the simplified message-free log-replication abstraction; parameterized soundness for arbitrary `N`, terms, and log lengths relies on the TLAPS/Ivy/Coq proofs cited in **Evidence**, not on bounded BFS.
6. **Multi-Region Consensus-Free Atomic Storage Reconfiguration (`SmartMerge`, `DynaStore`) — `not examined` in source:** While Jehl, Vitenberg, and Meling's `SmartMerge` (DISC 2015, `DOI: 10.1007/978-3-662-48653-5_11`) proves that *read/write atomic registers* can reconfigure without consensus using commutative lattice merges over configuration sets, that construction does not extend to general non-commutative replicated state machines (SMR) without solving consensus (FLP / Herlihy hierarchy).

---

## Evidence

All primary repository revisions and literature DOIs were verified on `2026-11-19`.

### Primary Upstream Source Inspections

- **`kenmcmil/ivy` (`257e3da96557df04303ccb38e80b5da1cd16cbae`):**
  - `ivy/ivy_fragment.py:17-605`: Full implementation of `FEU`/`FAU` stratification graph (`map_fmla` lines 87–151, `check_interpreted` & `is_arithmetic_literal` lines 162–195, `create_macro_maps` lines 227–277, `make_skolems` lines 292–320, `create_strat_map` lines 322–377, `check_feu` lines 441–465).
  - `doc/decidability.md:1-600`: Normative specification of wlp VC polarity, EPR, stratified function symbols, stratified quantifier alternations, relevant vocabularies, FEU, and FAU arithmetic literals.
  - `ivy/ivy_l2s.py:1-120`: Liveness-to-safety (`l2s_tactic`, `l2s_tactic_full`, `trace_hook` marking `l2s_saved = true`).
- **`aman-goel/ivybench` (`d2c9298fdd099001c71a34bc2e118db6f07d8404`):**
  - `paxos/ivy/oopsla17_paxos.ivy:15-185`: `total_order(le)`, quorum intersection axiom (`line 43`), `left_rnd` derived relation (`lines 48, 103`), safety conjecture (`lines 147-150`), EPR inductive invariants (`lines 154-185`).
- **`microsoft/Ironclad` (`2fe4dcdc323b92e93f759cc3e373521366b7f691`):**
  - `ironfleet/src/Dafny/Distributed/Protocol/RSL/RefinementProof/Refinement.i.dfy:31-250`: `SystemRefinementRelation`, `IsMaximalQuorumOf2bsSequence`, `ConvertBehaviorSeqToImap` (`{:opaque}`/`{:trigger}`), `RslSystemBehaviorRefinementCorrectImap`.
  - `ironfleet/src/Dafny/Distributed/Protocol/RSL/LivenessProof/Assumptions.i.dfy:27-160`: `AssumptionParameters` (9 real-time/synchrony parameters), `HostExecutesPeriodically`, `PersistentClientSendsRequestPeriodically`.
  - `ironfleet/src/Dafny/Distributed/Protocol/RSL/LivenessProof/LivenessProof.i.dfy:38-205`: `lemma_EventuallyLiveReplicaExecutesClientRequest`, `lemma_LivenessAssumptionsAssumingClientNeverGetsReplyCannotHold`.
- **`uwplse/verdi` (`7e1641b758d8f0032aa7de63620bc115330e0a6b`) & `uwplse/verdi-raft` (`a3375e867326a82225e724cc1a7b4758b029376f`):**
  - `verdi/theories/Core/Net.v:12-220`: `BaseParams`, `MultiParams`, `FailureParams`, `DiskOpMultiParams`, `inductive_invariant`, `inductive_invariant_true_in_reachable`.
  - `verdi/theories/Core/DupDropReordering.v:11-160`: `dup_drop_step` (`DDS_dup`, `DDS_drop`) and `Lemma dup_drop_Permutation`.
  - `verdi-raft/theories/RaftProofs/EndToEndLinearizability.v:1-120, 420-485`: ~90 modular invariant interface imports/typeclass hints and `Theorem raft_linearizable`.
- **`konnov/bymc` (`266366f738bce9dbd5d04336fd9123d85ae2bca1`):**
  - `bymc/src/taIr.ml:6-208`: Threshold automaton AST (`decl_t`, `arith_expr_t`, `rel_expr_t`, `rule_t`, `ta_t`, `ltl_expr_t`).
  - `bymc/src/symbSkel.ml:20-160`: Symbolic skeleton (`Sk.skel_t`, `Sk.rule_t`, `keep_reachable`).
- **`etcd-io/raft` (`99f9ffb3d19c2dee73cc802737cd7e1e5f008986`):**
  - `confchange/confchange.go:31-350`: `Changer.EnterJoint`, `LeaveJoint`, `Simple` (`symdiff > 1` rejection at line 140), `makeLearner` (`LearnersNext` staging at lines 222–227), `checkInvariants` (lines 276–332).
  - `quorum/joint.go:19-75`: `type JointConfig [2]MajorityConfig`, `CommittedIndex`, `VoteResult`.
  - `raft.go:386-395, 737-747, 953-963, 983-1000, 1325-1360, 1943-1990, 2058-2062`: `pendingConfIndex` initialization on `becomeLeader`, `AutoLeave` trigger in `appliedTo`, `hasUnappliedConfChanges`, `applyConfChange` → `switchToConfig`, `committedEntryInCurrentTerm`.
  - `doc.go:93-140`: Apply-time `Node.ApplyConfChange` contract.
- **`will62794/logless-reconfig` (`05178a700a05e3a3e7f1808c39a5f61f2e6cece0`):**
  - `MongoRaftReconfig.tla:35-162`: `CSM`/`OSM` composition, `IsCommitted`, `OplogCommitment(s)` (`lines 96-101`), `JointNext`, safety properties (`OnePrimaryPerTerm`, `LeaderCompleteness`, `StateMachineSafety`).
  - `MongoLoglessDynamicRaft.tla:26-132`: `IsNewerConfig`, `CanVoteForConfig`, `ConfigQuorumCheck`, `TermQuorumCheck`, `BecomeLeader`, `Reconfig` (`QuorumsOverlap`), `SendConfig`.

### Peer-Reviewed Specifications and Literature

- O. Padon, K. L. McMillan, A. Panda, M. Sagiv, S. Shoham, *"Ivy: Safety Verification by Interactive Generalization"*, PLDI 2016 (`DOI: 10.1145/2908080.2908118`); K. L. McMillan & O. Padon, *"Ivy: A Multi-modal Verification Tool for Distributed Algorithms"*, CAV 2020 (`DOI: 10.1007/978-3-030-53291-8_12`).
- O. Padon, G. Losa, M. Sagiv, S. Shoham, *"Paxos Made EPR: Decidable Reasoning About Distributed Protocols"*, PACMPL 1(OOPSLA), 2017 (`DOI: 10.1145/3140568`).
- O. Padon, J. Hoenicke, G. Losa, A. Podelski, M. Sagiv, S. Shoham, *"Reducing Liveness to Safety in First-Order Logic"*, POPL 2018 (`DOI: 10.1145/3158114`).
- I. Konnov, M. Lazić, H. Veith, J. Widder, *"A Short Counterexample Property for Safety and Liveness Verification of Fault-Tolerant Distributed Algorithms"*, POPL 2017 (`DOI: 10.1145/3009837.3009860`).
- E. A. Emerson & V. Kahlon, *"Reducing Model Checking of the Many to the Few"*, CADE 2000 (`DOI: 10.1007/10721959_19`); O. Marić, C. Sprenger, D. Basin, *"Cutoffs for Consensus Algorithms"*, CAV 2017 (`DOI: 10.1007/978-3-319-63390-9_12`).
- C. Hawblitzel et al., *"IronFleet: Proving Practical Distributed Systems Correct"*, SOSP 2015 (`DOI: 10.1145/2815400.2815428`).
- J. R. Wilcox et al., *"Verdi: A Framework for Implementing and Formally Verifying Distributed Systems"*, PLDI 2015 (`DOI: 10.1145/2737924.2737958`); D. Woos et al., *"Planning for Change in a Formal Verification of the Raft Consensus Protocol"*, CPP 2016 (`DOI: 10.1145/2854065.2854081`).
- L. Lamport, D. Malkhi, L. Zhou, *"Stoppable Paxos"*, Microsoft Research TR `MSR-TR-2008-192` (2008), and *"Vertical Paxos and Primary-Backup Replication"*, PODC 2009 (`DOI: 10.1145/1582716.1582783`).
- H. Howard, D. Malkhi, A. Spiegelman, *"Flexible Paxos: Quorum Intersection Revisited"*, OPODIS 2016 (`DOI: 10.4230/LIPIcs.OPODIS.2016.25`).
- D. Ongaro & J. Ousterhout, *"In Search of an Understandable Consensus Algorithm"*, USENIX ATC 2014; D. Ongaro, *Consensus: Bridging Theory and Practice*, Stanford PhD Dissertation (2014) and July 2015 `raft-dev` single-server membership change erratum.
- W. Schultz, I. Dardik, S. Tripakis, *"Formal Verification of a Distributed Dynamic Reconfiguration Protocol"*, CPP 2022 (`DOI: 10.1145/3497775.3503688`), companion preprint W. Schultz, S. Zhou, I. Dardik, S. Tripakis, `arXiv:2102.11960v3` (2021).
- M. Whittaker et al., *"Matchmaker Paxos: A Reconfigurable Consensus Protocol"*, `arXiv:2007.09468v2` (`DOI: 10.48550/arXiv.2007.09468`, 2020).
- P.-L. Aublin, R. Guerraoui, N. Knežević, V. Quéma, M. Vukolić, *"The Next 700 BFT Protocols"*, ACM TOCS 32(4), 2015 (`DOI: 10.1145/2658994`; preliminary EuroSys 2010, `DOI: 10.1145/1755913.1755950`).
- L. Jehl, R. Vitenberg, H. Meling, *"SmartMerge: A New Approach to Reconfiguration for Atomic Storage"*, DISC 2015 (`DOI: 10.1007/978-3-662-48653-5_11`).

### Execution Evidence (`Python 3.13.15`, Linux x86_64, `2026-11-19`)

- **Probe 1A (Stratification Graph & `FAU` Fragment Check):** Verified union-find + Tarjan SCC cycle detection + positive arithmetic literal gate across 5 test formulas (`Paxos-EPR`: `IN_FAU`; `next_round(R)`: self-loop `A_vote,1 -> A_vote,1`; dual `∀∃` cycle: SCC `['A_member,0', 'A_member,1']`; positive `R1 < R2`: `IN_FAU`; `R + 1`: `INTERP_ERR`).
- **Probe 1B (BFS Raft Reconfiguration Safety):**
  - 4-server single-server bug (`C_0 = {0,1,2,3}`, `enforce_current_term_commit=False`): `ELECTION_SAFETY_VIOLATION` (`DUAL_LEADERS term=3: [0, 1]`) after 3,941 popped states (`7,810` discovered states) in 6 steps.
  - 4-server Ongaro 2015 patch (`enforce_current_term_commit=True`, `allow_noop=True, max_log=2, max_term=3`): exhaustive `SAFE` across all 59,617 reachable states tracking `committed_ever` (`58,683` reachable states in the compact Election Safety revalidation script below).
  - 6-server disjoint migration `{0,1,2} → {3,4,5}`: `direct_disjoint` → `ELECTION_SAFETY_VIOLATION` (`DUAL_LEADERS term=2: [1, 3]`) at 167 states; `joint_consensus` → `SAFE_BOUNDED` through 100,000 explored states.

---

## Revalidation

### 1. Revalidating Upstream Source Contracts (Cheapest Discriminating Diffs)

- **Ivy `FAU` decidability rules:** Fetch `ivy/ivy_fragment.py` from `kenmcmil/ivy` and diff `map_fmla`, `is_arithmetic_literal`, `make_skolems`, and `check_feu` against `257e3da96557df04303ccb38e80b5da1cd16cbae` to check whether newer arithmetic theories or non-stratified extensions were admitted.
- **`etcd-io/raft` reconfiguration guards:** Diff `confchange/confchange.go` (`EnterJoint`, `LeaveJoint`, `Simple`, `checkInvariants`), `quorum/joint.go`, and `raft.go` (`becomeLeader`'s `pendingConfIndex` initialization, `stepLeader`'s `alreadyPending` check, and `applyConfChange`) against `99f9ffb3d19c2dee73cc802737cd7e1e5f008986`. Any change switching activation from apply-time to append-time requires verifying that `committedEntryInCurrentTerm()` gates every `ConfChange` proposal.
- **Verdi / IronFleet reconfiguration support:** Check whether `uwplse/verdi` (`Net.v`) relaxes fixed `nodes : list name` or whether `microsoft/Ironclad` (`RSL/Configuration.i.dfy`) replaces static `replica_ids` with epoch-indexed configurations.

### 2. Self-Contained Executable Revalidation Probe (Python 3.10+, Standard Library Only)

Run the following standalone script to revalidate both the `FAU` stratification-cycle razor (Probe 1A) and the 4-server Ongaro 2015 single-server reconfiguration bug vs. current-term commit barrier (Probe 1B) in under 5 seconds:

```bash
python3 - <<'PY'
from collections import defaultdict, deque

# --- Probe 1A: Minimal Stratification-Graph Cycle Check ---
def has_cycle(edges):
    adj = defaultdict(list)
    nodes = set()
    for u, v in edges:
        adj[u].append(v); nodes.add(u); nodes.add(v)
    color = {}
    def dfs(u):
        color[u] = 1
        for v in adj[u]:
            if color.get(v) == 1 or (color.get(v, 0) == 0 and dfs(v)):
                return True
        color[u] = 2
        return False
    return any(color.get(n, 0) == 0 and dfs(n) for n in nodes)

assert not has_cycle([("quorum", "node")])                        # Paxos-EPR: acyclic
assert has_cycle([("round", "round")])                            # next_round(R): self-cycle
assert has_cycle([("quorum", "node"), ("node", "quorum")])        # dual AE: 2-cycle
print("Probe 1A stratification checks passed.")

# --- Probe 1B: 4-Server Ongaro 2015 Single-Server Bug vs Current-Term Barrier ---
def is_quorum(s, cfg): return all(len(s & c) * 2 > len(c) for c in cfg)
def latest_cfg(log, init):
    for _, k, p in reversed(log):
        if k == "CONF": return p
    return init
def uncomm_conf(log, ci): return any(log[i][1] == "CONF" for i in range(ci, len(log)))
def up_to_date(cl, vl):
    return (cl[-1][0] if cl else 0, len(cl)) >= (vl[-1][0] if vl else 0, len(vl))

def check_single_server(enforce_term_commit, allow_noop, max_log):
    servers = (0, 1, 2, 3)
    init_cfg = (frozenset({0, 1, 2, 3}),)
    st0 = ((0, 0, 0, 0), frozenset(), ((), (), (), ()), (0, 0, 0, 0))
    seen, q = {st0}, deque([(st0, [])])
    while q:
        (terms, leaders, logs, commits), tr = q.popleft()
        by_t = defaultdict(set)
        for s, t in leaders: by_t[t].add(s)
        for t, ls in by_t.items():
            if len(ls) > 1: return ("VIOLATION", len(seen), tr + [f"DUAL_LEADERS term={t}: {sorted(ls)}"])
        def push(ns, d):
            if ns not in seen: seen.add(ns); q.append((ns, tr + [d]))
        cands = (0,) if (not leaders and max(terms) == 0) else servers
        for s in cands:
            cfg = latest_cfg(logs[s], init_cfg)
            if s not in cfg[0]: continue
            for nt in range(terms[s] + 1, 4):
                if nt == 1 and s != 0: continue
                elig = {v for v in cfg[0] if terms[v] < nt and up_to_date(logs[s], logs[v])}
                if s not in elig: continue
                oth = sorted(elig - {s})
                for m in range(1 << len(oth)):
                    vs = {s} | {oth[i] for i in range(len(oth)) if (m >> i) & 1}
                    if is_quorum(vs, cfg) and not any(is_quorum(vs - {x}, cfg) for x in vs if x != s):
                        ntm = list(terms)
                        for v in vs: ntm[v] = nt
                        nl = frozenset((x, xt) for x, xt in leaders if x not in vs) | {(s, nt)}
                        push((tuple(ntm), nl, logs, commits), f"Elect(S{s},t={nt},v={sorted(vs)},c={sorted(cfg[0])})")
        if allow_noop:
            for s, lt in leaders:
                if len(logs[s]) < max_log and not any(e[0] == lt and e[1] == "NOOP" for e in logs[s]):
                    nl = list(logs); nl[s] = logs[s] + ((lt, "NOOP", lt),)
                    push((terms, leaders, tuple(nl), commits), f"Noop(S{s},t={lt})")
        for s, lt in leaders:
            cfg = latest_cfg(logs[s], init_cfg)
            if len(logs[s]) >= max_log or uncomm_conf(logs[s], commits[s]) or len(cfg[0]) != 4: continue
            if enforce_term_commit and (commits[s] == 0 or logs[s][commits[s]-1][0] != lt): continue
            for rm in sorted(cfg[0] - {s}):
                nl = list(logs); nl[s] = logs[s] + ((lt, "CONF", (cfg[0] - {rm},)),)
                push((terms, leaders, tuple(nl), commits), f"Conf(S{s},t={lt},rm=S{rm})")
        for s, lt in leaders:
            for f in servers:
                if f != s and terms[f] <= lt and (logs[f] != logs[s] or commits[f] < commits[s]):
                    ntm = list(terms); ntm[f] = lt
                    nld = frozenset((x, xt) for x, xt in leaders if not (x == f and xt < lt))
                    nlg = list(logs); nlg[f] = logs[s]
                    ncm = list(commits); ncm[f] = max(commits[f], commits[s])
                    push((tuple(ntm), nld, tuple(nlg), tuple(ncm)), f"Repl(S{s}->S{f},t={lt})")
        for s, lt in leaders:
            cfg = latest_cfg(logs[s], init_cfg)
            for idx in range(commits[s] + 1, len(logs[s]) + 1):
                if logs[s][idx-1][0] != lt: continue
                h = {v for v in servers if len(logs[v]) >= idx and logs[v][idx-1] == logs[s][idx-1]}
                if is_quorum(h, cfg):
                    ncm = list(commits); ncm[s] = idx
                    push((terms, leaders, logs, tuple(ncm)), f"Commit(S{s},t={lt},idx={idx})")
    return ("SAFE_EXHAUSTIVE", len(seen), [])

r_bug = check_single_server(False, False, 1)
r_fix = check_single_server(True, True, 2)
assert r_bug[0] == "VIOLATION" and r_fix[0] == "SAFE_EXHAUSTIVE"
print(f"Probe 1B buggy={r_bug[0]} (seen={r_bug[1]}): {r_bug[2]}")
print(f"Probe 1B fixed={r_fix[0]} (seen={r_fix[1]})")
PY
```
