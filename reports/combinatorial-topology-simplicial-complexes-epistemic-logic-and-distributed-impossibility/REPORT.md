# Combinatorial Algebraic Topology, Input/Output Automata, Heard-Of Predicates, and Epistemic Impossibility in Distributed Computing

## Summary

Operational interleaving search explodes combinatorially as process counts and network delays scale, leaving both design-space impossibility questions and parameterized fault proofs intractable unless abstracted algebraically or geometrically. Four complementary mathematical frameworks eliminate exhaustive trace exploration by isolating invariant obstructions across topology, simulation relations, round-based communication predicates, and epistemic fixpoints:

1. **Combinatorial Algebraic Topology (`Herlihy & Shavit 1999`, `Saks & Zaharoglou 2000`, `Borowsky & Gafni 1993`, `Castañeda & Rajsbaum 2008`):** Asynchronous wait-free shared-memory protocols correspond bijectively to color-preserving simplicial maps from a chromatic subdivision $\sigma(\mathcal{I})$ of the input complex to the output complex $\mathcal{O}$ carried by the task specification $\Delta$ (the **Asynchronous Computability Theorem**). One round of immediate-snapshot (`IS`) execution on $3$ processes subdivides $\Delta^2$ into $\mathrm{Chr}^1(\Delta^2)$ with $V = 12$ view vertices, $E = 24$ edges, and $T = 13$ triangles ($\chi = 1$, $\partial_1 \circ \partial_2 = 0$), forcing an odd number ($\ge 1$) of panchromatic 3-decision simplices across all $1,728$ valid carrier-preserving labelings (`chromatic_topology_ho_epistemic_probe.py`)—thereby proving $2$-set agreement impossibility via Sperner's lemma (`vltanh/lean4-fixed-point` `Sperner.count_eq_one` in `ZMod 2`).
2. **Input/Output Automata (`IOA` / `TIOA`) and Forward/Backward Simulations (`Lynch & Vaandrager 1995`):** Partitioning external actions into input-enabled receivers and internal/output drivers preserves trace inclusion under parallel composition without circular rely/guarantee obligations. Just as prophecy variables complete `TLA+` refinement mappings, **image-finite backward simulations** are required when implementations defer non-deterministic choices relative to specifications; dropping image-finiteness breaks liveness/infinite-trace soundness via König's lemma.
3. **Heard-Of (`HO` / `SHO`) Predicates and Parameterized Threshold Abstraction (`Charron-Bost & Schiper 2009`, `Biely et al. 2007`, `ByMC`):** Replacing culprit-attributed crash/omission/Byzantine fault assumptions with communication-closed round predicates $SHO(p, r) \subseteq HO(p, r)$ unifies synchronous, asynchronous, and partially synchronous models (`HOModel.thy`) and justifies a stuttering reduction (`Reduction.thy`) from interleaved asynchronous message buffers to atomic synchronous rounds. Crucially, `Reduction.thy` establishes that per-process stuttering preserves local properties (`consensus`, `weak_consensus`) **only**—never simultaneous global predicates across distinct processes—while `OneThirdRule` strictly requires $|HO(p, r)| > 2N/3$ (`0` disjoint quorum pairs on $N=4$ at size $3$, vs. $6$ split-quorum pairs at size $2$).
4. **Halpern–Moses Epistemic Logic and Symbolic BDD Checking (`Halpern & Moses 1990`, `SMCDEL`, `Velisarios`):** Greatest-fixpoint common knowledge $C_G \varphi = \nu Z.\,(\varphi \land \bigwedge_{i \in G} K_i Z)$ vanishes ($0$ worlds in `chromatic_topology_ho_epistemic_probe.py`) under unbounded delay or lossy channels even as distributed knowledge $D_{A,B}$ spans $7/8$ worlds and finite mutual knowledge $E_{A,B}^k$ shrinks monotonically (`6 -> 5 -> 4` for $k=1,2,3$). Symbolic observational structures (`SMCDEL` `KnowStruct`) compress $|W|^2$ Kripke relations into compact BDDs, explaining real split-brain outages (GitHub Oct 2018 43s partition; Cloudflare Nov 2020 non-transitive `HO` switch fault).
5. **Six-Level (`L1`–`L6`) & Comprehensibility (`C1`–`C2`) Trade-Off:** Topological, `HO`, and symbolic epistemic frameworks invest moderate upfront mathematical modeling effort (`L1`) and near-zero runtime execution overhead (`L4` except extracted code like `Velisarios`) to prune impossible protocol families before coding—saving person-years compared to operational bivalence (`AFP/FLP` ~4.5 KLoC Isabelle) or monolithic consensus proofs.

## Applicability

These findings apply directly to the primary publications, formal developments, and executable micro-probes inspected for this report:

- **Combinatorial topology foundations and mechanized Lean 4 / Isabelle developments:**
  - Herlihy and Shavit, *The Topological Structure of Asynchronous Computability*, JACM 46(6), 1999 (DOI `10.1145/331524.331529`); Saks and Zaharoglou, *Wait-Free $k$-Set Agreement is Impossible: The Topology of Public Knowledge*, SICOMP 29(5), 2000 (DOI `10.1137/S0097539796307698`); Borowsky and Gafni, *Generalized FLP Impossibility Result for $t$-Resilient Asynchronous Computations*, STOC 1993 (DOI `10.1145/167088.167119`); Castañeda and Rajsbaum, *New Combinatorial Topology Bounds for Renaming*, PODC 2008 / JACM (DOI `10.1145/1400751.1400791`).
  - `leanprover-community/mathlib4` at `35f494609c32653bae53eb33f0cf2d899808909a` (`Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean`, `Mathlib/Analysis/Convex/SimplicialComplex/Basic.lean`) and `vltanh/lean4-fixed-point` at `5f650f00b1db63837a452696331a98ca886b94a8` (`FixedPoint/Common/Sperner.lean`, `FixedPoint/Common/Subdivision.lean`, `README.md`).
  - `isabelle-prover/mirror-afp-devel` at `773174513872254f8efe1cb3a3ce64037f0b1da6` (`thys/FLP/FLPTheorem.thy`).
- **Automata simulations, Heard-Of round reductions, and parameterized checking:**
  - Lynch and Vaandrager, *Forward and Backward Simulations — Part I: Untimed Systems*, Information and Computation 121(2), 1995 (DOI `10.1006/inco.1995.1134`).
  - Charron-Bost and Schiper, *The Heard-Of Model: Computing in Distributed Systems with Benign Faults*, Distributed Computing 22(1), 2009 (DOI `10.1007/s00446-009-0084-6`); Biely et al., *Tolerating Corrupted Communication*, PODC 2007 (DOI `10.1145/1281100.1281137`); Debrat and Merz, `isabelle-prover/mirror-afp-devel@773174513872` (`thys/Heard_Of/HOModel.thy`, `thys/Heard_Of/Reduction.thy`).
  - `konnov/bymc` at `266366f738bce9dbd5d04336fd9123d85ae2bca1` (`bymc/src/absCounter.ml`, POPL 2017 DOI `10.1145/3009837.3009860`).
- **Epistemic distributed logic, symbolic BDDs, event verification, and industrial incidents:**
  - Halpern and Moses, *Knowledge and Common Knowledge in a Distributed Environment*, JACM 37(3), 1990 (DOI `10.1145/79147.79161`); `jrclogic/SMCDEL` at `ad484a6424b8ed8e7f064376ffc549958c03b141` (`src/SMCDEL/Language.hs`, `src/SMCDEL/Symbolic/S5.hs`); `vrahli/Velisarios` at `6fb353b18610cd79210755fcc90123536c367aaa` (`PBFT/PBFTquorum.v`); GitHub Oct 21, 2018 & Cloudflare Nov 2, 2020 outage analyses; and Python `3.13.15` execution of `chromatic_topology_ho_epistemic_probe.py` (Linux `x86_64`).

Findings do not extend without modification to colored tasks under BG-simulation, synchronous simultaneous global properties under `HO` stuttering reduction, or quantum/probabilistic adversaries without epistemic knowledge extensions.

## Findings

### Combinatorial Algebraic Topology of Asynchronous Computability

#### Chromatic Complexes, Immediate-Snapshot Subdivisions, and Carrier Maps

Basis: **normative** + **execution** + **derived**

In the topological model of Herlihy and Shavit (`10.1145/331524.331529`) and Saks and Zaharoglou (`10.1137/S0097539796307698`), a distributed decision task for $n + 1$ asynchronous processes with IDs $C = \{0, \dots, n\}$ is a triple $(\mathcal{I}, \mathcal{O}, \Delta)$:
- **Chromatic Input Complex $\mathcal{I}$:** Each vertex $v = (p, x)$ pairs a process ID (`color(v) = p \in C`) with an input value $x$; each $k$-simplex $\sigma \in \mathcal{I}$ represents a consistent initial configuration of $k+1$ participating processes with distinct colors.
- **Chromatic Output Complex $\mathcal{O}$:** Each vertex $(p, y)$ pairs a process ID with a decision value $y$; simplices represent valid simultaneous decision vectors.
- **Monotonic Carrier Map $\Delta : \mathcal{I} \to 2^{\mathcal{O}}$:** Maps every input simplex $\sigma \in \mathcal{I}$ to a subcomplex $\Delta(\sigma) \subseteq \mathcal{O}$ of legal outputs when only processes in $\mathrm{colors}(\sigma)$ take steps (wait-freedom), satisfying $\sigma \subseteq \tau \implies \Delta(\sigma) \subseteq \Delta(\tau)$ and color preservation.

For single-round **Immediate-Snapshot (`IS`)** shared memory (each active process atomically writes its state and snapshots all previously/concurrently written states), every execution corresponds to an ordered partition $B_0 \prec B_1 \prec \dots \prec B_{m-1}$ of active processes: processes in block $B_j$ observe the cumulative union $\bigcup_{i \le j} B_i$. On the standard $2$-simplex $\Delta^2$ ($3$ processes), enumerating all ordered partitions ($1$ single-block + $6$ two-block + $6$ three-block = $13$) constructs the first chromatic subdivision $\mathrm{Chr}^1(\Delta^2)$ (`chromatic_topology_ho_epistemic_probe.py` check 1):
- **Round 1 ($\mathrm{Chr}^1(\Delta^2)$):** $V = 12$ view vertices, $E = 24$ edges, $T = 13$ triangles, Euler characteristic $\chi = 12 - 24 + 13 = 1$, and $0$ violations of the chain-complex boundary identity $\partial_1 \circ \partial_2 = 0$ over $\mathbb{Z}$.
- **Round 2 ($\mathrm{Chr}^2(\Delta^2)$):** Iterated IS subdivision yields $V = 99$, $E = 267$, $T = 169 = 13^2$, preserving $\chi = 1$ and $(n-1)$-connectivity ($\tilde{H}_q(\mathrm{Chr}^r(\Delta^n)) = 0$ for all $0 \le q \le n$).

#### Sperner's Lemma, k-Set Agreement, BG-Simulation, and Renaming Bounds

Basis: **normative** + **execution** + **derived**

| Task / Reduction | Topological Obstruction / Equivalence | Decidable Condition / Bound | Critical Failure / Scope Boundary |
| --- | --- | --- | --- |
| Wait-free $k$-Set Agreement ($n+1$ procs, $k \le n$) | Boundary carrier validity induces a **Sperner coloring** on $\mathrm{Chr}^r(\Delta^n)$ | Odd ($\ge 1$) panchromatic $(n+1)$-color simplex contradicts $\le k$ outputs | Breaks if $k \ge n + 1$ (trivial) or synchrony/failure detectors break $\mathrm{Chr}^r$ connectivity |
| **Borowsky–Gafni (`BG`) Simulation** (`10.1145/167088.167119`) | Safe-agreement objects let $t+1$ wait-free simulators trace any $t$-resilient $(n+1)$-proc protocol | Colorless task $t$-resilient solvable iff $(t+1)$-proc wait-free solvable | **Fails on colored tasks** (e.g., renaming) because simulators break process-ID symmetry |
| Wait-Free Renaming ($n+1$ procs into $M$ names) | Symmetry-preserving chain map $\mathcal{P}(\Delta^n) \to \mathcal{O}_{\mathrm{renaming}}$ vs. Euler/Steenrod obstruction (`10.1145/1400751.1400791`) | $M = 2n$ always solvable; $M = 2n - 1$ impossible iff $\gcd\{\binom{n+1}{i}\}_{1 \le i \le n} \neq 1$ | **Exceptional solvability:** at $n+1 = 7$ ($n=6$), binomial GCD $= 1$, so $M = 11 = 2n - 1$ **is solvable** |
| **Asynchronous Computability Theorem** (`10.1145/331524.331529`) | Existence of chromatic subdivision $\sigma(\mathcal{I})$ + color-preserving simplicial map $\mu : \sigma(\mathcal{I}) \to \mathcal{O}$ carried by $\Delta$ | Necessary and sufficient for wait-free read/write solvability | Equivalent continuous map $|\mathcal{I}| \to |\mathcal{O}|$ requires care on non-simply-connected complexes (homology vs. homotopy) |

In `chromatic_topology_ho_epistemic_probe.py` (check 1), exhaustively enumerating every single carrier-respecting decision rule $\delta(p, \mathit{view}) \in \mathit{view}$ across all $12$ vertices of $\mathrm{Chr}^1(\Delta^2)$ ($1^3 \cdot 2^6 \cdot 3^3 = 1,728$ total maps) demonstrates that **all `1,728 / 1,728` maps** produce an odd number of 3-decision panchromatic triangles (`min_panchromatic = 1`), giving a completely finite, executable witness of wait-free 2-set agreement impossibility (`k = 2 < n + 1 = 3`).

#### Mechanized Simplicial Complexes, Sperner Parity, and Operational Bivalence

Basis: **source** + **documentation**

Comparing mechanized formalizations reveals a sharp architectural split between **combinatorial topology proofs** (`Lean 4`) and **operational bivalence proofs** (`Isabelle/HOL`, `Rocq`):

1. **Lean 4 `Mathlib` Simplicial Complexes (`leanprover-community/mathlib4@35f494609c32`):** Separates purely combinatorial `PreAbstractSimplicialComplex ι` / `AbstractSimplicialComplex ι` (`Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean:51-306`, forming a `CompleteLattice` over downward-closed `Finset ι` faces containing singletons) from embedded Euclidean `Geometry.SimplicialComplex 𝕜 E` (`Mathlib/Analysis/Convex/SimplicialComplex/Basic.lean:59-111`), which replaces textbook gluing predicates with `inter_subset_convexHull` (`convexHull 𝕜 s ∩ convexHull 𝕜 t = convexHull 𝕜 (s ∩ t)`).
2. **Lean 4 Sperner & Subdivision Proof (`vltanh/lean4-fixed-point@5f650f00b1db`):** `FixedPoint/Common/Sperner.lean:64-130, 340-459` formalizes Sperner's lemma mod $2$ over iterated barycentric subdivisions (`ZMod 2`) without axioms or `native_decide` (`README.md:17`):
   - `sum_erase_image_eq` (`lines 64-130`) proves per-simplex parity of `0..m`-labeled facets;
   - `doors_eq` (`lines 342-377`) pairs every interior facet via the involution `σ * swap (Fin.castSucc k) k.succ` (`Finset.sum_involution`, cancelling interior terms mod $2$!) leaving only boundary faces `facet m`;
   - `count_eq_one` (`lines 400-427`) proves odd panchromatic count by induction on dimension $r$, and `exists_cell` (`lines 432-459`) bounds vertex $\ell^1$ diameter by $2(r / (r + 1))^n$.
3. **Isabelle/HOL Operational Bivalence (`isabelle-prover/mirror-afp-devel@773174513872`):** `thys/FLP/FLPTheorem.thy:13-140` formalizes Völzer's proof of Fischer–Lynch–Paterson consensus impossibility via a `flpPseudoConsensus` locale over asynchronous message multisets (`NonUniformExecutionsConstructable`), explicitly reasoning about step-by-step configuration reachability and fair infinite schedules across ~4,500 LoC of Isabelle rather than homology or simplicial subdivisions.

### Input/Output Automata and Simulation Completeness

#### IOA/TIOA Signature Partitioning and Forward vs. Backward Simulations

Basis: **normative** + **derived**

Lynch and Tuttle's Input/Output Automata (`IOA`) and Lynch–Vaandrager (`10.1006/inco.1995.1134`) partition every automaton $A$'s action signature into disjoint input ($in(A)$), output ($out(A)$), and internal ($int(A)$) actions with strict **input enabling**: every state accepts every $a \in in(A)$. Parallel composition $A_1 \parallel A_2$ is legal whenever $out(A_1) \cap out(A_2) = \emptyset$ and internal actions are disjoint, yielding automatic trace-projection compositionality ($\mathrm{traces}(A_1 \parallel A_2)|_i \subseteq \mathrm{traces}(A_i)$) without circular assume-guarantee loops. Timed I/O Automata (`TIOA`) adjoin continuous trajectories $\tau : [0, t] \to \mathrm{States}(A)$ for hybrid real-time drift bounds.

Lynch and Vaandrager (`10.1006/inco.1995.1134`) establish the exact automata-theoretic dual of Abadi–Lamport refinement completeness:
- **Forward Simulation ($F \subseteq S_{\mathcal{I}} \times S_{\mathcal{S}}$):** Relates reachable states forward along transitions ($s \xrightarrow{a}_{\mathcal{I}} s' \land (s, u) \in F \implies \exists u'.\, u \xrightarrow{a^*}_{\mathcal{S}} u' \land (s', u') \in F$). Sound for finite and infinite traces, **incomplete** when implementation $\mathcal{I}$ defers an externally invisible choice that specification $\mathcal{S}$ makes earlier.
- **Backward Simulation ($B \subseteq S_{\mathcal{I}} \times S_{\mathcal{S}}$):** Every reachable state has a non-empty image $B(s) \neq \emptyset$, initial states map to initial states ($B[\mathit{Start}_{\mathcal{I}}] \subseteq \mathit{Start}_{\mathcal{S}}$), and transitions match backward ($s \xrightarrow{a}_{\mathcal{I}} s' \land (s', u') \in B \implies \exists u.\, (s, u) \in B \land u \xrightarrow{a^*}_{\mathcal{S}} u'$). Backward simulations are sound for finite traces unconditionally, and sound for infinite fair traces **if and only if $B$ is image-finite** (each $s$ relates to finitely many $u$), mirroring the finite-branching prophecy constraint via König's lemma. Any trace-inclusion refinement splits canonically into a forward simulation followed by an image-finite backward simulation.

### Heard-Of Predicates, Reduction Theorems, and Threshold Checking

#### Culprit-Free Round Predicates (`HO` / `SHO`) and Coarse-to-Fine Reduction

Basis: **normative** + **source** + **execution** + **derived**

Charron-Bost and Schiper (`10.1007/s00446-009-0084-6`) and Biely et al. (`10.1145/1281100.1281137`) eliminate separate operational formalizations for crash, link omission, dynamic partitions, partial synchrony (`GST`), and Byzantine corruption by modeling protocols as round-synchronous `CHOAlgorithm` records (`afp/Heard_Of/HOModel.thy:185-285`: `CinitState`, `sendMsg`, `CnextState`) parametrized purely by per-process, per-round subsets $SHO(p, r) \subseteq HO(p, r) \subseteq \Pi$:
- $q \notin HO(p, r)$: $p$ hears nothing from $q$ in round $r$ (`msgs q = None`, whether due to sender crash, network drop, or timeout).
- $q \in HO(p, r) \setminus SHO(p, r)$: $p$ receives a **corrupted** or Byzantine-equivocated value `Some m'` differing from `sendMsg` (`HOModel.thy:263-267`, `fg_rcv_msg` in `Reduction.thy:125-132`).
- Fault models reduce cleanly to **communication predicates**: e.g., `OneThirdRule` requires $\forall p, r.\, |HO(p, r)| > 2N/3$ and an eventual uniform hearing round for termination; `LastVoting` (Paxos core) requires $|HO(p, r)| > N/2$ and a post-`GST` phase of stable coordinator hearing; `Byzantine` models constrain $|SHO(p, r)|$ relative to $N - t$.

In `Reduction.thy:65-150, 771-879`, Debrat and Merz formalize Chaouch-Saad's **Reduction Theorem** proving that every interleaved asynchronous execution `fg_run` (with separate `fg_send_msg`, `fg_rcv_msg`, and `fg_local` steps over an explicit network bag of `(p, r, q, m)` quadruples) is **locally stutter-equivalent** (`locally_similar`) to a coarse-grained atomic round execution `CSHORun`. Consequently, `local_property_reduction` transfers `consensus_is_local` and `weak_consensus_is_local` (`lines 841-879`) from synchronous rounds down to fully interleaved asynchronous runs. **Critical Soundness Boundary (`Reduction.thy:31-37`):** Stuttering equivalence per process does **not** preserve simultaneous global predicates referencing states of distinct processes at the same wall-clock instant (e.g., global round barriers in intermediate steps).

In `chromatic_topology_ho_epistemic_probe.py` (check 2), evaluating `OneThirdRule` over $N=4$ nodes confirms `0` disjoint quorum pairs when requiring $|HO(p, r)| \ge 3$ ($> 2N/3$), versus `6` disjoint quorum pairs when relaxing to size $2$ (which admits split-brain writes). Meanwhile, `konnov/bymc@266366f738bc` (`bymc/src/absCounter.ml:98-212`, DOI `10.1145/3009837.3009860`) abstracts symmetric threshold-guarded `Promela` processes into parametric integer **counters** (`c_ctx#get_ctr`) tracking how many processes occupy each local control state, replacing $all(...)$ and $card(...)$ quantifiers with linear arithmetic guards checked via SMT/nuXmv over **all** $N > 3t$ simultaneously.

### Epistemic Logic of Distributed Knowledge and Industrial Outages

#### S5 Semantics, Common Knowledge Fixpoints, and SMCDEL Compression

Basis: **normative** + **source** + **execution**

Halpern and Moses (`10.1145/79147.79161`) define knowledge over interpretable runs $(R, \pi)$ via local-state equivalence $r(i, t) = r'(i, t') \implies (r, t) \sim_i (r', t')$:
- **Individual knowledge $K_i \varphi$:** True at all worlds indistinguishable to process $i$.
- **Distributed knowledge $D_G \varphi$:** True across the **intersection** $\bigcap_{i \in G} \sim_i$ (pooled evidence across group $G$).
- **Mutual knowledge $E_G^k \varphi$:** $E_G^1 \varphi \triangleq \bigwedge_{i \in G} K_i \varphi$, $E_G^{k+1} \varphi \triangleq E_G(E_G^k \varphi)$.
- **Common knowledge $C_G \varphi$:** Greatest fixpoint $\nu Z.\,(\varphi \land \bigwedge_{i \in G} K_i Z)$, true only across the transitive closure $(\bigcup_{i \in G} \sim_i)^*$ (everybody knows, everybody knows everybody knows, ad infinitum).

Halpern and Moses prove that under unbounded asynchronous communication or unreliable message delivery, **no protocol can ever attain non-trivial common knowledge $C_G \varphi$** of an external event (Coordinated Attack theorem), making simultaneous multi-node state changes unachievable unless common knowledge is weakened to $\epsilon$-common knowledge (bounded clock skew $\epsilon$) or eventual/timestamped consensus.

In `jrclogic/SMCDEL@ad484a6424b8` (`src/SMCDEL/Language.hs:72-120`, `src/SMCDEL/Symbolic/S5.hs:74-260`), explicit Kripke graphs ($O(|W|^2)$ edges) are replaced by **Knowledge Structures** `KnS [Prp] Bdd [(Agent, [Prp])]` ($\mathcal{F} = (V, \theta, O_1, \dots, O_n)$):
- Valid worlds are a single Boolean state law BDD $\theta$ over propositions $V$;
- Each agent $i$'s indistinguishability relation collapses to sharing observational variables $O_i \subseteq V$, turning $K_i \varphi$ into symbolic universal quantification `forallSet (allprops \\ obs ! i) (imp lawbdd (bddOf kns form))` (`S5.hs:249-251`);
- $D_G \varphi$ universally quantifies only outside $\bigcup_{i \in G} O_i$ (`lines 259-260`), and $C_G \varphi$ computes the greatest BDD fixpoint `gfp lambda` (`lines 255-257`).

Running `chromatic_topology_ho_epistemic_probe.py` (check 3, `probe_sha256: 982e3209847e41208e5c70a01331f7582e5dffdf843925142fdb9bf3a43334a8`) on a 3-round, 8-world lossy Coordinated Attack structure confirms `distributed_knowledge_D_AB = 7` (all attack worlds), `mutual_knowledge_E_k_sizes = {1: 6, 2: 5, 3: 4}` (decaying linearly per half-round), and `common_knowledge_gfp_C_AB = 0` (empty fixpoint).

In Byzantine protocol verification, `vrahli/Velisarios@6fb353b18610` (`PBFT/PBFTquorum.v:57-98`) formalizes epistemic event-order logic (`Logic of Events`) in Rocq, proving that any two $2F+1$ quorums among $3F+1$ replicas intersect in at least $F+1$ nodes (`two_quorums`), guaranteeing at least one honest witness to propagate knowledge across views.

#### Real-World Outage Evidence: Asymmetric Partitions and Split-Brain

Basis: **documentation** + **derived**

- **GitHub October 21, 2018 Outage (*"Oct 21 post-incident analysis"*):** A `43`-second inter-datacenter network partition disconnected database clusters (`Orchestrator`). Because no remote agent could distinguish a delayed ACK from a hard partition or achieve common knowledge $C_G$ of failover, both datacenters elected conflicting MySQL primaries during the `43 s` window, producing `24` hours of split-brain state reconciliation and stale reads—precisely validating Bailis & Kingsbury's (*The Network is Reliable*, `CACM 2014`, Jepsen corpus) observation that real deployments cannot assume common knowledge or fail-stop partition symmetry.
- **Cloudflare November 2, 2020 `etcd` 3.3 Outage (*"A Byzantine failure in the real world"*):** A misconfigured switch yielded non-transitive asymmetric connectivity (`HO(A) = {A,C}`, `HO(B) = {B,C}`, `HO(C) = {A,B,C}`). As confirmed in `chromatic_topology_ho_epistemic_probe.py` (check 2, `asym_A_hears_B = False`), `A` and `B` fail `OneThirdRule`'s symmetric quorum reachability while `C` reaches everyone—causing repeated `etcd` election disruptions over ~6 hours when `PreVote` was absent.

```text
Basis: execution (Python 3.13.15, Linux x86_64)
Probe: chromatic_topology_ho_epistemic_probe.py (sha256: 982e3209847e41208e5c70a01331f7582e5dffdf843925142fdb9bf3a43334a8)
Output:
  check_1_chromatic_sperner: {'chr1_V_E_T_euler': (12, 24, 13, 1), 'chr1_d1_o_d2_violations': 0, 'chr2_V_E_T_euler': (99, 267, 169, 1), 'chr1_carrier_maps_checked': 1728, 'chr1_odd_panchromatic_maps': 1728, 'chr1_min_panchromatic_simplices': 1}
  check_2_heard_of_quorums: {'asym_A_hears_B': False, 'asym_passes_OTR_gt_2N_div_3': {'A': False, 'B': False, 'C': True}, 'N4_disjoint_pairs_size_3': 0, 'N4_disjoint_pairs_size_2': 6}
  check_3_epistemic_fixpoint: {'worlds_count': 8, 'attack_worlds': 7, 'distributed_knowledge_D_AB': 7, 'mutual_knowledge_E_k_sizes': {1: 6, 2: 5, 3: 4}, 'common_knowledge_gfp_C_AB': 0}
```

### Six-Level Performance, Verification, and Footprint Matrix (L1–L6)

Basis: **source** + **documentation** + **derived**

| Framework / Proof Artifact | (L1) Authoring Velocity & Proof Size | (L2) Toolchain Build Time & RSS | (L3) Checking / Elaboration Latency | (L4) Generated Runtime Execution | (L5) Certificate / Kernel Check Speed | (L6) RAM, Artifact & Binary Footprint |
| --- | --- | --- | --- | --- | --- | --- |
| `vltanh/lean4-fixed-point` (`Sperner` / `Brouwer`) | `460` LoC `Sperner.lean` (`~3,200` LoC across `23` modules, `README.md:104`); high math skill requirement | Lean 4 + `Mathlib` cache (`lake exe cache get`); `~30 s` incremental project build once Mathlib cached | Sub-second to few seconds per lemma (`ZMod 2` involution + ring proofs) | None (pure mathematical impossibility/fixed-point library; `0` production codegen) | Lean 4 kernel + `scripts/Audit.lean` + `comparator` (`~1–5 s` axiom check, zero `native_decide`) | Mathlib `.olean` cache `~1–2 GB`; local project `.olean` tens of MB |
| `AFP/FLP` Operational Bivalence (`Isabelle/HOL`) | `~4,500` LoC (`FLPTheorem.thy` `1,503` LoC); tedious inductive execution/message-multiset lemmas | Isabelle/HOL base image (`~1–2 GB` Poly/ML heap) | `~20–40 s` batch `isabelle build` checking all fairness & non-uniform steps | None (impossibility theorem only) | Deterministic Isabelle/Pure LCF kernel inference (`~20–40 s`) | Isabelle heap image + HTML/session artifacts (`hundreds MB`) |
| `AFP/Heard_Of` (`HOModel` + `Reduction` + Algorithms) | `HOModel.thy` `433` LoC + `Reduction.thy` `882` LoC + `~5 KLoC` verifying `OneThirdRule`, `LastVoting`, `EIGByz`, etc. | Isabelle/HOL + `Stuttering_Equivalence` session | `~30–90 s` session check; `Reduction.thy` proves coarse-to-fine once for all algorithms | None (abstract round verification; requires separate impl refinement) | Deterministic LCF kernel check (`s`–`min`) | Poly/ML session RSS `~0.5–1.5 GB` |
| `ByMC` (`konnov/bymc` Threshold Automata) | Compact Promela-like threshold specs (`~50–250` LoC); **parametric over all $N > 3t$** | OCaml + Z3/Yices/NuSMV (`<1 min` build) | `<1 s–tens of s` on threshold consensus benchmarks (`absCounter.ml`); exponential blowup avoided via counter abstraction | None (parametric design checker) | Re-run counter SMT/nuXmv queries (`s`) | `tens–hundreds MB` SMT/BDD solver RSS (independent of concrete $N$) |
| `SMCDEL` (`jrclogic/SMCDEL` BDD Epistemic) | Concise Haskell `KnowStruct` specs (`~30–150` LoC) vs. exponential Kripke graphs | GHC + `CacBDD` / `CUDD` C bindings (`<30 s` build) | `<1 ms–1.3 s` for `2^20–2^50+` worlds (`SumAndProduct`, `MuddyChildren`), vs. $O(\|W\|^2)$ explicit `S5.hs` timeout | Executable Haskell evaluation / model finder (research scale, not distributed runtime) | Recompute BDD fixpoint (`ms`–`s`) | Compact shared BDD DAG nodes (`tens MB` vs. multi-GB explicit Kripke graphs) |
| `Velisarios` (`vrahli/Velisarios` Rocq Events) | `~60 KLoC` Rocq proofs for `PBFT` event-order safety (`PBFTquorum.v` `325` LoC) | Coq/Rocq (`~15–45 min` cold build) | `min`–`tens min` batch `coqc`; explicit causal event trees avoid SMT unpredictability | OCaml extracted `PBFT` replicas (single-node sequential message loop + GC) | Rocq CIC kernel `.vo` check (`min`) | Multi-hundred MB `.vo` artifacts + extracted OCaml binary |

Key cross-level synthesis (`Basis: derived`):
- **Early impossibility pruning multiplies `L1` ROI:** Spending days modeling a task in chromatic complexes (`Chr^r`), `HO` round predicates, or `SMCDEL` (`L1`/`L3` in seconds) detects impossible specifications ($k$-set agreement, unauthenticated split-quorums at $\le 2N/3$, asynchronous common knowledge) **before** investing `~50 KLoC` (`Verdi-Raft`) or `~60 KLoC` (`Velisarios`) in doomed implementation proofs.
- **Symbolic & counter encodings invert `L3`/`L6` complexity:** Explicit-state Kripke relations (`O(|W|^2)`) and explicit immediate-snapshot trees (`13^r` simplices per $3$-process round, growing super-exponentially in $N$) hit memory ceilings (`L6`) within 2–3 rounds, whereas `SMCDEL` BDDs and `ByMC` threshold counter abstraction collapse symmetric or factored worlds into sub-second (`L3`), megabyte-scale (`L6`) checks.

### Human Comprehensibility (C1) and Universal Conceptual Minimization (C2)

#### (C1) Geometric & Epistemic Clarity vs. Operational Interleaving Explosion

Basis: **source** + **documentation** + **derived**

- **Working-memory compression:** A 1-page geometric diagram of $\mathrm{Chr}^1(\Delta^2)$ (`13` simplices, `chromatic_topology_ho_epistemic_probe.py`) or a 3-line `(HO, SHO)` predicate (`|HO(p, r)| > 2N/3`) captures all asynchronous schedules or Byzantine corruptions in human working memory at once. Conversely, operational bivalence (`FLPTheorem.thy`, `1,503` lines) forces readers to track multiset network buffers, fairness queues, and valency flips across interleaved transitions (`NonUniformExecutionsConstructable`).
- **Onboarding and diagnostic trade-off:** The price of topological compression is mathematical prerequisite depth: while Sperner mod-2 facet pairing (`Sperner.lean:342-377`) is elementary in $n = 2$, higher-dimensional generalizations (`Castañeda & Rajsbaum 2008` renaming at $n+1 = 7$) rely on algebraic homology, torsion, and chain maps that are harder to audit casually than a concrete `ByMC` or `SMCDEL` counterexample trace.

#### (C2) Simplicity, Minimization, and Universal Representation

Basis: **source** + **derived**

Each framework succeeds by eliminating realization-medium clutter with a universal mathematical primitive, while exposing exact leakage boundaries that must not be overlooked:

1. **Communication-Closed `(HO, SHO)` Predicates (`HOModel.thy`)** eliminate separate operational fault models (`crash`, `send-omission`, `receive-omission`, `link drop`, `GST partial synchrony`, `Byzantine payload corruption`) by expressing every execution uniformly as $(HO(p, r), SHO(p, r))$ sets. **Boundary check:** Complexity is genuinely eliminated for **local** round-based properties (`consensus_is_local`), **not** for cross-process simultaneous invariants (`Reduction.thy:31-37`), nor for protocols whose network state depends on non-round-tagged long-lived channels without epoch tagging.
2. **Chromatic Simplicial Carrier Maps $\mu : \mathrm{Chr}^r(\mathcal{I}) \to \mathcal{O}$ (`10.1145/331524.331529`)** collapse every asynchronous read/write schedule into a single static topological continuity/simplicial question. **Boundary check:** The representation unifies wait-free read/write tasks cleanly, yet `BG`-simulation cannot hide process-ID colors (`colored` tasks such as renaming require color-preserving maps directly).
3. **Observational Knowledge Structures `KnS (V, θ, O_i)` (`SMCDEL`)** eliminate explicit Kripke accessibility graphs by deriving indistinguishability directly from agent-visible propositions $O_i$. **Boundary check:** Works natively when observational uncertainty is propositional and static/announced; dynamic link delays require explicit round propositions in $V$ (`2r + 2` chain in `chromatic_topology_ho_epistemic_probe.py`) rather than an infinite-state asynchronous Kripke frame.

## Boundaries

- **not examined:**
  - Mechanized proofs of the full Asynchronous Computability Theorem (`ACT`) or `Castañeda–Rajsbaum` $n+1 = 7$ renaming upper-bound protocols inside Lean 4 / Rocq (`mathlib4` at `35f494609c32` and `vltanh/lean4-fixed-point` at `5f650f00b1db` establish abstract/geometric simplicial complexes and Sperner/Brouwer, not distributed task carrier maps directly).
  - Continuous `TIOA` clock-trajectory proofs in Isabelle/PVS beyond untimed `IOA` forward/backward simulation (`10.1006/inco.1995.1134`).
  - Local compilation/execution of `isabelle build`, `bymc`, `SMCDEL`, or `Velisarios` `coqc` proof suites (benchmarks cited from primary repositories/papers; local execution focused on the self-contained Python probe).
- **unknown:**
  - Exact scaling wall-clock times of `ByMC` counter-abstraction when extended to non-symmetric asymmetric `HO` graphs such as Cloudflare's 3-node non-transitive topology (standard `ByMC` assumes symmetric threshold process templates).
- **known not to apply:**
  - `AFP/Heard_Of/Reduction.thy` coarse-to-fine reduction (`local_property_reduction`) does **not** preserve simultaneous global predicates referencing multiple distinct processes at the same atomic step (`Reduction.thy:31-37`).
  - Borowsky–Gafni (`BG`) simulation (`10.1145/167088.167119`) does **not** reduce colored tasks (such as wait-free renaming) because simulating processes cannot inherit unique identities of simulated processes.
  - Non-image-finite backward simulations (`10.1006/inco.1995.1134`) fail to preserve infinite-trace / liveness refinement.
- **unsupported:**
  - Wait-free $k$-set agreement for $n + 1$ processes when $k \le n$ in asynchronous read/write shared memory (`10.1145/331524.331529`, `10.1137/S0097539796307698`).
  - Exact deterministic common knowledge $C_G \varphi$ over unbounded-delay or lossy channels (`10.1145/79147.79161`, verified `0`-world greatest fixpoint in `chromatic_topology_ho_epistemic_probe.py`).

## Evidence

### Primary Git Repositories and Inspected Source Locations

- **`leanprover-community/mathlib4` (`35f494609c32653bae53eb33f0cf2d899808909a`):** `Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean:50-308` (`PreAbstractSimplicialComplex`, `AbstractSimplicialComplex` `CompleteLattice`) and `Mathlib/Analysis/Convex/SimplicialComplex/Basic.lean:59-111` (`Geometry.SimplicialComplex`, `convexHull_inter_convexHull`, `disjoint_or_exists_inter_eq_convexHull`).
- **`vltanh/lean4-fixed-point` (`5f650f00b1db63837a452696331a98ca886b94a8`):** `FixedPoint/Common/Sperner.lean:64-130, 340-459` (`sum_erase_image_eq`, `doors_eq`, `doors_eq_count`, `count_eq_one`, `exists_cell`) and `README.md:1-174` (`~3,200` lines across `23` modules, `~30 s` incremental build, zero `axiom`/`native_decide`).
- **`isabelle-prover/mirror-afp-devel` (`773174513872254f8efe1cb3a3ce64037f0b1da6`):** `thys/Heard_Of/HOModel.thy:42-330` (`consensus`, `weak_consensus`, `CHOAlgorithm`, `SHOmsgVectors`, `CSHORun`), `thys/Heard_Of/Reduction.thy:1-150, 740-882` (`fg_rcv_msg`, `local_property_reduction`, `consensus_is_local`, simultaneous-state caveat), and `thys/FLP/FLPTheorem.thy:13-140` (`flpPseudoConsensus`, `NonUniformExecutionsConstructable`).
- **`konnov/bymc` (`266366f738bce9dbd5d04336fd9123d85ae2bca1`):** `bymc/src/absCounter.ml:98-212` (`trans_prop_decl`, `replace_card`, `tr_atomic` counter abstraction), alongside Konnov et al. POPL 2017 (DOI `10.1145/3009837.3009860`).
- **`jrclogic/SMCDEL` (`ad484a6424b8ed8e7f064376ffc549958c03b141`):** `src/SMCDEL/Language.hs:72-120` (DEL AST `PrpF`, `K`, `C_Delta`, `D_Delta`, announcements) and `src/SMCDEL/Symbolic/S5.hs:74-260` (`KnowStruct`, `bddOf` for `K`/`Ck`/`Dk`, `gfp lambda` fixpoint).
- **`vrahli/Velisarios` (`6fb353b18610cd79210755fcc90123536c367aaa`):** `PBFT/PBFTquorum.v:43-98` (`length_reps = 3 * F + 1`, `two_quorums` $F+1$ intersection).

### Normative Theory and Non-Academic Industrial Literature

- Herlihy, M., & Shavit, N. (1999). *The Topological Structure of Asynchronous Computability*. Journal of the ACM, 46(6), 858–923. DOI `10.1145/331524.331529`.
- Saks, M., & Zaharoglou, F. (2000). *Wait-Free $k$-Set Agreement is Impossible: The Topology of Public Knowledge*. SIAM J. Comput., 29(5), 1449–1483. DOI `10.1137/S0097539796307698`.
- Borowsky, E., & Gafni, E. (1993). *Generalized FLP Impossibility Result for $t$-Resilient Asynchronous Computations*. STOC 1993. DOI `10.1145/167088.167119`.
- Castañeda, A., & Rajsbaum, S. (2008). *New Combinatorial Topology Bounds for Renaming: The Lower Bound*. PODC 2008. DOI `10.1145/1400751.1400791`.
- Lynch, N. A., & Vaandrager, F. W. (1995). *Forward and Backward Simulations — Part I: Untimed Systems*. Information and Computation, 121(2), 214–233. DOI `10.1006/inco.1995.1134`.
- Charron-Bost, B., & Schiper, A. (2009). *The Heard-Of Model: Computing in Distributed Systems with Benign Faults*. Distributed Computing, 22(1), 49–71. DOI `10.1007/s00446-009-0084-6`.
- Biely, M., Charron-Bost, B., Gaillard, A., Hutle, M., Schiper, A., & Widder, J. (2007). *Tolerating Corrupted Communication*. PODC 2007, 244–253. DOI `10.1145/1281100.1281137`.
- Halpern, J. Y., & Moses, Y. (1990). *Knowledge and Common Knowledge in a Distributed Environment*. Journal of the ACM, 37(3), 549–587. DOI `10.1145/79147.79161`.
- GitHub Engineering Blog (Oct 30, 2018). *"Oct 21 post-incident analysis"* (`https://github.blog/2018-10-30-oct21-post-incident-analysis/`).
- Cloudflare Engineering Blog (Nov 2020). *"A Byzantine failure in the real world"* (`https://blog.cloudflare.com/a-byzantine-failure-in-the-real-world/`).
- Bailis, P., & Kingsbury, K. (2014). *The Network is Reliable*. Communications of the ACM, 57(9), 48–55. DOI `10.1145/2655735`.

### Preserved Standalone Executable Micro-Probe (`chromatic_topology_ho_epistemic_probe.py`)

Command: `python3 chromatic_topology_ho_epistemic_probe.py` (`Python 3.13.15`, Linux `x86_64`, observed `2026-11-19`, exit `0`, SHA-256 `982e3209847e41208e5c70a01331f7582e5dffdf843925142fdb9bf3a43334a8`).

```python
#!/usr/bin/env python3
"""Self-contained micro-probe for chromatic subdivisions, Sperner parity, HO quorums, and S5 fixpoints."""
import hashlib
import itertools
from pathlib import Path


def immediate_snapshot_subdivision(simplices, n_procs=3):
    """Apply one round of chromatic immediate-snapshot subdivision Chr(.) to a pure simplex list."""
    procs = tuple(range(n_procs))
    ordered_parts = []
    for k in range(1, n_procs + 1):
        for assign in itertools.product(range(k), repeat=n_procs):
            if set(assign) == set(range(k)):
                ordered_parts.append(
                    tuple(frozenset(p for p in procs if assign[p] == b) for b in range(k))
                )
    ordered_parts = sorted(set(ordered_parts))

    out = []
    for simp in simplices:
        by_color = {v[0]: v for v in simp}
        for blocks in ordered_parts:
            verts = []
            seen_verts = set()
            for b in blocks:
                for p in b:
                    seen_verts.add(by_color[p])
                view = frozenset(seen_verts)
                for p in b:
                    verts.append((p, view))
            out.append(tuple(sorted(verts, key=lambda x: x[0])))
    return out


def check_chromatic_subdivision_and_sperner():
    """1. Chr^1(Delta^2) and Chr^2(Delta^2) topology + exhaustive 2-set agreement Sperner parity."""
    base = [((0, frozenset()), (1, frozenset()), (2, frozenset()))]
    # Replace dummy views with vertex IDs for round 0
    base = [((0, 0), (1, 1), (2, 2))]

    chr1 = immediate_snapshot_subdivision(base, 3)
    v1 = sorted({v for s in chr1 for v in s}, key=lambda x: (x[0], len(x[1])))
    e1 = {frozenset(e) for s in chr1 for e in itertools.combinations(s, 2)}
    euler1 = len(v1) - len(e1) + len(chr1)

    # Verify d1 o d2 == 0 on oriented 2-simplices over Z
    # Orient each 2-simplex (v0, v1, v2) sorted by color (0, 1, 2)
    boundary_sum_violations = 0
    for s in chr1:
        # d2(v0, v1, v2) = +(v1,v2) - (v0,v2) + (v0,v1); d1(a,b) = b - a
        v0, v1_v, v2 = s
        net = {}
        for coef, (a, b) in ((1, (v1_v, v2)), (-1, (v0, v2)), (1, (v0, v1_v))):
            net[b] = net.get(b, 0) + coef
            net[a] = net.get(a, 0) - coef
        if any(val != 0 for val in net.values()):
            boundary_sum_violations += 1

    # Round 2 chromatic subdivision Chr^2(Delta^2)
    chr2 = immediate_snapshot_subdivision(chr1, 3)
    v2 = {v for s in chr2 for v in s}
    e2 = {frozenset(e) for s in chr2 for e in itertools.combinations(s, 2)}
    euler2 = len(v2) - len(e2) + len(chr2)

    # Carrier-respecting decision map on Chr^1(Delta^2): delta(p, view) in view
    # Note views in Chr^1 are subsets of {(0,0),(1,1),(2,2)}; extract underlying input IDs
    choices = [sorted(c for (c, _) in view) for (_, view) in v1]
    total_maps = 0
    odd_panchromatic = 0
    min_pan = 999
    for coloring in itertools.product(*choices):
        total_maps += 1
        cmap = dict(zip(v1, coloring))
        pan = sum(1 for s in chr1 if len({cmap[v] for v in s}) == 3)
        min_pan = min(min_pan, pan)
        if pan % 2 == 1:
            odd_panchromatic += 1

    return {
        "chr1_V_E_T_euler": (len(v1), len(e1), len(chr1), euler1),
        "chr1_d1_o_d2_violations": boundary_sum_violations,
        "chr2_V_E_T_euler": (len(v2), len(e2), len(chr2), euler2),
        "chr1_carrier_maps_checked": total_maps,
        "chr1_odd_panchromatic_maps": odd_panchromatic,
        "chr1_min_panchromatic_simplices": min_pan,
    }


def check_heard_of_quorums():
    """2. Heard-Of non-transitive asymmetric topology vs OneThirdRule > 2N/3 threshold."""
    # Asymmetric 3-node HO graph (A<->C, B<->C, A<-/->B)
    ho_asym = {"A": {"A", "C"}, "B": {"B", "C"}, "C": {"A", "B", "C"}}
    a_can_hear_b = "B" in ho_asym["A"]
    passes_otr_n3 = {p: len(s) > (2 * 3) / 3 for p, s in ho_asym.items()}

    # Quorum intersection across N=4 nodes: compare threshold >= 3 (> 2N/3) vs >= 2
    nodes4 = (0, 1, 2, 3)
    subsets3 = [set(s) for s in itertools.combinations(nodes4, 3)]
    subsets2 = [set(s) for s in itertools.combinations(nodes4, 2)]
    disjoint_ge3 = sum(1 for x in subsets3 for y in subsets3 if x.isdisjoint(y))
    disjoint_ge2 = sum(1 for x in subsets2 for y in subsets2 if x.isdisjoint(y))
    return {
        "asym_A_hears_B": a_can_hear_b,
        "asym_passes_OTR_gt_2N_div_3": passes_otr_n3,
        "N4_disjoint_pairs_size_3": disjoint_ge3,
        "N4_disjoint_pairs_size_2": disjoint_ge2,
    }


def check_halpern_moses_epistemic(max_rounds=3):
    """3. S5 observational structure (SMCDEL-style) for r-round lossy Coordinated Attack."""
    # Worlds w in 0..(2*max_rounds+1):
    #   w = 0: bit=0 (no attack)
    #   w = 2k-1: bit=1, A sent k msgs, B received k-1 msgs
    #   w = 2k:   bit=1, A sent k msgs, B received k msgs (for k=1..max_rounds)
    #   w = 2*max_rounds+1: bit=1, A sent max_rounds+1, B received max_rounds (boundary)
    # Use clean finite window of size 2*max_rounds+2 where B's obs changes on even steps and A's on odd:
    n_worlds = 2 * max_rounds + 2
    worlds = set(range(n_worlds))
    attack = worlds - {0}  # worlds where attack is initially ordered (bit=1)

    # Observations O_A and O_B partition worlds into indistinguishable pairs {2k, 2k+1} / {0, 1}
    obs_a = {w: w // 2 for w in worlds}
    obs_b = {w: (w + 1) // 2 for w in worlds}

    def box(obs_fn, target):
        return {w for w in worlds if all(u in target for u in worlds if obs_fn[u] == obs_fn[w])}

    # Distributed knowledge D_{A,B}: intersection of equivalence classes (here singleton {w})
    dk_attack = {
        w
        for w in worlds
        if all(u in attack for u in worlds if obs_a[u] == obs_a[w] and obs_b[u] == obs_b[w])
    }

    # Mutual knowledge depth k: E^k(phi)
    ek_sizes = {}
    cur = attack
    for k in range(1, max_rounds + 1):
        cur = box(obs_a, cur) & box(obs_b, cur)
        ek_sizes[k] = len(cur)

    # Common knowledge greatest fixpoint: gfp Z. (attack & K_A(Z) & K_B(Z))
    z = set(worlds)
    while True:
        z_next = attack & box(obs_a, z) & box(obs_b, z)
        if z_next == z:
            break
        z = z_next

    return {
        "worlds_count": n_worlds,
        "attack_worlds": len(attack),
        "distributed_knowledge_D_AB": len(dk_attack),
        "mutual_knowledge_E_k_sizes": ek_sizes,
        "common_knowledge_gfp_C_AB": len(z),
    }


if __name__ == "__main__":
    digest = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print("probe_sha256:", digest)
    print("check_1_chromatic_sperner:", check_chromatic_subdivision_and_sperner())
    print("check_2_heard_of_quorums:", check_heard_of_quorums())
    print("check_3_epistemic_fixpoint:", check_halpern_moses_epistemic(3))
```

## Revalidation

To revalidate these findings against newer upstream commits or local verification runs without re-surveying the full literature:

1. **Rerun the embedded micro-probe:** Save the Python source block above as `chromatic_topology_ho_epistemic_probe.py` and run `python3 chromatic_topology_ho_epistemic_probe.py`, confirming SHA-256 `982e3209847e41208e5c70a01331f7582e5dffdf843925142fdb9bf3a43334a8` and identical combinatorial outputs (`(12, 24, 13, 1)` on `Chr^1(Delta^2)`, `1,728/1,728` odd panchromatic carrier maps, `0` disjoint `N=4` size-3 quorums, and `0`-world `C_AB` greatest fixpoint).
2. **Verify `vltanh/lean4-fixed-point` axiom hygiene:** Run `lake env lean scripts/Audit.lean` against commit `5f650f00b1db63837a452696331a98ca886b94a8` (or newer) to confirm `Sperner.count_eq_one` and `Brouwer.KKM.exists_fixedPoint` depend solely on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) without `native_decide` or `sorryAx`.
3. **Check `AFP/Heard_Of` reduction assumptions:** Diff `thys/Heard_Of/Reduction.thy` in `isabelle-prover/mirror-afp-devel@773174513872` to confirm whether `local_property_reduction` remains restricted to per-process stutter-invariant properties.
4. **Check `SMCDEL` symbolic fixpoint operators:** Diff `src/SMCDEL/Symbolic/S5.hs` in `jrclogic/SMCDEL@ad484a6424b8` (`bddOf` for `K`, `Ck`, and `Dk`) to confirm symbolic observational projection semantics remain unchanged.
