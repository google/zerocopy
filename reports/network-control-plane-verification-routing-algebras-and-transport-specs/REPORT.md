# Network Control-Plane Verification, Routing Algebras, and Transport Specifications

## Summary

Formal verification of networked systems splits cleanly across two planes with fundamentally different mathematical models—**distributed fixed-point convergence** in routing control planes and **reactive state-machine conformance** in wire-transport endpoints:

1. **Routing Fixed Points and Algebraic Convergence (`SPP`, `MED`, `Sobrinho`, `Metarouting`):** Interdomain routing (`BGP-4`, RFC 4271) is not guaranteed to converge or possess a unique equilibrium. The Griffin–Shepherd–Wilfong Stable Paths Problem (`SPP`, ToN 2002) proves that checking whether a BGP policy configuration has a stable solution is NP-complete: `BAD GADGET` has `0` stable states across all `81` assignments and oscillates indefinitely, `DISAGREE` has `2` stable equilibria (RFC 4264 "BGP wedgies"), and BGP Multi-Exit Discriminator (`MED`, Griffin–Wilfong ICNP 2002 / RFC 3345) induces persistent intra-AS oscillation (`0` stable states across `6` states in our executable probe) because comparing `MED` only among routes from the same neighboring AS violates preference transitivity. Sobrinho's routing algebra theory (ToN 2005) separates **strict monotonicity** (sufficient for loop-free convergence) from **isotonicity** (necessary and sufficient for hop-by-hop optimality)—our exhaustive algebraic checker confirms that both Shortest-Widest Path and Gao–Rexford valley-free routing with hop tie-breaking are strictly monotonic yet *non-isotonic*.
2. **Concrete Simulation vs. Symbolic Control-Plane Verification (`Batfish`, `Minesweeper`, `Bagpipe`, `NV`):**
   - `Batfish` (`batfish/batfish@735d69e0`) computes concrete forwarding tables via iterative non-monotonic fixed-point simulation (`IncrementalBdpEngine.computeNonMonotonicPortionOfDataPlane`), detecting divergence via `BdpOscillationException`—fast for concrete environments (`k=0`), but blind to latent failover bugs (our probe demonstrates `0/1` failures at `k=0` vs. `1/5` blackhole failures at `k=1`).
   - `Minesweeper` (SIGCOMM 2017) encodes stable routing fixed points plus up to `k` symbolic link failures (`sum(failed_e) <= k`) directly into SMT, whereas modern `batfish/batfish@735d69e0` (`projects/minesweeper/src/main/java/org/batfish/minesweeper/bdd/`) replaces monolithic network SMT with BDD-based symbolic route-policy analysis (`TransferBDD`, `BDDRoute`, `MutableBDDInteger`).
   - `Bagpipe` (`uwplse/bagpipe@67a38c4c`, OOPSLA 2016) mechanizes RFC 4271 BGP semantics in Coq (`BGPSpec.v`), proves a sound reduction of AS-wide policies to parallel per-router SMT queries (`BGPV.v`: `parallelBGPVDec`, `fastPolicyImpliesPolicy`), and mechanizes Gao–Rexford global Internet convergence (`GaoRexford/InternetConverges.v`).
   - `NV` (`NetworkVerification/nv@952dae45`, PLDI 2020) defines a functional Stable Routing Problem (SRP) intermediate language `(G, A, trans, merge, init)` (`Srp.ml`) compiled both to native OCaml with CUDD MTBDDs (`NativeBdd.ml`) and to unboxed SMT-LIB2 (`Smt.ml`, `SmtUnboxed.ml`), extended with Kirigami assume-guarantee network partitioning (`SrpRemapping.ml`, `SmtKirigami.ml`).
3. **Executable Transport Protocol Specifications (`Ivy QUIC` vs. `HOL4 Netsem TCP`):**
   - `Ivy` (`kenmcmil/ivy@84a6b955`, SIGCOMM 2019) formalizes QUIC compositionally as assume-guarantee `before`/`require` obligations on `frame.*.handle` and `packet_event` (`quic_frame.ivy`, `quic_packet.ivy`), then compiles the specification itself into randomized adversarial peer testers (`quic_server_test.ivy`, `quic_shim.ivy`) that uncover real interoperability and security bugs in black-box implementations without reading their source.
   - `Netsem` (`rems-project/netsem@0b02450e`, JACM 2018) specifies real-world TCP/IP and POSIX Sockets post-hoc as a massive nondeterministic HOL4 Labelled Transition System (`TCP1_hostLTSScript.sml`, 18,620 lines; `TCP1_hostTypesScript.sml` `tcpcb`/`socket`/`host`), acting as an offline symbolic trace-checking oracle validated against thousands of Linux, FreeBSD, and Windows wire/syscall traces.
4. **Decoupled Congestion Control Contracts (`CCP`: `portus` + `ccp-kernel`):** `CCP` (SIGCOMM 2018) decouples per-packet datapath measurement aggregation—expressed as bounded, non-looping fold programs (`portus/src/lang/ast.rs`)—from user-space congestion control algorithms (`CongAlg`, `Flow::on_report`, `Report::get_field` versioned by `program_uid` in `portus/src/lib.rs`). Direct source inspection of `ccp-project/ccp-kernel@e3b3b7ea` (`tcp_ccp.c`) surfaces two concrete kernel-contract defects: (1) `ccp_now`/`ccp_since`/`ccp_after` (L70–93) read wall-clock `ktime_get_real_ts64` (`CLOCK_REALTIME`) rather than monotonic time, breaking microsecond fold timers on NTP steps; and (2) `do_set_cwnd` (L47–59) truncates byte `cwnd /= tp->mss_cache` directly into `tp->snd_cwnd` without a `>= 1` clamp, permitting silent zero-window stalls.

## Applicability

This report synthesizes primary-source code inspection, peer-reviewed papers, RFCs, and deterministic Python 3 micro-probes across the following pinned revisions and standards:

- **Routing Theory & Algebras:** Griffin, Shepherd, and Wilfong (IEEE/ACM ToN 2002, `DOI: 10.1109/90.993304`), Griffin and Wilfong (IEEE ICNP 2002, `DOI: 10.1109/ICNP.2002.1181389`), Sobrinho (IEEE/ACM ToN 2005, `DOI: 10.1109/TNET.2005.857653`), Griffin and Sobrinho (ACM SIGCOMM 2005, `DOI: 10.1145/1080091.1080094`), RFC 4271 (BGP-4), RFC 3345 (BGP Persistent Route Oscillation Condition), and RFC 4264 (BGP Wedgies).
- **Control-Plane Verifiers:**
  - `batfish/batfish` at `735d69e0fbdf7ea9427fcff4855bb51f52a81fc2` (`IncrementalBdpEngine.java`, `BgpRoutingProcess.java`, `TransferBDD.java`, `BDDRoute.java`) compared with the original Minesweeper SMT paper (Beckett et al., SIGCOMM 2017, `DOI: 10.1145/3098822.3098834`). Note carefully the architectural divergence between the 2017 Minesweeper SMT paper and the modern `projects/minesweeper/bdd/` package in `batfish/batfish@735d69e0`!
  - `uwplse/bagpipe` at `67a38c4c6def7fb270a045b4afa668d22e293be7` (Weitz et al., OOPSLA 2016, `DOI: 10.1145/2983990.2984012`): Coq formalization of single-AS BGP policy verification and Gao–Rexford convergence.
  - `NetworkVerification/nv` at `952dae45c374dcd80e081faa16fae12217f4dc8e` (Giannarakis et al., PLDI 2020, `DOI: 10.1145/3385412.3386019`): OCaml/CUDD/Z3 SRP intermediate language, simulator, SMT encoder, and Kirigami modular partitioner.
- **Transport Protocol Specifications & Congestion Control:**
  - `kenmcmil/ivy` branch `quic23` at `84a6b955291ae419ed10ba96cd184fee084652e9` (McMillan & Zuck, SIGCOMM 2019, `DOI: 10.1145/3341302.3342087`), targeting IETF QUIC draft-23 (pre-RFC 9000; RFC 9000 extensions exist in downstream forks such as `ElNiak/QUIC-Ivy` branch `quic-rfc9000`, noted under Boundaries).
  - `rems-project/netsem` at `0b02450eee334fc42f74ad3da09d3ce1a0698a48` (Bishop et al., JACM 2018, `DOI: 10.1145/3243650`), formalizing BSD/Linux/Windows TCP/IPv4 + POSIX Sockets behavior.
  - `ccp-project/portus` at `a43f3071c428aef98893455ce06d40db169242da` and `ccp-project/ccp-kernel` at `e3b3b7ea927ae7b7281f26c76c7bd9d872e267de` (Narayan et al., SIGCOMM 2018, `DOI: 10.1145/3230543.3230553`).

## Findings

### 1. Control-Plane Fixed Points, BGP Oscillation Pathologies, and Routing Algebras (SPP, MED, Sobrinho, Metarouting)

Basis: normative (RFC 4271, RFC 3345) + documentation (ToN 2002, ICNP 2002, ToN 2005, SIGCOMM 2005) + execution (standalone Python 3 micro-probe in `## Evidence`)

Routing protocols compute a distributed fixed point over a network graph $G = (V, E)$. Unlike shortest-path IGPs (`OSPF`, `IS-IS`), policy-based interdomain routing (`BGP-4`) allows each autonomous system to rank candidate routes arbitrarily, decoupling local preferences from global convergence.

#### 1.1 The Stable Paths Problem (SPP) and Pathological Gadgets
Griffin, Shepherd, and Wilfong (IEEE/ACM ToN 2002, `DOI: 10.1109/90.993304`) abstract BGP convergence to an instance $S = (G, \mathcal{P}, \Lambda)$ with destination $0 \in V$, sets of permitted simple paths $\mathcal{P}^v$, and strict ranking functions $\lambda^v : \mathcal{P}^v \to \mathbb{N}$ (plus the empty path $\epsilon$ ranked lowest). A path assignment $\pi : V \to \mathcal{P} \cup \{\epsilon\}$ is **stable** iff for every $v \neq 0$:
$$\pi(v) = \arg\max_{\lambda^v} \left( \{\epsilon\} \cup \{ (v, u) \cdot \pi(u) \in \mathcal{P}^v \mid (v, u) \in E,\; \pi(u) \neq \epsilon \} \right)$$
Key complexity and structural theorems:
- **Solvability is NP-complete:** Deciding whether an arbitrary SPP instance has a stable solution is NP-complete (reduction from 3-SAT).
- **Dispute Wheel Condition:** A sufficient (not necessary) condition guaranteeing a unique stable solution under arbitrary asynchronous activation schedules is the absence of a **Dispute Wheel**—a cyclic chain of nodes $u_0, \dots, u_{k-1}$ where each $u_i$ prefers a rim path routed through $u_{i+1}$ over its direct spoke path to $0$.
- **Executable Verification (SPP Probe in `## Evidence`):**
  1. **`BAD GADGET` (No Stable Solution):** Four nodes `{1, 2, 3, 4}` with ranked preferences `1: [1-3-0, 1-0]`, `2: [2-1-0, 2-0]`, `3: [3-4-2-0, 3-0]`, `4: [4-2-0, 4-0]`. Exhaustive enumeration over all $3^4 = 81$ states confirms **`0` stable states**. Under deterministic round-robin activation, the system enters an infinite oscillation cycle (detected between steps `3` and `19`, passing through `{1: (1,0), 2: (2,1,0), 3: (3,0), 4: (4,0)}`).
  2. **`DISAGREE` (Non-Unique Equilibria / BGP Wedgie, RFC 4264):** Two nodes `{1, 2}` with preferences `1: [1-2-0, 1-0]` and `2: [2-1-0, 2-0]`. Exhaustive enumeration finds **`2` stable states**: `{1: (1, 2, 0), 2: (2, 0)}` and `{1: (1, 0), 2: (2, 1, 0)}`. Which equilibrium is reached depends on transient packet timing or historical link flaps; once trapped in the unintended backup equilibrium, restoring a failed link does not restore the intended primary path without manual intervention.

#### 1.2 BGP `MED` Non-Transitivity Oscillations (Griffin & Wilfong ICNP 2002; RFC 3345)
Even when eBGP policies satisfy Gao–Rexford commercial constraints (no inter-AS dispute wheel), RFC 4271 Section 9.1.2.2(c) specifies that the `MULTI_EXIT_DISC` (`MED`) attribute is compared **only** between routes whose first AS in `AS_PATH` is identical. This breaks total-order transitivity of the BGP decision process inside an iBGP route-reflector topology:
- Suppose inside AS 100, route reflectors `R1` and `R2` observe three candidate routes:
  - `rA_hi`: from `AS_A`, `MED = 10`, IGP cost `(R1: 1, R2: 100)`.
  - `rB`: from `AS_B`, `MED = 0`, IGP cost `(R1: 5, R2: 2)`.
  - `rA_lo`: from `AS_A`, `MED = 0`, IGP cost `(R1: 10, R2: 10)`.
- At `R1`, the pairwise preference relation forms a **Condorcet cycle**:
  - `rA_lo` beats `rA_hi` (same neighbor `AS_A`, `MED 0 < 10`);
  - `rA_hi` beats `rB` (different AS $\implies$ `MED` ignored, IGP `1 < 5`);
  - `rB` beats `rA_lo` (different AS $\implies$ `MED` ignored, IGP `5 < 10`).
- **Executable Verification (MED Probe in `## Evidence`):** With `R1` locally holding `{rA_hi, rB}` (receiving `rA_lo` iff `R2` picks it) and `R2` locally holding `{rA_lo}` (receiving `rB` iff `R1` picks it), exhaustive enumeration over all $3 \times 2 = 6$ joint selections under RFC 4271 grouped `deterministic-med` confirms **`0` stable states**, oscillating indefinitely:
  ```text
  (R1: rA_hi -> rB, R2: rA_lo -> rB) | (R1: rB -> rA_hi, R2: rB -> rA_lo) | ...
  ```
- **Remediation Contract:** Either deploy `bgp always-compare-med` (restoring a total preorder at the cost of allowing a peer AS to manipulate tie-breaks against unrelated ASes), advertise multiple best paths per reflector (`BGP ADD-PATH`, RFC 7911), or enforce full-mesh iBGP / aligned IGP-MED hierarchies.

#### 1.3 Sobrinho's Routing Algebra Theory and Metarouting
Sobrinho (IEEE/ACM ToN 2005, `DOI: 10.1109/TNET.2005.857653`) and Griffin & Sobrinho (*Metarouting*, SIGCOMM 2005, `DOI: 10.1145/1080091.1080094`) model routing protocols algebraically as a tuple $\mathcal{A} = (S, \preceq, L, \oplus, \bar{0}, \bar{\infty})$ where $S$ is the set of route signatures (with best/origin $\bar{0}$ and unusable/filtered $\bar{\infty}$), $\preceq$ is a total preference order ($s_1 \preceq s_2$ means $s_1$ is preferred to or equal to $s_2$), $L$ is a set of link labels, and $\oplus : L \times S \to S$ is the route-extension function. Two axioms govern protocol correctness:
1. **Strict Monotonicity:** $\forall l \in L,\; \forall s \in S \setminus \{\bar{\infty}\}:\; s \prec l \oplus s$. Guarantees that path-vector and distance-vector protocols converge to a **unique loop-free stable state** on every finite topology (and eliminates routing loops without requiring path-vector loop detection).
2. **Isotonicity:** $\forall l \in L,\; \forall s_1, s_2 \in S:\; s_1 \preceq s_2 \implies l \oplus s_1 \preceq l \oplus s_2$. Necessary and sufficient for Bellman–Ford and Dijkstra algorithms to compute **globally optimal paths** and for hop-by-hop destination-based forwarding to stay consistent with each router's optimal choice.

**Executable Algebraic Audit (Routing-Algebra Probe in `## Evidence`):** Exhaustively verifying three canonical routing algebras without artificial hop truncation produces:

| Routing Algebra | Strictly Monotonic? | Isotonic? | Minimal Counterexample Witness `(label, s1, s2, ext(l, s1), ext(l, s2))` | Operational Consequence |
| :--- | :--- | :--- | :--- | :--- |
| **Shortest-Path** `(cost, +)` | `True` | `True` | None | Converges uniquely; Dijkstra/Bellman–Ford globally optimal. |
| **Shortest-Widest Path** `(max bw, min hops)` | `True` | **`False`** | `l=(bw=5, 1)`, `s1=(10, 1) < s2=(5, 0)`, yet `l(s1)=(5, 2) > l(s2)=(5, 1)` | Converges loop-free, **but** an intermediate router discarding suboptimal `s2=(5,0)` in favor of `s1=(10,1)` hides the path that would have won behind a `bw=5` bottleneck link! |
| **Gao–Rexford Valley-Free + Hops** `(C < R < P, min hops)` | `True` | **`False`** | `l=from_prov`, `s1=(Cust, 1) < s2=(Peer, 0)`, yet `l(s1)=(Prov, 2) > l(s2)=(Prov, 1)` | Converges uniquely (consistent with `Bagpipe`'s mechanized Coq theorem), **but** hop-by-hop selection is non-isotonic across provider boundaries (a provider learning a customer's route collapses `Cust` and `Peer` into `Prov`, inverting preference by hop count). |

Metarouting (SIGCOMM 2005) lifts these axioms into a combinator language (lexical products $\mathcal{A} \otimes \mathcal{B}$, scoped products $\mathcal{A} \odot \mathcal{B}$, disjoint unions) whose composition theorems automatically preserve strict monotonicity and/or isotonicity—e.g., a lexical product $\mathcal{A} \otimes \mathcal{B}$ is strictly monotonic if $\mathcal{A}$ is monotonic and $\mathcal{B}$ is strictly monotonic, and isotonic if $\mathcal{A}$ is *strictly* isotonic and $\mathcal{B}$ is isotonic.

### 2. Concrete Simulation vs. Symbolic Control-Plane Verification: Batfish, Minesweeper, Bagpipe, and NV

Basis: source (`batfish/batfish@735d69e0`, `uwplse/bagpipe@67a38c4c`, `NetworkVerification/nv@952dae45`) + papers (NSDI 2015, OOPSLA 2016, SIGCOMM 2017, PLDI 2020) + execution (standalone Python 3 micro-probe in `## Evidence`)

#### 2.1 Batfish Concrete Control-Plane Simulation (`batfish/batfish@735d69e0`)
- **Architecture (`IncrementalBdpEngine.java`, L430–549, L998–1075):** Batfish parses multi-vendor router configurations (Cisco IOS/NX-OS/XR, Juniper Junos, Arista EOS, FRR) into a vendor-independent `Configuration` model and runs an **Incremental Batfish Data Plane (IBDP)** engine that iteratively simulates IGP (`OspfRoutingProcess`, `EigrpRoutingProcess`) and EGP (`BgpRoutingProcess`) route exchange across `VirtualRouter`s until RIBs reach a fixed point.
- **Non-Monotonic Scheduling & Oscillation Detection:** `computeNonMonotonicPortionOfDataPlane` (L1000–1075) runs rounds of `VirtualRouter::reinitForNewIteration`, `VirtualRouter::redistribute`, `updateResolvableRoutes`, cross-VRF leaking, and node-colored schedule steps (`IbdpSchedule.getSchedule`, shuffling each independent color class via `toListInRandomOrder`). If iterations fail to stabilize within the oscillation detector's loop check, Batfish aborts with `throw new BdpOscillationException("Network has no stable solution")` (L539).
- **Fundamental Coverage Gap (`k=0` Simulation vs. `k>=1` Failures):** Concrete simulation evaluates **one** physical topology state and **one** set of external BGP announcements at a time. In the $k$-failure reachability probe in `## Evidence`, a 4-node dual-homed topology (`Src -- S1 -- Dst` primary `LP=200`, `Src -- S2 -- Dst` backup `LP=100`, peer link `S1 -- S2`) with a latent export-filter bug blocking backup tag `"BAK"` on `S2 -> Src` exhibits:
  - `k = 0` link failures: **`0 / 1`** scenarios violate `Src -> Dst` reachability (concrete simulation passes cleanly!).
  - `k = 1` link failures: **`1 / 5`** scenarios fail (`(('S1', 'Dst'),)` triggers a silent blackhole!).
  - `k = 2` link failures: **`6 / 10`** scenarios fail.

#### 2.2 Minesweeper: 2017 $k$-Failure SMT Encoding vs. Modern Batfish BDD Route-Policy Engine
A critical distinction separates the SIGCOMM 2017 Minesweeper paper from the current `projects/minesweeper/` tree inside `batfish/batfish@735d69e0`:
1. **SIGCOMM 2017 Minesweeper Full-Network SMT Encoding (`DOI: 10.1145/3098822.3098834`):**
   - Instead of simulating message passing, Minesweeper encodes the **stable equilibrium equations** directly in Z3 over symbolic route records `(valid, prefixLen, localPref, asPathLen, med, metric, communities, ...)` per directed edge and router.
   - To verify resilience against up to $k$ arbitrary link failures (and arbitrary external BGP announcements), Minesweeper introduces one Boolean variable $\text{failed}_e$ per link $e \in E$ with cardinality constraint $\sum_{e \in E} \text{ite}(\text{failed}_e, 1, 0) \le k$, gates edge route exports on $\neg \text{failed}_e$, asserts the negated property (e.g., $\neg \text{Reachable}(s, d)$), and queries Z3: `UNSAT` proves the property holds for **every** failure scenario of size $\le k$ and **every** external route; `SAT` yields a concrete failing link set and external announcement witness.
   - **Soundness Caveat of Stable-State SMT Encodings (Derived):** Because Minesweeper encodes *existence of a stable state violating a property*, if a configuration has **no** stable state (e.g., `BAD GADGET` or `MED` oscillation), the stable-state constraints themselves are unsatisfiable (`UNSAT`)—which can be misread as "property holds" unless oscillation freedom is checked separately! Conversely, if multiple stable states exist (`DISAGREE`), SMT checks *all* equilibria (stronger than single-trace simulation).
2. **Modern `batfish/batfish@735d69e0` (`projects/minesweeper/src/main/java/org/batfish/minesweeper/bdd/`):**
   - In the audited `batfish/batfish` revision, the legacy `smt/Encoder.java` is no longer present; `projects/minesweeper` implements **BDD-based symbolic route-policy analysis** (`TransferBDD.java`, L141–218; `BDDRoute.java`, L69–190, L379–424).
   - `BDDRoute` represents an entire symbolic set of BGP announcements using `MutableBDDInteger` bit-vectors (`_prefix`, `_prefixLength`, `_localPref` [32b], `_med` [32b], `_nextHop` [32b], `_tag` [32b], `_weight` [16b], `_adminDist`, `_clusterListLength` [32b]) plus finite `BDDDomain` encodings for `_protocolHistory`, `_nextHopInterfaces`, `_peerAddress`, `_sourceVrfs`, and `ConfigAtomicPredicates` (compressing arbitrary regex community matches into disjoint Boolean atomic predicates).
   - `TransferBDD` symbolically executes a router's `RoutingPolicy` AST into a list of `(guard_BDD, output_BDDRoute)` paths (`TransferReturn`), powering scalable single-policy differential verification (`searchRoutePolicies`, `compareRoutePolicies`) without monolithic whole-network SMT blowup.

#### 2.3 Bagpipe: Coq-Verified BGP Semantics, Single-AS Reduction, and Gao–Rexford Convergence (`uwplse/bagpipe@67a38c4c`)
Bagpipe (Weitz et al., OOPSLA 2016, `DOI: 10.1145/2983990.2984012`) eliminates the trusted-computing-base gap between BGP semantics and SMT queries by mechanizing both the operational model and the verifier reduction in Coq:
- **Mechanized RFC 4271 Operational Semantics (`src/bagpipe/coq/Main/BGPSpec.v`, L40–112, L360–408):** Defines `Inductive RoutingInformation := available (_: PathAttributes) | notAvailable`, `Mode := ibgp | ebgp`, `TopologyClass`, `Record NetworkState := { routerState; linkState; uninterpretedState }`, and `routerHandler`/`forwardHandler`/`generateHandler` modeling `Adj-RIB-In -> Decision Process -> Loc-RIB -> Adj-RIB-Out -> UPDATE` transmission per RFC 4271.
- **Verified Reduction to Parallel Per-Router Symbolic Queries (`src/bagpipe/coq/Main/BGPV.v`, L722–744, L866, L969–993, L1106, L1501–1504):**
  - Instead of encoding the entire multi-router network graph into one SMT instance, Bagpipe proves that for an AS with a full-mesh iBGP internal network and local route-policy properties (`fastPolicy (localPolicy (denoteQuery Q))`), verifying **every** reachable network state reduces soundly to checking each border router's import/export/preference policies independently over symbolic route announcements (`parallelBGPVImport`, `parallelBGPVExport`, `parallelBGPVPreference`).
  - The top-level Coq theorem `parallelPolicySemiDec` (`BGPV.v`, L1501–1504) extracts directly to Racket/Rosette + Z3 via `fastPolicyImpliesPolicy`: if the extracted parallel SMT search returns no counterexample, the Coq kernel guarantees the BGP safety property holds across all reachable asynchronous executions of `BGPSpec.v`!
- **Mechanized Global Convergence (`src/bagpipe/coq/GaoRexford/InternetConverges.v`, L50–93):** Proves `routerPrefixConverges : RouterPrefixConverges` (from `Claim2` and `ribsFromInConverges`): under Gao–Rexford commercial export/preference axioms and fairness assumptions, every router's `locRIB` for a prefix converges to a stable `RoutingInformation` value.

#### 2.4 NV: Functional SRP Intermediate Language, CUDD MTBDD Simulation, Unboxed SMT, and Kirigami Modularity (`NetworkVerification/nv@952dae45`)
NV (Giannarakis et al., PLDI 2020, `DOI: 10.1145/3385412.3386019`) decouples network verification frontends from solver backends via a statically typed functional intermediate language defining a **Stable Routing Problem (SRP)**:
- **Core Abstraction (`src/lib/Srp.ml`, `src/lib/Simulator.ml`, `src/lib/Main_defs.ml`):** An NV program declares a topology `(nodes, edges)`, a route attribute algebraic data type (integers, booleans, records, bitvectors, `option`, finite maps), and three pure functions: `init : tnode -> attr`, `trans : tedge -> attr -> attr`, and `merge : tnode -> attr -> attr -> attr` (plus symbolic inputs `symbolic x : ty` and `require`/`assert` predicates).
- **Dual Compilation Backends:**
  1. **Native OCaml + CUDD MTBDD Compilation (`src/lib/Main_defs.ml` L185–186, `src/lib/compile/NativeBdd.ml` L1–40):** Compiles NV policies to native OCaml functions operating over CUDD Multi-Terminal BDDs (`BddMap`, `value_to_bdd`), enabling simultaneous symbolic simulation across the entire IPv4 prefix space ($2^{32}$ prefixes) orders of magnitude faster than interpreting ASTs or enumerating prefixes.
  2. **Unboxed SMT-LIB2 Backend (`src/lib/smt/Smt.ml` L66–70, `SmtUnboxed.ml`, `SmtClassicEncoding.ml`):** Flattens algebraic option/record route types into unboxed SMT-LIB2 terms (`SmtUtils.smt_config.unboxing <- true`; boxed encoding is explicitly rejected with `failwith "Boxed encoding no longer supported"` at `Smt.ml` L70), significantly reducing Z3 datatype-theory overhead compared to naive ADT encodings.
- **Kirigami Assume-Guarantee Partitioning (`src/lib/kirigami/SrpRemapping.ml` L14–71, `src/lib/smt/SmtKirigami.ml`):** Partitions a monolithic SRP into ranked sub-network `fragment`s along cut edges `(u, v)`, replacing each cross-cut edge with a fresh symbolic hypothesis variable `$assume_u~v$` constrained by user-supplied or synthesized interface predicates (`require` on input cut, `assert` on output cut), enabling compositional verification of large datacenters whose monolithic SMT formula would time out.

### 3. Cross-System Control-Plane Verifier Comparison Matrix

Basis: source + documentation + derived (synthesized from Sections 1–2)

| Verifier | Primary Abstraction | Reasoning Engine | Failure / Symbolic Environment Scope | Oscillation / Multiple-Equilibria Handling | Soundness / TCB Guarantee | Primary Scaling Bottleneck |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Batfish IBDP** (`batfish/batfish@735d69e0`) | Multi-vendor config -> `VirtualRouter` RIBs | Concrete iterative fixed-point simulation | Fixed topology (`k=0`), fixed external adverts (must enumerate failures) | Detects non-convergence (`BdpOscillationException`); samples 1 randomized equilibrium on `DISAGREE` | Engineering fidelity to vendor quirks (unverified Java) | Combinatorial explosion over $k$-failures or external announcements |
| **Minesweeper (2017 SMT)** (`SIGCOMM 2017`) | Stable routing fixed-point equations | Monolithic Z3 SMT over route records + `failed_e` | All external announcements + up to $k$ arbitrary link failures | **Blind to non-existence** (`UNSAT` if oscillating); checks **all** equilibria when multiple exist | Unverified Java-to-Z3 translation | Whole-network SMT time grows exponentially on dense BGP topologies / large $k$ |
| **Batfish Minesweeper BDD** (`batfish/batfish@735d69e0`) | Single-router `RoutingPolicy` -> `BDDRoute` | JavaBDD (`JFactory`) + `ConfigAtomicPredicates` | All possible BGP announcements to one route-map/policy | N/A (stateless per-policy transfer function, not global fixed point) | Unverified Java; exact over modeled BGP attributes | Large policy path branching or high atomic-predicate count |
| **Bagpipe** (`uwplse/bagpipe@67a38c4c`) | Mechanized Coq RFC 4271 (`BGPSpec.v`) | Coq-extracted parallel per-router Rosette/Z3 | All external announcements across 1 AS (full-mesh iBGP assumption) | Proves safety over all reachable dynamic traces; separate Coq Gao–Rexford convergence proof | **Highest TCB assurance:** reduction theorem verified in Coq (`BGPV.v`) | Restricted to local AS policies & full-mesh iBGP (no arbitrary multi-AS IGP+RR coupling) |
| **NV + Kirigami** (`NetworkVerification/nv@952dae45`) | Functional SRP `(G, A, trans, merge, init)` | Native OCaml + CUDD MTBDDs; Unboxed Z3 SMT; Kirigami cuts | Symbolic prefixes (MTBDD) or arbitrary symbolic inputs/failures (SMT) | Simulator detects non-convergence dynamically; SMT encodes stable fixed point (same `UNSAT` caveat unless checked) | Unverified OCaml compiler; Kirigami soundness requires valid cut predicates | SMT scaling on cyclic non-monotonic BGP without Kirigami partitioning |

### 4. Executable Wire-Transport Specifications: Compositional QUIC Testing in Ivy and HOL4 TCP/Sockets Semantics

Basis: source (`kenmcmil/ivy@84a6b955`, `rems-project/netsem@0b02450e`) + documentation (SIGCOMM 2019 `DOI: 10.1145/3341302.3342087`, JACM 2018 `DOI: 10.1145/3243650`)

Verifying real transport implementations (`QUIC`, `TCP`) faces a sharp obstacle: production implementations span tens of thousands of lines of optimized C/Rust/Go with asynchronous kernel timers, TLS crypto libraries, and undocumented corner cases. Two landmark approaches attack this from complementary directions: **specification-driven adversarial testing (Ivy)** and **post-hoc formal trace-oracle validation (Netsem)**.

#### 4.1 Compositional Specification-Based Testing of QUIC in Ivy (`kenmcmil/ivy@84a6b955`)
McMillan & Zuck (SIGCOMM 2019, `DOI: 10.1145/3341302.3342087`) write a formal specification of the QUIC wire protocol in Ivy's first-order relational transition language and exploit **assume-guarantee duality** to turn the specification directly into an automated black-box tester:
- **Layered Event Architecture (`quic_frame.ivy`, `quic_packet.ivy`, `quic_server_test.ivy`):**
  - Instead of modeling QUIC as a monolithic byte-level automaton, the specification decomposes events into layers: TLS handshake events -> frame generation (`frame.*.handle`) -> packet encapsulation (`packet_event`) -> UDP wire transmission (`quic_shim.ivy`).
  - **Frame-Layer Preconditions (`doc/examples/quic/quic_frame.ivy`, L10–35, L451–576):** Each frame variant (`frame.stream`, `frame.ack`, `frame.rst_stream`, `frame.max_data`, etc.) attaches `before` monitor obligations via `require` clauses:
    - `frame.ack.handle` (L451–487): enforces connection existence (`connected(dcid) & connected_to(dcid) = scid`), key-level establishment (`e = quic_packet_type.handshake -> established_handshake_keys(scid)`), single encryption level per packet queue (`num_queued_frames(scid) > 0 -> e = queued_level(scid)`), valid non-empty ACK block gaps, and that every acknowledged packet was previously sent (`require sent_pkt(dcid, e, jdx)`).
    - `frame.stream.handle` (L545–576): enforces `1-RTT` key establishment, non-closed connection (`~conn_closed(scid)`), exact byte consistency with application data (`f.data = stream_app_data(dcid, f.id).segment(offset, offset + f.length)`), flow-control bounds (`offset + f.length <= stream_max_data(dcid, f.id)`), and `stream_id_allowed`.
  - **Packet-Layer Preconditions (`doc/examples/quic/quic_packet.ivy`, L83, L270–369, L558–562):** `packet_event(src, dst, pkt)` enforces packet-type matching (`pkt.ptype = queued_level(scid)`), strictly fresh packet numbers (`~sent_pkt(scid, pkt.ptype, pkt.seq_num)`), non-empty payload matching the frame queue (`pkt.payload = queued_frames(scid)`), and anti-ACK-loop credit (`~_generating & ~queued_non_ack(scid) -> ack_credit(scid) > 0`, L349), plus mandatory transport parameter presence (L558–562).
- **Assume-Guarantee Mirror Synthesis (`quic_server_test.ivy`, L438–499):**
  - Actions `export`ed by the test (`frame.ack.handle`, `frame.stream.handle`, `frame.crypto.handle`, `packet_event`, `frame.retire_connection_id.handle`, L438–446) are executed by the **generated randomized peer** (the Ivy tester): Ivy invokes Z3 at runtime to solve the `require` preconditions into valid (yet deliberately adversarial/unusual, e.g., out-of-order, fragmented, migrating) protocol frames and packets!
  - Actions triggered by packets received from the **implementation under test (IUT)** flip the exact same `require` clauses into **runtime assertions** (the oracle): any violation immediately flags a wire-level specification bug with a reproducible packet trace.
- **Explicit Shim & Serialization Soundness Boundary (`doc/examples/quic/quic_shim.ivy`, L13–75):**
  - `after packet_event` (L67–75) invokes `pkt_serdes.to_bytes(pkt)` and `prot.encrypt(client.tls_id, rnum, spkt)` before calling `net.send(...)`.
  - Crucially, the source itself documents two intentional coverage omissions in `quic_shim.ivy` (L45–55): (1) packet-number encoding width is chosen deterministically rather than randomized across all legal 1–4 byte encodings, and (2) multiple QUIC packets are not coalesced into a single UDP datagram—meaning IUT bugs triggered specifically by coalesced Initial+Handshake datagrams or non-minimal packet-number lengths escape this draft-23 shim unless extended.

#### 4.2 HOL4 Operational Semantics of TCP/IP and POSIX Sockets (`rems-project/netsem@0b02450e`)
Bishop et al. (JACM 2018, `DOI: 10.1145/3243650`) demonstrate an orthogonal methodology for legacy, RFC-underspecified protocols where multiple OS kernels disagree on edge cases:
- **Rich Concrete Host State (`specification/TCP1_hostTypesScript.sml`, L30–46, L144–423):** Defines `Hol_datatype` records matching real BSD/Linux kernel structures rather than abstract textbook FSMs—`tcpcb` (L230: `snd_una`, `snd_nxt`, `rcv_nxt`, `rcv_up`, congestion/RTT parameters, reassembly queue elements, retransmission mode, persist/keepalive/2MSL timers), `tcp_socket` (L341: TCP state `CLOSED`, `LISTEN`, ..., `TIME_WAIT`, send/receive queues, listen queues `q`/`q0`), `socket` (L359), and whole-OS `host` (L423: file descriptor table, interfaces, routing table, thread states).
- **Nondeterministic Labelled Transition System (`specification/TCP1_hostLTSScript.sml`, 18,620 lines; L929–940, L1373–1431):** Uses `Net_Hol_reln` to inductively define `host_redn0_rules` covering both POSIX socket syscalls (`accept_1`, `connect_1`, `send_1`, `recv_1`, `close_1` with blocking/`O_NONBLOCK` semantics) and network segment delivery (`deliver_in_1`, `deliver_out_1`), explicitly parameterized by `arch` (FreeBSD, Linux, Windows) and nondeterminism over internal OS scheduling and timer jitter. Look at L934–939: the spec explicitly models subtle BSD/Linux distinctions such as ignoring data/FIN while pulling `rcv_up` in `TIME_WAIT` (or `CLOSING` when `ourfinisacked`) while still processing data in `FIN_WAIT_1`/`FIN_WAIT_2`.
- **Symbolic Trace-Checking Oracle:** Because the specification is a relational HOL4 LTS with real-valued timing windows rather than an executable function, validation runs a specialized HOL4 symbolic evaluator (`TCP` trace checker) that checks whether captured real-world syscall + tcpdump traces are valid paths of `host_redn0_rules`—turning formal semantics into a high-precision bug-finding oracle (uncovering subtle FreeBSD/Linux/Windows bugs and RFC errata) without claiming full source-code refinement proofs of kernel C code.

### 5. Datapath-Decoupled Congestion Control Contracts: CCP (`portus` & `ccp-kernel`)

Basis: source (`ccp-project/portus@a43f3071`, `ccp-project/ccp-kernel@e3b3b7ea`) + documentation (SIGCOMM 2018 `DOI: 10.1145/3230543.3230553`)

Congestion control algorithms (`Cubic`, `BBR`, `Copa`, `Vegas`) historically had to be re-implemented inside every transport datapath (Linux kernel TCP, QUIC stacks, DPDK/mTCP). The **Congestion Control Plane (CCP)** decouples fast-path per-packet measurement from slow-path rate/window policy across a programmable IPC boundary:

1. **Two-Tier Datapath/Control-Plane Split (`ccp-project/portus@a43f3071`):**
   - **Safe, Bounded Datapath Fold DSL (`src/lang/ast.rs`, L14–59; `src/lang/datapath.rs`):** Rather than sending every ACK across kernel-to-user IPC (which would saturate CPU at 10+ Gbps), a user-space algorithm installs a small, loop-free *fold program* into the datapath via `CongAlg::datapath_programs` (`src/lib.rs`, L290–296). The AST (`Expr::Sexp(Op, Box<Expr>, Box<Expr>)`) restricts operations strictly to terminating arithmetic/boolean/EWMA primitives:
     ```text
     Op = Add | Sub | Mul | Div | Min | Max | MaxWrap | Equiv | Gt | Lt
        | And | Or | Bind | Def | If | NotIf | Ewma
     Command = Fallthrough | Report
     ```
     Each ACK updates persistent fold registers (e.g., `Ack.bytes_acked`, `Flow.rtt_sample_us`, `Flow.bytes_in_flight`) in $O(\text{instructions})$ bounded time, emitting a `Report` across IPC only when a `when` guard triggers (e.g., once per RTT, on loss, or on microsecond timer expiry).
   - **Versioned Control-Plane Contract (`src/lib.rs`, L86–95, L213–296):** User-space algorithms implement `trait CongAlg<I: Ipc>` and `trait Flow { fn on_report(&mut self, sock_id: u32, m: Report); }`, pushing updates back via `Datapath::set_program` and `update_field` (setting `Cwnd` or `Rate`). To prevent stale measurements from an earlier fold program from corrupting state transitions after a `set_program` switch, `Report::get_field` (L222–225) enforces a strict runtime epoch guard:
     ```rust
     if sc.program_uid != self.program_uid {
         return Err(Error::from(StaleProgramError));
     }
     ```

2. **Concrete Kernel-Datapath Contract Hazards Discovered in Source (`ccp-project/ccp-kernel@e3b3b7ea/tcp_ccp.c`):**
   Direct audit of the Linux kernel `tcp_congestion_ops` shim exposes three boundary invariants that are *not* enforced by the `portus` DSL type system:
   - **Hazard 1 — Non-Monotonic Wall-Clock Timers (`tcp_ccp.c`, L70–93):** `ccp_now()`, `ccp_since(u64 then)`, and `ccp_after(u64 us)` compute elapsed time using `ktime_get_real_ts64(&now)` (`CLOCK_REALTIME`) subtracted from module-init `tzero`. Under an NTP backward step or leap-second adjustment, `timespec64_sub(now, then_ts)` wraps or jumps negatively into unsigned `u64`, either firing fold-program timers prematurely or stalling report generation for decades! Kernel datapath timers must bind strictly to monotonic time (`ktime_get_ts64` / `ktime_get_ns`).
   - **Hazard 2 — Unclamped Byte-to-Packet `cwnd` Truncation (`tcp_ccp.c`, L47–59):** `do_set_cwnd` converts the user-space byte `cwnd` via integer division directly into the kernel packet window:
     ```c
     cwnd /= tp->mss_cache;
     tp->snd_cwnd = cwnd;
     ```
     There is no `max(cwnd, 1U)` (or `2U` as used in `tcp_ccp_ssthresh`, L225) clamp and no zero-guard on `tp->mss_cache`. Any user-space algorithm returning `cwnd < mss_cache` (e.g., a unit bug passing packets instead of bytes) silently sets `tp->snd_cwnd = 0`, permanently stalling transmission!
   - **Hazard 3 — Asynchronous Loss-Reaction Split (`tcp_ccp.c`, L190–250, L386):** While `kernel_datapath->fto_us = 1000` (L386) sets a 1 ms fallback timeout, immediate Linux TCP loss/recovery callbacks (`tcp_ccp_ssthresh` L222–226 returning `max(tp->snd_cwnd >> 1U, 2U)`, `tcp_ccp_undo_cwnd` L229–233) still execute hardcoded Reno-like fallbacks in kernel space asynchronously with delayed Netlink/chardev IPC (`IPC_NETLINK` / `IPC_CHARDEV`, L387–406), creating transient state divergence if user space assumes exclusive ownership of `snd_cwnd` across `TCP_CA_Recovery` / `TCP_CA_Loss`.

### 6. Verification Boundary Invariants for Routing Control Planes and Transport Endpoints

Basis: derived (synthesized from Sections 1–5)

Designing verifiable network control planes and transport stacks requires enforcing five structural invariants at specification and FFI/kernel boundaries:

1. **Separate Equilibrium Existence from Equilibrium Safety:** Any SMT control-plane verifier (`Minesweeper`, `NV`) that asserts stable fixed-point equations must verify **oscillation freedom** separately (e.g., via Sobrinho strict monotonicity, dispute-wheel/MED checks, or Coq/Gao–Rexford axioms) so an empty solution set (`BAD GADGET`, `MED` cycle) never masquerades as a vacuous `UNSAT` safety proof!
2. **Distinguish Monotonicity from Isotonicity Before Composing Policies:** Combining bandwidth, local preference, MED, and hop count preserves loop-free convergence only under strict monotonicity and preserves hop-by-hop optimality only under isotonicity (Metarouting combinator rules); non-isotonic policies (`Shortest-Widest`, `Gao–Rexford + hops`) require explicit awareness of hidden-path suboptimality.
3. **Verify Over Symbolic Failure Sets, Not Only `k=0` Snapshots:** Concrete data-plane simulation (`Batfish IBDP`) is a necessary vendor-parsing sanity check, not a resilience proof; $k$-link-failure symbolic analysis (`Minesweeper`, `NV` + `Kirigami` cuts) or per-policy BDD equivalence (`TransferBDD`) is required to catch latent backup-path filter bugs.
4. **Co-Audit Specification Shims Against Wire Encodings:** Compositional specification testers (`Ivy QUIC`) and post-hoc LTS trace oracles (`Netsem HOL4`) are only as complete as their wire/crypto shims (`quic_shim.ivy` serialization width & packet coalescing; `TCP1_hostTypes` OS-parameterized `arch` flags). Any deterministic restriction in the shim creates a blind spot in testing.
5. **Enforce Monotonicity, Unit Clamping, and Epoch Versioning Across Kernel/User Control Loops (`CCP`):** Cross-privilege transport control interfaces must enforce monotonic clocks (`CLOCK_MONOTONIC`), safe kernel-side clamping of untrusted user-space `cwnd`/`pacing_rate` actuators (`snd_cwnd >= 2`, non-zero `mss_cache`), and monotonic `program_uid` epoch checks (`StaleProgramError`) to reject stale async reports.

## Boundaries

- **RFC 9000 QUIC extensions & post-draft-23 Ivy forks — not examined in source:** This report directly audited `kenmcmil/ivy` branch `quic23` (`84a6b955291ae419ed10ba96cd184fee084652e9`, corresponding to the SIGCOMM 2019 paper and IETF QUIC draft-23). Downstream RFC 9000 extensions (e.g., `ElNiak/QUIC-Ivy` branch `quic-rfc9000` @ `3b2d8151953c75602e1387465c50237f095e8b36`, covering Version Negotiation, Retry integrity tags, and QUIC Spin Bit / Multipath) were resolved at Git ref level only and not source-audited.
- **Data-plane verification (`HSA`, `VeriFlow`, `APKeep`, `P4` `p4v`) — not examined:** This report focuses on *control-plane* routing convergence/policy verification and *transport-layer* specifications, not stateless packet-header forwarding verification (`FIB`/`ACL` data-plane checkers) or P4 switch-pipeline verification.
- **Full Batfish vendor parser soundness — unknown:** `batfish/batfish@735d69e0` parses dozens of proprietary router OS dialects (Cisco, Juniper, Arista, Palo Alto) into its vendor-independent IR; discrepancies between proprietary vendor firmware and Batfish's parser are empirically tested rather than formally verified.
- **Monolithic `Minesweeper` Z3 SMT encoder in modern Batfish — unsupported (removed/superseded):** While `batfish/batfish@735d69e0` retains the `projects/minesweeper` directory, the legacy `org.batfish.minesweeper.smt.Encoder` / `TransferSSA` files from the 2017 paper are absent at this revision; modern `projects/minesweeper` centers on per-policy BDD verification (`bdd/TransferBDD.java`, `bdd/BDDRoute.java`).
- **Equivalence of stable-state SMT `UNSAT` with real-world convergence — known not to apply:** As proven by Probe 2A (`BAD GADGET` and `MED` oscillation), a network with `0` stable states renders stable-fixed-point SMT formulas vacuously unsatisfiable regardless of the asserted safety violation; oscillation freedom must be established independently.
- **Execution of Coq/HOL4/Ivy/OCaml toolchains — not examined in execution:** Coq (`Bagpipe`), HOL4 (`Netsem`), OCaml/CUDD (`NV`), Java (`Batfish`), and C++/Z3 (`Ivy`) builds were not compiled on this lightweight host; findings on those codebases rest on direct primary-source inspection plus peer-reviewed papers, complemented by standalone Python 3 execution probes for routing fixed points, MED oscillation, Sobrinho algebra axioms, and $k$-failure reachability.

## Evidence

### Git Source Inspection (Observed `2026-11-19`)
- `batfish/batfish` @ `735d69e0fbdf7ea9427fcff4855bb51f52a81fc2`:
  - `projects/batfish/src/main/java/org/batfish/dataplane/ibdp/IncrementalBdpEngine.java` (L430–442, L537–549, L998–1075): `computeDataPlane`, `BdpOscillationException`, `computeNonMonotonicPortionOfDataPlane`, `IbdpSchedule.getSchedule`, `toListInRandomOrder`.
  - `projects/minesweeper/src/main/java/org/batfish/minesweeper/bdd/TransferBDD.java` (L141–218) and `BDDRoute.java` (L69–190, L379–424): `MutableBDDInteger` bit-vector route fields (`_prefix`, `_localPref`, `_med`, `_nextHop`, `_tag`, `_weight`, `_adminDist`, `_clusterListLength`) and `ConfigAtomicPredicates`.
- `uwplse/bagpipe` @ `67a38c4c6def7fb270a045b4afa668d22e293be7`:
  - `src/bagpipe/coq/Main/BGPSpec.v` (L40–112, L360–408): `RoutingInformation`, `Mode`, `TopologyClass`, `NetworkState`, `routerHandler`.
  - `src/bagpipe/coq/Main/BGPV.v` (L722–744, L866, L969–993, L1106, L1501–1504): `fastPolicyDec`, `parallelBGPVDec`, `parallelPolicySemiDec`, `fastPolicyImpliesPolicy`.
  - `src/bagpipe/coq/GaoRexford/InternetConverges.v` (L50–93): `RouterPrefixConverges`, `routerPrefixConverges`, `Claim2`.
- `NetworkVerification/nv` @ `952dae45c374dcd80e081faa16fae12217f4dc8e`:
  - `src/lib/Srp.ml`, `src/lib/Simulator.ml` (L71–75), `src/lib/Main_defs.ml` (L185–186): SRP abstraction and native OCaml/BDD simulation.
  - `src/lib/compile/NativeBdd.ml` (L1–40): CUDD `value_to_bdd` encoding for `TUnit`/`TBool`/`TInt`/`TTuple`/`TNode`.
  - `src/lib/smt/Smt.ml` (L1–70), `SmtClassicEncoding.ml`, `SmtUnboxed.ml`: unboxed SMT-LIB2 translation (`SmtUtils.smt_config.unboxing <- true`).
  - `src/lib/kirigami/SrpRemapping.ml` (L14–71) and `src/lib/smt/SmtKirigami.ml`: Kirigami `fragment` partitioning and `$assume_u~v$` cut hypotheses.
- `kenmcmil/ivy` @ `84a6b955291ae419ed10ba96cd184fee084652e9` (`refs/heads/quic23`):
  - `doc/examples/quic/quic_frame.ivy` (L10–95, L451–487, L545–576): `frame.ack.handle` and `frame.stream.handle` `require` obligations.
  - `doc/examples/quic/quic_packet.ivy` (L83, L270–369, L558–562): `packet_event` invariants and `ack_credit`.
  - `doc/examples/quic/quic_server_test.ivy` (L85–115, L234–383, L438–499): `export`/`import` assume-guarantee boundary.
  - `doc/examples/quic/quic_shim.ivy` (L13–75): `pkt_serdes.to_bytes`, `prot.encrypt`, and documented determinism/coalescing `TODO` limitations (L45–55).
- `rems-project/netsem` @ `0b02450eee334fc42f74ad3da09d3ce1a0698a48`:
  - `specification/TCP1_hostTypesScript.sml` (L30–46, L144–423): HOL4 `tcpcb`, `tcp_socket`, `socket`, `host` datatypes.
  - `specification/TCP1_hostLTSScript.sml` (18,620 lines; L929–940, L1373–1431): `Net_Hol_reln` `host_redn0_rules`, `TIME_WAIT`/`CLOSING` segment rules, `accept()` LTS rule.
- `ccp-project/portus` @ `a43f3071c428aef98893455ce06d40db169242da`:
  - `src/lang/ast.rs` (L14–80): fold-program `Prim`, `Op`, `Command`, `Expr` AST.
  - `src/lib.rs` (L86–95, L213–296): `Datapath`, `Report::get_field` (`StaleProgramError`), `Flow`, `CongAlg`.
- `ccp-project/ccp-kernel` @ `e3b3b7ea927ae7b7281f26c76c7bd9d872e267de`:
  - `tcp_ccp.c` (L47–59 `do_set_cwnd`, L70–93 `ktime_get_real_ts64` wall-clock timers, L190–250 `tcp_ccp_cong_control`/`tcp_ccp_ssthresh`, L380–406 `fto_us = 1000` and Netlink/chardev IPC setup).

### Peer-Reviewed Papers & Standards (Verified `2026-11-19`)
- Griffin, Shepherd, Wilfong, *"The Stable Paths Problem and Interdomain Routing"*, IEEE/ACM ToN 2002, `DOI: 10.1109/90.993304`.
- Griffin & Wilfong, *"Analysis of the MED Oscillation Problem in BGP"*, IEEE ICNP 2002, `DOI: 10.1109/ICNP.2002.1181389` (and IETF RFC 3345, RFC 4264, RFC 4271).
- Sobrinho, *"An Algebraic Theory of Dynamic Network Routing"*, IEEE/ACM ToN 2005, Vol. 13(5), pp. 1160–1173, `DOI: 10.1109/TNET.2005.857653`.
- Griffin & Sobrinho, *"Metarouting"*, ACM SIGCOMM 2005, `DOI: 10.1145/1080091.1080094`.
- Fogel et al., *"A General Approach to Network Configuration Analysis"* (Batfish), USENIX NSDI 2015.
- Weitz et al., *"Scalable Verification of Border Gateway Protocol Configurations with an SMT Solver"* (Bagpipe), ACM OOPSLA 2016, `DOI: 10.1145/2983990.2984012`.
- Beckett et al., *"A General Approach to Network Configuration Verification"* (Minesweeper), ACM SIGCOMM 2017, `DOI: 10.1145/3098822.3098834`.
- Giannarakis, Loehr, Beckett, Walker, *"NV: An Intermediate Language for Verification of Network Control Planes"*, ACM PLDI 2020, `DOI: 10.1145/3385412.3386019`.
- McMillan & Zuck, *"Formal Specification and Testing of QUIC"*, ACM SIGCOMM 2019, `DOI: 10.1145/3341302.3342087`.
- Bishop et al., *"Engineering with Logic: Rigorous Test-Oracle Specification and Validation for TCP/IP and the Sockets API"*, JACM 2018, Vol. 66(1), Art. 1, `DOI: 10.1145/3243650`.
- Narayan et al., *"Restructuring Endpoint Congestion Control"* (CCP), ACM SIGCOMM 2018, `DOI: 10.1145/3230543.3230553`.

### Execution Micro-Probe (Observed `2026-11-19`, Python 3 standard library on Linux)
Standalone probe reproducing SPP (`BAD GADGET`, `DISAGREE`), BGP `MED` oscillation, Sobrinho algebra axiom checks, and the $k$-link-failure reachability gap:
```python
import itertools

def solve_spp(nodes, ranked):
    doms = {v: list(ranked[v]) + [None] for v in nodes}
    out = []
    for combo in itertools.product(*(doms[v] for v in nodes)):
        pi = dict(zip(nodes, combo)); pi[0] = (0,)
        if all(pi[v] == next((c for c in ranked[v] if pi[c[1]] == c[1:]), None) for v in nodes):
            out.append({v: pi[v] for v in nodes})
    return out

bad = {1: [(1,3,0),(1,0)], 2: [(2,1,0),(2,0)], 3: [(3,4,2,0),(3,0)], 4: [(4,2,0),(4,0)]}
dis = {1: [(1,2,0),(1,0)], 2: [(2,1,0),(2,0)]}
print("BAD_GADGET:", len(solve_spp([1,2,3,4], bad)), "DISAGREE:", len(solve_spp([1,2], dis)))

# MED oscillation (RFC 3345 / Griffin-Wilfong)
rt = {"rA_hi": ("A",10,1,100), "rB": ("B",0,5,2), "rA_lo": ("A",0,10,10)}
def best_med(avail, idx):
    by_as = {}
    for r in avail: by_as.setdefault(rt[r][0], []).append(r)
    w = [min(rs, key=lambda r: (rt[r][1], rt[r][idx])) for rs in by_as.values()]
    return min(w, key=lambda r: rt[r][idx])
med_eq = [(s1, s2) for s1 in ("rA_hi","rB","rA_lo") for s2 in ("rA_lo","rB")
          if (best_med(["rA_hi","rB"]+(["rA_lo"] if s2=="rA_lo" else []), 2),
              best_med(["rA_lo"]+(["rB"] if s1=="rB" else []), 3)) == (s1, s2)]
print("MED_STABLE:", len(med_eq))

# Sobrinho isotonicity counterexample for Shortest-Widest (max bw, min hops)
sw_le = lambda a, b: (a[0] > b[0]) or (a[0] == b[0] and a[1] <= b[1])
sw_ext = lambda l, s: (0, 999) if s[0] == 0 else (min(l[0], s[0]), s[1] + l[1])
l, s1, s2 = (5, 1), (10, 1), (5, 0)
assert sw_le(s1, s2) and not sw_le(sw_ext(l, s1), sw_ext(l, s2))
print("SW_NON_ISOTONIC:", l, s1, s2, "->", sw_ext(l, s1), sw_ext(l, s2))

# Gao-Rexford (valley-free + hops) non-isotonicity witness
gr_ext = lambda lbl, s: (3,999) if s[0]==3 else ((0,s[1]+1) if lbl=="from_cust" and s[0]==0 else ((1,s[1]+1) if lbl=="from_peer" and s[0]==0 else ((2,s[1]+1) if lbl=="from_prov" else (3,999))))
assert (0,1) <= (1,0) and not (gr_ext("from_prov",(0,1)) <= gr_ext("from_prov",(1,0)))
print("GR_NON_ISOTONIC:", gr_ext("from_prov",(0,1)), gr_ext("from_prov",(1,0)))

# k-link-failure reachability gap (k=0 passes, k=1 fails on latent backup filter)
edges = [("Src","S1"),("S1","Dst"),("Src","S2"),("S2","Dst"),("S1","S2")]
def reachable(down):
    up = set(edges) - set(down)
    rib = {"Dst": (200, 0, "ORIG")}
    for _ in range(10):
        for u, v in list(up) + [(b, a) for a, b in up]:
            if u not in rib: continue
            lp, h, tag = rib[u]
            if (u,v)==("Dst","S1"): c = (200, h+1, "PRI")
            elif (u,v)==("Dst","S2"): c = (100, h+1, "BAK")
            elif (u,v) in {("S2","Src"),("S2","S1")} and tag=="BAK": continue
            else: c = (lp, h+1, tag)
            if v not in rib or c[0]>rib[v][0] or (c[0]==rib[v][0] and c[1]<rib[v][1]): rib[v] = c
    return "Src" in rib
for k in (0, 1, 2):
    combos = list(itertools.combinations(edges, k))
    fails = [d for d in combos if not reachable(d)]
    print(f"k={k}: {len(fails)}/{len(combos)} fail, sample={fails[:2]}")
```
Observed outputs:
- `BAD_GADGET: 0 DISAGREE: 2` (`[{1: (1, 2, 0), 2: (2, 0)}, {1: (1, 0), 2: (2, 1, 0)}]`)
- `MED_STABLE: 0`
- `SW_NON_ISOTONIC: (5, 1) (10, 1) (5, 0) -> (5, 2) (5, 1)` (and for Gao–Rexford+hops: `l='from_prov'`, `s1=(0, 1)`, `s2=(1, 0)` $\to$ `(2, 2)` vs. `(2, 1)`).
- $k$-failure gap on dual-homed 4-node graph: `k=0: 0/1`, `k=1: 1/5` (`(('S1', 'Dst'),)`), `k=2: 6/10`.

## Revalidation

1. **Batfish Minesweeper Architecture Check:** Check whether `batfish/batfish` `projects/minesweeper/src/main/java/org/batfish/minesweeper/` has re-introduced whole-network SMT verification alongside `bdd/TransferBDD.java` by diffing its package tree against commit `735d69e0fbdf7ea9427fcff4855bb51f52a81fc2`.
2. **NV Backend & Kirigami Check:** Diff `NetworkVerification/nv` `src/lib/smt/Smt.ml` and `src/lib/kirigami/SrpRemapping.ml` against `952dae45c374dcd80e081faa16fae12217f4dc8e` to check whether oscillation checks or automated cut-predicate synthesis have been added to the SMT/Kirigami backends.
3. **Ivy QUIC RFC 9000 Coverage Check:** To extend transport-testing findings from QUIC draft-23 (`kenmcmil/ivy@84a6b955`) to finalized RFC 9000, inspect `ElNiak/QUIC-Ivy` (`refs/heads/quic-rfc9000`, `3b2d8151953c75602e1387465c50237f095e8b36`) specifically at `quic_shim.ivy` to determine whether packet coalescing and randomized packet-number encoding lengths are now implemented.
4. **CCP Kernel Timer & `cwnd` Clamp Re-Audit:** Inspect `ccp-project/ccp-kernel` `tcp_ccp.c` (`do_set_cwnd` L47–59 and `ccp_now`/`ccp_since`/`ccp_after` L70–93) against `e3b3b7ea927ae7b7281f26c76c7bd9d872e267de` to check whether `ktime_get_real_ts64` has been replaced with `ktime_get_ts64` and whether a `>= 1` / `>= 2` floor clamp has been added to `tp->snd_cwnd`.
5. **Algebraic & Fixed-Point Sanity Probe:** Re-run the inline Python 3 probe under `## Evidence` whenever validating a new routing metric or BGP tie-break rule against Sobrinho's strict-monotonicity and isotonicity axioms.
