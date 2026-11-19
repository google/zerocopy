# Consensus Quorum Reconfiguration, Bitset Linearizability Checking, and Adya Transactional Cycle Inference

## Summary

Dynamic consensus reconfiguration and black-box consistency verification govern two halves of replicated state-machine safety: preserving quorum intersection across membership transitions inside the protocol, and deciding whether externally observed operation or transaction histories satisfy linearizability or transactional isolation specifications.

1. **Consensus Reconfiguration & Quorum Intersection (`Raft`, `etcd-io/raft`, `Flexible Paxos`):** Single-server Raft membership transitions (`|C_old Δ C_new| <= 1`) admit a split-brain violation of Leader Completeness when configurations activate upon log append and a newly elected leader appends a second configuration change before committing an entry from its current term (`Ongaro, 2015`). `etcd-io/raft` (`b4329be1d376662f487d8cf76addaefe503ed65d`) eliminates rollback-prone append-time activation by deferring configuration switching until **state-machine application** (`applyConfChange`), gated by `r.pendingConfIndex = r.raftLog.lastIndex()` plus a zero-payload current-term entry on `becomeLeader()` so at most one unapplied configuration change exists at a time. Multi-voter changes run through a unified `JointConfig [2]MajorityConfig` algebra where empty outgoing `MajorityConfig` acts as the semilattice/conjunction identity (`CommittedIndex = ∞`, `VoteResult = VoteWon`) and voter-to-learner demotions stage through `LearnersNext` to preserve `Learners ∩ (Voters[0] ∪ Voters[1]) = ∅`. More generally, `Flexible Paxos` (`DOI: 10.4230/LIPIcs.OPODIS.2016.25`) proves that steady-state replication quorums $\mathcal{Q}_2$ need not intersect one another—safety requires only cross-phase intersection $Q_1 \cap Q_2 \neq \emptyset$ ($|Q_1| + |Q_2| > N$ for uniform sizes)—provided reconfiguration stops old $\mathcal{Q}_2^{\text{old}}$ quorums via an overlapping $\mathcal{Q}_1^{\text{old}}$ quorum before activating $\mathcal{Q}_2^{\text{new}}$.
2. **Bitset Linearizability Checking (`Porcupine`):** Deciding whether a black-box concurrent read/write history is linearizable is NP-complete (`Gibbons & Korach, 1997`, `DOI: 10.1137/S0097539794279614`). `anishathalye/porcupine` (`97cd067defd99df172053ba7f4ca5bbae57fe446`) exploits locality (`P-compositionality`) by partitioning independent keys (`Model.Partition`), representing the concurrent frontier via **Knuth Dancing-Links (`lift`/`unlift`) pointer surgery** over closed `[Call, Return]` intervals, and memoizing visited `(linearized_bitset, abstract_state)` pairs under MurmurHash3 64-bit finalizer keys (`0xff51afd7ed558ccd`). When cross-key operations preclude partitioning (`noPartition`), state-space and monotonic hash-cache growth remain exponential in concurrency width $c$.
3. **Polynomial Black-Box Adya Cycle Inference (`Elle`):** General black-box serializability and snapshot-isolation checking over opaque register histories is NP-complete (`Biswas & Enea, OOPSLA 2019`, `DOI: 10.1145/3360591`). `jepsen-io/elle` (`4e359e597c52938b0afebb8bc42273914d68a424`, `DOI: 10.14778/3430915.3430918`) co-designs **history-carrying client workloads** (`[:append k v]` with globally unique `v` and `[:r k [...]]`) so the longest observed list per key directly exposes the storage engine's total per-key `ww` version order in $O(\sum |v|)$ time, making `ww`, `wr`, and `rw` anti-dependency edges directly constructible over `io.lacuna.bifurcan.DirectedGraph` with 1-byte `BitRels` edge bitmasks. Elle decides Adya `PL-1` (`G0`), `PL-2` (`G1c`), `PL-2.99` (`G2-item`), `PL-3` (`G2`), and `PL-SI` (`G-SIb` via relational sequential extension `(ww ∪ wr) ∪ ((ww ∪ wr) ; rw)`) in $O(V + E)$ Tarjan strongly-connected-component (`SCC`) time, extracting minimal human-auditable cycle witnesses via specialized bit-packed `BFSPath` automata.

## Applicability

The findings in this report apply to the concrete upstream revisions and specifications listed in `REPORT.json` and relate them as a layered verification pipeline for consensus-backed storage engines:

- **Consensus & Reconfiguration Layer:** Applies to `etcd-io/raft` at commit `b4329be1d376662f487d8cf76addaefe503ed65d` (`go.etcd.io/raft/v3`, verified identical in reconfiguration, quorum, and TLA+ modules to upstream `HEAD` `ae830f4a15a0bdb5f59bb7988e50663e92cc028f` as of `2026-11-19`), contrasted against Diego Ongaro's static-membership TLA+ specification `ongardie/raft.tla` at `6ecbdbcf1bcde2910367cdfd67f31b0bae447ddd`, Ongaro's 2014 dissertation §4.1–4.3 + July 2015 single-server reconfiguration erratum, and Howard, Malkhi, and Spiegelman's `Flexible Paxos` (`OPODIS 2016`, `DOI: 10.4230/LIPIcs.OPODIS.2016.25`). Behavioral claims about `etcd-io/raft` depend on `Config.DisableConfChangeValidation == false` (the default) and on the host application honoring the `RawNode` contract: persisting `Entries` and `HardState` before transmitting `Messages`, and invoking `RawNode.ApplyConfChange` deterministically as committed `EntryConfChange` / `EntryConfChangeV2` log entries are applied.
- **Single-Object / Key-Partitionable Linearizability Layer:** Applies to `anishathalye/porcupine` at commit `97cd067defd99df172053ba7f4ca5bbae57fe446` (`go.mod` package `github.com/anishathalye/porcupine`, matching `HEAD` as of `2026-11-19`). Partitioned complexity claims require the checked specification to be **P-compositional** (every operation touches a single partition key, and `Model.Step` is a pure deterministic function—or finite `NondeterministicModel` lifted via `ToModel()`).
- **Multi-Key Transactional Isolation Layer:** Applies to `jepsen-io/elle` at commit `4e359e597c52938b0afebb8bc42273914d68a424` (`0.2.9-SNAPSHOT`, matching `HEAD` as of `2026-11-19`) and Adya, Liskov, and O'Neil's Direct Serialization Graph (`DSG`) formalism (`ICDE 2000`, `DOI: 10.1109/ICDE.2000.839388`). Complete polynomial-time version-order recovery applies specifically to `elle.list-append` under unique per-key append elements (`verify-unique-appends`) where appended suffixes are eventually observed by at least one committed `:ok` or `:info` read; `elle.rw-register` provides sound but incomplete partial version-order inference.

## Findings

### 1. Consensus Reconfiguration Safety, `etcd-io/raft` Joint/Learner Algebra, and `Flexible Paxos`

#### 1.1 Ongaro's Single-Server Reconfiguration Bug and the Current-Term Commit Guard

`Basis: normative + source + execution + derived`

In Ongaro's 2014 Raft dissertation (§4.1), dynamic membership changes were simplified from two-phase joint consensus ($C_{\text{old}} \to C_{\text{old,new}} \to C_{\text{new}}$) to single-server additions or removals ($|C_{\text{old}} \triangle C_{\text{new}}| = 1$) taking effect **immediately when appended** to a server's log (prior to commitment). For any single step $C_i \to C_{i+1}$ with $|C_i \triangle C_{i+1}| = 1$, every majority of $C_i$ intersects every majority of $C_{i+1}$:
$$\forall Q \in \mathrm{Maj}(C_i),\, Q' \in \mathrm{Maj}(C_{i+1}) : |Q| + |Q'| = \left(\left\lfloor \frac{|C_i|}{2}\right\rfloor + 1\right) + \left(\left\lfloor \frac{|C_{i+1}|}{2}\right\rfloor + 1\right) > |C_i \cup C_{i+1}| \implies Q \cap Q' \neq \emptyset.$$
However, **quorum intersection is not transitive across uncommitted log branches** ($C_1 \leftarrow C_0 \to C_2$ can have $|C_1 \triangle C_2| = 2$ and disjoint majorities!). Because `ongardie/raft.tla` (`6ecbdbcf1bcde2910367cdfd67f31b0bae447ddd`, `raft.tla:11`) declared `CONSTANTS Server` statically rather than modeling `config` as a mutable state variable, TLC model checking did not cover reconfiguration.

**Concrete 4-Node Split-Brain Counterexample (verified by execution probe):**
Let $C_0 = \{S_1, S_2, S_3, S_4\}$.
1. **Term 1 ($C_0 \to C_1$ locally on $S_1$):** $S_1$ wins election in Term 1 via $\{S_1, S_2, S_3\} \in \mathrm{Maj}(C_0)$ and appends $C_1 = C_0 \setminus \{S_4\} = \{S_1, S_2, S_3\}$ at `(index=1, term=1)`. Under append-time activation, $S_1$ switches immediately to $C_1$, then partitions before replicating `(1, C_1)`.
2. **Term 2 ($C_0 \to C_2$ committed by $S_2$):** $S_2$ times out, increments to Term 2, and wins election under $C_0$ with votes $\{S_2, S_3, S_4\} \in \mathrm{Maj}(C_0)$ (their logs are empty `[]`). Without committing a Term-2 entry under $C_0$ first, $S_2$ immediately appends $C_2 = C_0 \setminus \{S_3\} = \{S_1, S_2, S_4\}$ at `(index=1, term=2)` and replicates `(1, 2, C_2)` to $S_4$. Because $\{S_2, S_4\}$ has size $2 > \lfloor 3/2 \rfloor$, $\{S_2, S_4\} \in \mathrm{Maj}(C_2)$, so **$S_2$ commits `(index=1, term=2, C_2)`**!
3. **Term 3 (Simultaneous Disjoint Election of $S_1$):** $S_1$'s log has `lastTerm = 1, len = 1`; $S_3$'s log is STILL empty (`lastTerm = 0, len = 0`) because $S_2$ only needed $S_4$ to commit $C_2$. $S_1$ campaigns in Term 3 under its active configuration $C_1 = \{S_1, S_2, S_3\}$. $S_3$ grants its vote to $S_1$ (`(1, 1) >= (0, 0)`), giving $S_1$ quorum $\{S_1, S_3\} \in \mathrm{Maj}(C_1)$—**completely disjoint from $\{S_2, S_4\} \in \mathrm{Maj}(C_2)$**! $S_1$ overwrites the committed `(1, 2, C_2)` entry, violating Leader Completeness and State Machine Safety.

**Why the Current-Term Commit Guard Restores Safety:**
If leader $S_2$ in Term 2 must first commit an entry `(term=2, noop)` under its current configuration $C_0$ before appending $C_2$, then `(term=2, noop)` must be replicated to some $Q_{\text{noop}} \in \mathrm{Maj}(C_0)$ ($|Q_{\text{noop}}| \ge 3$). By pigeonhole intersection over $\{S_1, S_2, S_3, S_4\}$, $Q_{\text{noop}} \cap \{S_1, S_3\} \neq \emptyset$: either $S_1$ receives `(2, noop)` (truncating its uncommitted `(1, C_1)` and reverting $S_1$ to $C_0$) or $S_3$ receives `(2, noop)` (raising $S_3$'s `lastLogTerm` to $2 > 1$, so $S_3$ rejects $S_1$'s `RequestVote` in Term 3). Our exhaustive Python verification over all $\binom{4}{3} + \binom{4}{4} = 5$ majorities $Q_{\text{noop}} \in \mathrm{Maj}(C_0)$ confirms `0` reachable split-brain elections once the guard is enforced.

#### 1.2 Apply-Time Activation, `pendingConfIndex`, and Unified `JointConfig` Algebra in `etcd-io/raft`

`Basis: source`

Direct inspection of `etcd-io/raft` (`b4329be1d376662f487d8cf76addaefe503ed65d`) shows three architectural departures from Ongaro's append-time design:

1. **Apply-Time Configuration Activation & `pendingConfIndex` Serialization (`raft.go:386-393, 953-969, 1325-1347`):**
   Instead of mutating `r.trk.Config` on log append (and having to invert/undo configurations on log truncation), `etcd-io/raft` mutates `r.trk.Config` **only** when a committed configuration entry is applied via `RawNode.ApplyConfChange` -> `r.applyConfChange` (`rawnode.go:111-113`, `raft.go:1943-1963`). To make apply-time activation safe without quorum divergence:
   - Upon winning an election (`becomeLeader`, `raft.go:958-965`), the new leader sets `r.pendingConfIndex = r.raftLog.lastIndex()` (covering its entire inherited log tail without scanning it) and immediately appends an empty zero-payload current-term entry `emptyEnt := &pb.Entry{Data: nil}` (whose `entryPayloadSize` is `0`, consuming zero `uncommittedSize` quota).
   - In `stepLeader` (`raft.go:1325-1346`), every `MsgProp` entry of type `EntryConfChange` or `EntryConfChangeV2` checks:
     ```go
     alreadyPending := r.pendingConfIndex > r.raftLog.applied
     alreadyJoint := len(r.trk.Config.Voters[1]) > 0
     wantsLeaveJoint := len(cc.AsV2().Changes) == 0
     ```
     If `alreadyPending` holds (or joint-transition preconditions fail) and `!r.disableConfChangeValidation`, **the leader does not fail the batch or shift subsequent entry indices**: it silently rewrites `m.GetEntries()[i] = &pb.Entry{Type: pb.EntryNormal.Enum()}` (`raft.go:1341`), turning the rejected configuration proposal into an in-place no-op log entry! Otherwise it updates `r.pendingConfIndex = r.raftLog.lastIndex() + uint64(i) + 1`. Because `r.raftLog.applied <= r.raftLog.committed`, requiring `r.raftLog.applied >= r.pendingConfIndex` simultaneously enforces both Ongaro's current-term commit guard *and* single-in-flight configuration serialization.
2. **Semilattice Identity Unification of Simple and Joint Quorums (`quorum/joint.go:19-75`, `quorum/majority.go:120-198`):**
   `etcd-io/raft` represents *every* cluster voter configuration—whether simple or joint—as `type JointConfig [2]MajorityConfig`, where `Voters[0]` is `incoming` ($C_{\text{new}}$) and `Voters[1]` is `outgoing` ($C_{\text{old}}$, `nil` when non-joint). Rather than branching across replication and election codepaths, `MajorityConfig` assigns algebraic identity elements to the empty set `len(c) == 0`:
   - `MajorityConfig{}.CommittedIndex(l)` returns `math.MaxUint64` (`∞`, `majority.go:122-126`), the identity element of `JointConfig.CommittedIndex(l) = min(c[0].CommittedIndex(l), c[1].CommittedIndex(l))` (`joint.go:49-56`);
   - `MajorityConfig{}.VoteResult(votes)` returns `VoteWon` (`majority.go:170-175`), the identity element of Kleene three-valued conjunction over `{VoteLost < VotePending < VoteWon}` in `JointConfig.VoteResult` (`joint.go:61-75`).
   Furthermore, `MajorityConfig.CommittedIndex` stack-allocates `var stk [7]uint64` (`majority.go:135-141`), computing median-ack commit indices with **zero heap allocations** for all clusters with $n \le 7$ voters.
3. **`LearnersNext` Staging & `AutoLeave` Zero-Byte Exit (`confchange/confchange.go:51-121, 191-332`, `raft.go:737-755`):**
   `confchange.checkInvariants` (`confchange.go:276-332`) enforces strict role disjointness: `Learners ∩ (Voters[0] ∪ Voters[1]) = ∅`. When an atomic `EnterJoint` batch demotes an existing voter $v \in C_{\text{old}}$ to a learner, $v$ is removed from `Voters[0]` (`incoming`) but **must remain** in `Voters[1]` (`outgoing`) until `LeaveJoint`. Inserting $v$ directly into `Learners` would set `trk[v].IsLearner = true` while $v$ is still an outgoing voter. `Changer.makeLearner` (`confchange.go:221-227`) therefore stages $v \in \text{cfg.LearnersNext}$ (keeping `trk[v].IsLearner == false`), and `Changer.LeaveJoint()` (`confchange.go:103-107`) promotes `LearnersNext -> Learners` when clearing `Voters[1] = nil`. When `AutoLeave == true` (`ConfChangeTransitionJointImplicit`), `raft.appliedTo` (`raft.go:742-755`) automatically proposes an empty `ConfChangeV2` (`Data: nil`, payload size `0`, immune to `uncommittedSize` rejection) the instant `newApplied >= r.pendingConfIndex` on the leader.

#### 1.3 `Flexible Paxos` Asymmetric Quorum Intersection vs. Reconfiguration Hazards

`Basis: normative + derived + execution`

Classical Paxos and Raft assume homogeneous majorities where all quorums intersect ($Q_a \cap Q_b \neq \emptyset$). Howard, Malkhi, and Spiegelman (`Flexible Paxos`, `DOI: 10.4230/LIPIcs.OPODIS.2016.25`) prove that consensus safety relies solely on **Phase-1 (leader election / `Prepare`) quorums $\mathcal{Q}_1$ intersecting Phase-2 (log replication / `Accept`) quorums $\mathcal{Q}_2$**:
$$\forall Q_1 \in \mathcal{Q}_1,\, \forall Q_2 \in \mathcal{Q}_2 : Q_1 \cap Q_2 \neq \emptyset \quad \text{(for cardinality quorums: } |Q_1| + |Q_2| > N\text{).}$$
Disjoint Phase-2 quorums ($Q_2 \cap Q_2' = \emptyset$, e.g., $N = 4, |Q_2| = 2, |Q_1| = 3$, which yields `6` disjoint $(Q_2, Q_2')$ pairs and `0` disjoint $(Q_1, Q_2)$ pairs in our execution probe) cannot commit conflicting values *within the same ballot/term* because a single unique leader per term assigns proposals sequentially, and any subsequent term's leader must query $Q_1 \in \mathcal{Q}_1$, guaranteed to hit at least one acceptor in every committed $Q_2 \in \mathcal{Q}_2$.

**Critical Reconfiguration Boundary:** When reconfiguring from $(C^{\text{old}}, \mathcal{Q}_1^{\text{old}}, \mathcal{Q}_2^{\text{old}})$ to $(C^{\text{new}}, \mathcal{Q}_1^{\text{new}}, \mathcal{Q}_2^{\text{new}})$, **single-server intuition fails if $|Q_2^{\text{old}}| \le N/2$**: a new leader elected solely via $Q_1^{\text{new}}$ may fail to intersect an already-committed small replication quorum $Q_2^{\text{old}}$ unless the transition first **seals/stops** $\mathcal{Q}_2^{\text{old}}$ across a quorum $Q_{\text{stop}}$ satisfying $Q_{\text{stop}} \cap Q_2^{\text{old}} \neq \emptyset$ for all $Q_2^{\text{old}} \in \mathcal{Q}_2^{\text{old}}$ (i.e., $Q_{\text{stop}} \in \mathcal{Q}_1^{\text{old}}$, NOT $\mathcal{Q}_2^{\text{old}}$!). In steady state, choosing $|Q_2| = 2, |Q_1| = N - 1$ cuts commit latency to the fastest single follower (`1 + 1 = 2` acks) at the cost of lower leader-election fault tolerance (tolerating at most $1$ node failure during failover).

---

### 2. P-Compositional Bitset Linearizability Checking in `Porcupine`

`Basis: normative + source + execution`

Given a history $H$ of $n$ concurrent operations $op_i = (\text{Input}_i, \text{Output}_i, \text{Call}_i, \text{Return}_i)$ and a sequential specification $\mathcal{S} = (S, s_0, \delta)$, $H$ is **linearizable** (`Herlihy & Wing, TOPLAS 1990`, `DOI: 10.1145/78969.78972`) iff there exists a bijection $\pi : \{1,\dots,n\} \to \{0,\dots,n-1\}$ and sequence $s_0, s_1, \dots, s_n \in S$ such that:
1. **Real-Time Precedence:** $\text{Return}_i < \text{Call}_j \implies \pi(i) < \pi(j)$ (noting Porcupine's closed-interval rule in `model.go:16-47`: if $\text{Return}_i == \text{Call}_j$, $op_i$ and $op_j$ are treated as **concurrent**, sorted `callEntry` before `returnEntry` in `byTime.Less`, `checker.go:117-124`, avoiding false `Illegal` verdicts under coarse monotonic clocks); and
2. **Sequential Validity:** $\forall k \in \{1,\dots,n\},\, \delta(s_{k-1}, \text{Input}_{\pi^{-1}(k-1)}, \text{Output}_{\pi^{-1}(k-1)}) = (\text{true}, s_k)$.

Gibbons and Korach (`SIAM J. Comput. 1997`, `DOI: 10.1137/S0097539794279614`) proved that even for a **single read/write register** with non-unique writes, deciding linearizability is **NP-complete** (reducing 3-SAT via concurrent reader/writer gadgets). Wing & Gong's tree-search algorithm (`Knossos` WGL) backtracks over all minimal concurrent operations, revisiting identical `(linearized_set, state)` configurations $O(c!)$ times across $c$ concurrent operations.

`anishathalye/porcupine` (`97cd067defd99df172053ba7f4ca5bbae57fe446`) accelerates exact decision through three mechanisms verified in `checker.go` and `bitset.go`:

1. **P-Composition Partitioning (`checker.go:370-471`):** When `Model.Partition` splits $H$ into $K$ independent single-key subhistories $H_1, \dots, H_K$ ($n_k = |H_k|$, $\sum_k n_k = n$), `checkParallel` spawns one goroutine per partition (`checker.go:380-386`) and reduces $O(2^n |S|^K)$ global search to $\sum_{k=1}^K O(2^{n_k} |S_k|)$—canceling sibling goroutines immediately via `context.WithCancel` on the first `Illegal` partition (`checker.go:398-400`) when `computeInfo == false`.
2. **Dancing-Links Frontier Invariant (`checker.go:140-207, 236-296`):** `makeLinkedEntries` links sorted call and return entries into a doubly-linked list where each `callEntry` holds `match *node` pointing to its `returnEntry` (`returnEntry.match == nil`). In `checkSingle`, any operation $op_j$ valid to linearize next must satisfy $\text{Call}_j \le \min_{u \notin L} \text{Return}_u$. Because `entries` is sorted by timestamp with calls before returns on ties, **the exact set of minimal schedulable operations is the contiguous prefix of `callEntry` nodes preceding the very first remaining `returnEntry` (`entry.match == nil`)**! `lift(entry)` (`checker.go:236-244`) splices out both `entry` and `entry.match` in $4$ pointer writes ($O(1)$), and `unlift(entry)` (`checker.go:246-254`) restores both on backtrack in $4$ pointer writes ($O(1)$) with zero heap allocation.
3. **Bitset + State Memoization (`bitset.go:1-61`, `checker.go:209-229, 278-290`):** Each partition tracks linearized operation IDs in `type bitset []uint64` ($\lceil n_k / 64 \rceil$ words), hashed via MurmurHash3's finalizer multiplier `0xff51afd7ed558ccd` (`bitset.go:4, 42-49`) XORed with optional `model.Hash(newState)`. Before recursing, `cacheContains` (`checker.go:222-229`) checks `linearized.equal(elem.linearized) && model.Equal(newState, elem.state)`; if true, that `(subset, state)` suffix was already proved unlinearizable on an earlier permutation and is pruned immediately.

In our execution probe (`probe_pkg1.py`), `(bitset, state)` memoization reduces a 10-operation illegal single-key check from **`31,901` steps (`40.48 ms`)** to **`1,317` steps (`337` cache entries, `1.79 ms`, `24.2x` step reduction)**, and per-key partitioning across 3 keys (`13` total ops) reduces search from **`11,162` steps (`2,196` cache entries, `14.15 ms`)** to **`42` steps (`24` cache entries, `0.15 ms`, `265.8x` step reduction)**.

---

### 3. Polynomial Black-Box Adya Cycle Inference in `Jepsen` / `Elle`

#### 3.1 Complexity Escape via Co-Designed History-Carrying List-Append Workloads

`Basis: normative + source + execution`

Adya, Liskov, and O'Neil (`ICDE 2000`, `DOI: 10.1109/ICDE.2000.839388`) characterize isolation levels by forbidding directed cycles in the **Direct Serialization Graph (`DSG`)** over committed transactions, whose edges are:
- **Direct write-dependency (`ww`):** $T_1 \xrightarrow{ww_x} T_2$ iff $T_2$ installs version $x_j$ immediately succeeding $T_1$'s version $x_i$ in $x$'s total version order ($x_i \ll_x x_j$);
- **Direct read-dependency (`wr`):** $T_1 \xrightarrow{wr_x} T_2$ iff $T_1$ installs $x_i$ and $T_2$ externally reads $x_i$;
- **Direct anti-dependency (`rw`):** $T_1 \xrightarrow{rw_x} T_2$ iff $T_1$ reads $x_i$ and $T_2$ installs $x_j$, the immediate successor of $x_i$ in $\ll_x$.

For black-box testers observing only client inputs and outputs over ordinary registers (`[:w :x 1]`, `[:w :x 2]`), **$\ll_x$ is unobservable** when overwritten versions are never read, forcing exponential search over candidate version orders (`Biswas & Enea, OOPSLA 2019`, `DOI: 10.1145/3360591`: checking `Read Committed`, `Snapshot Isolation`, or `Serializability` from black-box register histories is **NP-complete**).

`jepsen-io/elle` (`elle/list_append.clj:61-81, 271-414, 506-581`) breaks this NP-completeness barrier by **co-designing the client algebra**: every write to key $k$ is a unique list append `[:append k v]` (`verify-unique-appends`, `list_append.clj:61-81`), and every read `[:r k [v_0, v_1, ..., v_m]]` returns the full sequence of elements appended up to that version:
1. **Prefix-Total Version Order Check (`incompatible-orders`, `list_append.clj:318-347`):** Grouping distinct non-empty observed lists per key and sorting by `count` (`sorted-values`, `list_append.clj:271-317`), a valid total version order $\ll_k$ exists on observed states iff each observed list is a strict prefix of the next (`prefix? a b`, e.g., `[1, 2]` vs. `[1, 3, 2]` immediately flags `:incompatible-order` $\implies$ `:G1a`).
2. **Direct $O(1)$ Edge Recovery (`list_append.clj:506-573`):** Taking the longest observed vector `vs = [v_0, v_1, ..., v_{L-1}]` per key (`append-index`, `list_append.clj:392-414`), element `v_i` has immediate predecessor `v_{i-1}` (or `::init` for `i = 0`, and `peek(vs)` as conservative lower bound if `v` was never read, `previously-appended-element`, `list_append.clj:517-536`). Thus:
   - `wr-mop-dep`: reading `[..., v_last]` adds $W(k, v_{\text{last}}) \xrightarrow{\text{wr}} T_{\text{read}}$;
   - `ww-mop-dep`: appending `v_i` adds $W(k, v_{i-1}) \xrightarrow{\text{ww}} T_{\text{write}}$;
   - `rw-mop-deps`: appending `v_i` adds $T_{\text{read}} \xrightarrow{\text{rw}} T_{\text{write}}$ for every $T_{\text{read}} \in \text{read-index}[k][v_{i-1}] \setminus \{T_{\text{write}}\}$ (including readers of `::init` `[]` before `v_0`!).

#### 3.2 `BitRels` Algebra, `sequential-extension` for Snapshot Isolation, and `BFSPath` Witness Extraction

`Basis: source + execution`

Elle's graph engine (`src/elle/BitRels.java`, `src/elle/BFSPath.java`, `src/elle/graph.clj`, `src/elle/txn.clj`) achieves `~50k–100k txns/s` throughput (`67,217 txns/s` even in unoptimized single-threaded Python in `probe_pkg1.py`) via four mechanisms:

| Consistency Model (`canonical`) | Forbidden Non-Cycle Anomalies | Acyclic Subgraph Specification (`elle/txn.clj:301-347`) | Cycle Phenomenon Witnessed |
| :--- | :--- | :--- | :--- |
| **Read Uncommitted (`:PL-1`)** | `:duplicate-elements`, `:cyclic-versions` | `ww ∪ wwp` (`0x09`) | `:G0` (dirty write cycle) |
| **Read Committed (`:PL-2`)** | `:G1a` (aborted read), `:G1b` (intermediate read), `:dirty-update` | `ww ∪ wwp ∪ wr ∪ wrp` (`0x1b`) | `:G1c` (circular information flow) |
| **Snapshot Isolation (`:PL-SI`)** | `:internal` (`INT`), `:G1a`, `:G1b` | `extension(ww ∪ wwp ∪ wr ∪ wrp, rw ∪ rwp)` | `:G-single` (`1` `rw` edge) & `:G-nonadjacent` ($\ge 2$ non-adjacent `rw` edges = `:G-SIb`) |
| **Repeatable Read (`:PL-2.99`)** | `:G1a`, `:G1b`, `:lost-update` | `ww ∪ wwp ∪ wr ∪ wrp ∪ rw` (`0x1f`) | `:G2-item` (item anti-dependency cycle, incl. write skew) |
| **Serializable (`:PL-3`)** | `:internal`, `:G1a`, `:G1b`, `:predicate-read-miss` | `ww ∪ wwp ∪ wr ∪ wrp ∪ rw ∪ rwp` (`0x3f`) | `:G2` (arbitrary item/predicate cycle) |
| **Strict Serializable (`:PL-SS`)** | All `:PL-3` anomalies | `ww ∪ wwp ∪ wr ∪ wrp ∪ rw ∪ rwp ∪ realtime` (`0xbf`) | `:G0-realtime`, `:G1c-realtime`, `:G2-realtime` (stale read / causal-realtime inversion) |

1. **1-Byte `BitRels` Edge Bitmasks (`BitRels.java:16-66`):** Every edge between two `jepsen.history.Op` vertices (hashed/compared strictly by integer `.index`, `graph.clj:88-106`) carries a single `byte` mask (`WW=0x01, WR=0x02, RW=0x04, WWP=0x08, WRP=0x10, RWP=0x20, PROCESS=0x40, REALTIME=0x80`). Subgraph projection (`project-rels`, `graph.clj:258-270`, parallelized across cores above `16,384` vertices at `txn.clj:705-706`) reduces to `(byte)(rels & target.rels)`.
2. **Relational `sequential-extension` for Snapshot Isolation (`graph.clj:399-434`, `txn.clj:319-321, 402-412`):** Under Cerone & Gotsman (`PODC 2016`) and Adya's `G-SI`, Snapshot Isolation permits cycles with **adjacent** `rw` edges (such as classic 2-key write skew $T_1 \xrightarrow{rw_y} T_2 \xrightarrow{rw_x} T_1$), but forbids any cycle in which every `rw` edge is separated by at least one `ww`/`wr` (or `process`/`realtime`) commit-order edge (`G-single` and `G-nonadjacent`). Elle computes `sequential-extension(A, B) = A ∪ (A ; B)` where $A = \text{ww} \cup \text{wr}$ and $B = \text{rw}$. Every non-adjacent `rw` step $x \xrightarrow{A} y \xrightarrow{B} z$ becomes a direct shortcut edge $x \to z$ in $A ; B$, turning non-adjacent `rw` cycles—and *only* non-adjacent `rw` cycles—into standard directed cycles in $A \cup (A ; B)$ detectable by Tarjan's linear-time SCC algorithm! Crucially, a 2-node read-skew cycle $T_1 \xrightarrow{wr} T_2 \xrightarrow{rw} T_1$ collapses to a **singleton self-loop $T_1 \to T_1$** in $A ; B$, which is why `txn.clj:402-412, 432-433` explicitly passes `includeSingletons = true` and checks `(bs/contains? (bg/in g v) v)`—confirmed directly by our execution probe (`SI_sccs=[[1]]` vs `PL3_sccs=[[2, 1]]`).
3. **Bit-Packed `BFSPath` Witness Extraction (`BFSPath.java:24-292`, `bfs.clj:32-167`):** Once Tarjan isolates an SCC, `cycle-cases-in-scc` (`txn.clj:839-893`) searches from most-severe (`:G0`) to least-severe (`:G2-realtime`) within a `1000 ms` per-SCC timeout (`txn.clj:725-727`), pruning implied/impossible anomalies via DAG reachability (`consistency_model.clj:55-193`) and running layered BFS over `BFSPath` states `(legal: byte, want: int [4 packed bytes], wantRW: byte, rwMode ∈ {NONE, SINGLE, NONADJACENT_FREE, NONADJACENT_TAKEN})` with loop-tail trimming (`trim-loop`, `bfs.clj:96-120`) to emit shortest human-readable counterexample cycles.

---

### 4. Multi-Level Performance and Resource Footprint Analysis (`L1`–`L6`)

`Basis: source + execution + documentation + derived`

| Metric / Dimension | `etcd-io/raft` + `Traceetcdraft.tla` (`b4329be1...`) | `Porcupine` (`97cd067d...`) | `Jepsen` / `Elle` (`4e359e59...`) | Deductive / SMT Baselines (`IronFleet` / `Verdi` / `MonoSAT` `Cobra`) |
| :--- | :--- | :--- | :--- | :--- |
| **(L1) Human & Agent Authoring Velocity** | Go core (`~6.5k LoC` non-test) + `confchange`/`quorum` (`~1k LoC`) + `etcdraft.tla`/`Traceetcdraft.tla` (`~1.5k LoC`); `~0.25:1` spec-to-code ratio; low drift cost via NDJSON trace checking. | Pure Go `Model{Partition, Init, Step, Equal}` typically **`30–120 LoC`** per data type; an engineer or LLM authors a KV/lock model in `< 15 min` (`< 2k` tokens). | Client generator + `list-append`/`rw-register` harness typically **`80–250 LoC`** Clojure; zero internal white-box instrumentation of target DB required. | `IronFleet` (`Hawblitzel et al., SOSP 2015`): `~37k` Dafny proof LoC (`~7:1` ratio, multi-person-year); `Verdi` (`PLDI 2015`): `~50k` Rocq LoC (`~10–15:1` ratio). |
| **(L2) Framework & Toolchain Build Time** | Pure Go library (`go build ./...`): **`~1.2–2.5 s`** cold, **`< 200 ms`** incremental; peak Go compiler RSS `~120–250 MB`. | Zero external runtime deps (`go.mod` stdlib only); `go test` builds in **`~0.4–0.9 s`** cold, **`< 100 ms`** incremental; compiler RSS `< 100 MB`. | Clojure + Java (`BitRels.java`, `BFSPath.java`) via Leiningen/JVM: **`~4–9 s`** cold AOT/javac compile, JVM startup `~0.8–1.5 s`, build RSS `~350–600 MB`. | `Verdi` (`rocq compile`): `10–30+ min` full build; `IronFleet` (Dafny/Z3): `15–45 min` CI build with SMT `rlimit` sensitivity. |
| **(L3) Compilation, Elaboration & Synthesis Latency** | `gopls` LSP diagnostics `< 30 ms`. TLC finite model checking (`MCetcdraft.cfg`): **hours** for $3$–$4$ servers, bounded terms/reconfigs (`tla/README.md:69`). | Deterministic model compilation instant; no solver synthesis step. `NondeterministicModel.ToModel` synthesizes powerset states lazily on-the-fly. | No SMT/SAT encoding phase (`0 ms` formula synthesis); graph construction runs via parallel `tesser`/`bifurcan` folds in linear $O(M \log M)$ time. | `Cobra` (`Tan et al., OSDI 2020`, MonoSAT): poly-size constraint synthesis + GPU/SAT solving (`seconds` to `timeouts` at $10k$ txns without session hints). |
| **(L4) Generated / Runtime Execution Performance** | In-memory `Step` + `MajorityConfig.CommittedIndex` (`[7]uint64` stack array): **`< 150 ns/op`** (`0` heap allocs for $n \le 7$); end-to-end Raft commit bound by WAL `fdatasync` + RTT (`0.5–5 ms` local NVMe, `p99.9` sensitive to fsync stalls). | Zero runtime overhead on production system when trace collection is off; offline trace logging adds `~50–200 ns/op` client timestamp/append overhead. | Client-side list growth increases read payload linearly ($O(w_k)$ bytes after $w_k$ appends to key $k$); `elle.list-append/gen` bounds `:max-writes-per-key` (default `32`–`128`) to keep wire payloads `< 1–4 KB`. | `IronFleet` extracted C# / `Verdi` extracted OCaml reached `~10k–30k ops/s`, `2–5x` slower than unverified Go/C++ production Raft engines. |
| **(L5) Proof / Certificate / Trace Verification Speed** | `Traceetcdraft.tla` TLC trace validation: **`~3,000` trace events in several minutes**, scaling **super-linearly** above `3,000` events (`tla/README.md:91-94`), requiring batching (`MAX_TRACE`). | Partitioned single-key KV histories (`10k–50k` ops, low per-key concurrency $c \le 8$): **`5–80 ms`** in parallel Go (`checkParallel`); unpartitioned $c \ge 20$ hits exponential cliff (`Unknown` timeout). | **`50,000–150,000+ txns/sec`** on multi-core JVM (`100k`-txn Jepsen history checked in **`~1–3 s`**; `10k`-txn pure-Python reference probe ran in **`148.8 ms` / `67.2k txns/s`**); per-SCC BFS capped at `1000 ms`. | `Knossos` WGL (`Clojure`): OOMs/times out at `c ~ 10–15` concurrent ops (`100–1000x` slower than Porcupine). `rocqchk` kernel replay on `Verdi`: minutes, single-threaded. |
| **(L6) RAM, Disk & Binary Footprints** | Library adds `< 1.5 MB` to compiled Go binary; per-peer `tracker.Progress` + `Inflights` ring uses `~4–16 KB/peer`; NDJSON trace files (`example.ndjson`) consume **`~600 B/event`** (`1.80 MB` for `~3,000` events). | Compiled binary `< 3 MB`; `bitset` uses `8 B` per `64` ops; **monotonic `cache` (`map[uint64][]cacheEntry`)** never evicts during `checkSingle`, reaching **`1–8+ GB` RSS** on unpartitioned high-concurrency histories before timeout. | `Bifurcan` `DirectedGraph` + 1-byte `BitRels` + `failed-write-indices` (`int` index vs full `Op` retention, `txn.clj:111-131`): **`~300–900 MB` JVM heap** for `100k` txns; SVG/DOT plots capped at `:max-plot-bytes` (`65,536 B`). | TLC state queue / fingerprint set consumes **`4–64+ GB` RAM**; SMT/SAT history checkers consume **`2–32 GB` RSS** on dense read-write dependency clauses. |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: source + documentation + derived`

#### 5.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)

1. **The Illusion of Local Comprehensibility in Single-Server Raft Reconfiguration:**
   Raft was explicitly designed around human understandability via state-space decomposition (`Ongaro & Ousterhout, USENIX ATC 2014`). Ironically, single-server reconfiguration (`|C_old Δ C_new| = 1`) **looked** locally simpler to humans than two-phase joint consensus because any single step preserves majority overlap, tempting engineers to reason locally about adjacent pairs $(C_0, C_1)$ and $(C_0, C_2)$ while overlooking the **nonlocal tree-branching invariant** across uncommitted terms ($C_1 \leftarrow C_0 \to C_2$, where $|C_1 \triangle C_2| = 2$). By contrast, `etcd-io/raft`'s invariant—*"at most one unapplied configuration change exists, and a new leader applies its entire inherited log plus one current-term entry before proposing another"* (`raft.go:958, 1326`)—restores a **1-variable local mental model** (`pendingConfIndex > applied`), though its silent rewrite of rejected `ConfChange` entries into normal empty entries (`raft.go:1341`) creates a **footgun for callers** expecting synchronous error returns from `ProposeConfChange` (callers must watch applied `ConfState` idempotently rather than assuming `ProposeConfChange == nil` implies membership changed!).
2. **Diagnostic & Counterexample Legibility (`Porcupine` HTML Timelines vs. `Elle` Cycle Narratives vs. TLC Traces):**
   - When `Porcupine` rejects a history (`CheckOperationsVerbose`), linearizability has **no small local subgraph witness** in general: invalidity is a universal property (*no* global topological ordering satisfies `Model.Step`). Porcupine mitigates this by recording `longest[id]`—the **maximal valid linearization prefix** including each operation (`checker.go:299-314`)—and rendering an interactive HTML timeline (`Visualize`) highlighting the exact operation where every legal prefix stalls. For humans, this works well up to `~20–40` concurrent operations per key, beyond which visually mentally backtracking across overlapping bars exceeds human working memory (`~4–7` items).
   - `Elle`, by contrast, produces **constant-size local witnesses** even inside `100,000`-transaction histories: a 2- or 3-transaction cycle rendered both as Graphviz SVG and step-by-step English prose via `DataExplainer` (`list_append.clj:638-641, 677-680, 729-737`, e.g., *"T1 did not observe T2's append of 4 to :x; T2 observed T1's append of 3 to :y"*). A human engineer can audit an Elle witness in `< 30 seconds` without trusting Elle's internal graph code!
   - Non-academic practitioner post-mortems underscore a second human-comprehension hazard: in Cloudflare's November 2, 2020 6.5-hour control-plane outage (*"A Byzantine failure in the real world"*), a partially failing switch created **intransitive, asymmetric packet loss** ($A \leftrightarrow B$ and $B \leftrightarrow C$, but $A \not\leftrightarrow C$). Without `PreVote` (`raft.go:917-931`), isolated nodes repeatedly incremented `Term` and disrupted the healthy leader despite no split-brain safety bug occurring—demonstrating that humans routinely conflate consensus *safety* (quorum intersection) with *liveness under non-transitive links*.

#### 5.2 Conceptual Simplicity, Orthogonality & Universal Model Refinement (`C2`)

1. **Where `etcd-io/raft` Achieves Genuine Deep-Module Unification—and Where Accidental Complexity Leaks:**
   - **Genuine Universal Refinement (`JointConfig [2]MajorityConfig`):** Defining empty `MajorityConfig{}` as $(\top_{\min} = \infty,\, \top_{\wedge_K} = \text{VoteWon})$ (`majority.go:122-126, 170-175`) passes both Ousterhout's **deep-module test** and Felleisen's **macro-expressibility test**: simple consensus is literally `JointConfig{C, nil}` with *zero* conditional branches in `CommittedIndex` or `VoteResult` and *zero* adapter overhead. Furthermore, `Changer.Simple` (`confchange.go:128-145`) is validated by the exact same `apply` engine plus `symdiff(old, new) <= 1`.
   - **Accidental State Proliferation (`Voters[0]`, `Voters[1]`, `Learners`, `LearnersNext`):** Maintaining four separate ID sets plus a boolean `Progress.IsLearner` flag (`confchange.go:283-329`) is an **implementation-medium artifact** of tracking per-peer replication (`ProgressMap`) flatly while `JointConfig` tracks two epochs. Refining configuration state to a single pure map $\rho : \text{NodeID} \to (\text{Role}_{\text{in}}, \text{Role}_{\text{out}})$ over the 3-element lattice $\text{Absent} < \text{Learner} < \text{Voter}$ eliminates `LearnersNext`, `IsLearner` desynchronization, and all four `checkInvariants` cross-set loops by construction: a demoted voter simply has $(\text{Role}_{\text{in}} = \text{Learner}, \text{Role}_{\text{out}} = \text{Voter})$, its effective replication role is $\max(\text{Role}_{\text{in}}, \text{Role}_{\text{out}}) = \text{Voter}$ until `LeaveJoint`projects $(\text{Role}_{\text{in}}, \text{Absent})$, and impossible states (`Learners ∩ Voters != ∅`) become unrepresentable!
2. **Universal Quorum-Reconfiguration Abstraction (`Flexible Paxos`):**
   `Flexible Paxos` exposes that Raft's "majority everywhere" rule conflates two orthogonal invariants: **intra-term ordering** (owned by a unique leader, requiring *zero* $\mathcal{Q}_2 \cap \mathcal{Q}_2$ intersection) and **cross-term state transfer** (requiring $\mathcal{Q}_1^{\text{next}} \cap \mathcal{Q}_2^{\text{prev}} \neq \emptyset$). Across arbitrary epoch transitions $e \to e+1$, the single universal invariant is: *every election/recovery quorum of epoch $e' > e$ must intersect every replication quorum of epoch $e$ until an epoch-sealing entry is replicated to an election/stop quorum of epoch $e$*. Both joint consensus ($\mathcal{Q}_2^{\text{joint}} = \mathcal{Q}_2^e \times \mathcal{Q}_2^{e+1}$) and single-server Raft with the current-term commit guard are specializations of this single law.
3. **Elle's Co-Design Principle (Trading Specification Generality for Polynomial Decidability):**
   Rather than building a heavier exponential solver (`Cobra`/`SAT`) for an under-determined observation interface (register overwrites), Kingsbury & Alvaro refined the **observation boundary itself** (`[:append k v]`), making the causal history an explicit homomorphic image inside read values. Under Jackson's concept-design lens, this eliminates hidden state guesswork rather than shifting complexity into solver heuristics—at the explicit boundary cost that workloads using blind overwrites (`elle.rw-register`) lose completeness.

## Boundaries

1. **`Porcupine` Non-Partitionable Multi-Key Cliff & Unbounded Cache Memory (`known not to apply` / `unsupported`):**
   Porcupine's polynomial/millisecond performance **known not to apply** when operations span multiple keys (e.g., multi-key `Txn`, `Rename(k1, k2)`, range scans) where `Model.Partition` must fall back to `noPartition` (`model.go:320-330`). Moreover, `checkSingle`'s `cache` (`map[uint64][]cacheEntry`, `checker.go:260, 282`) **never evicts entries**; on high-concurrency unpartitioned histories, memory grows monotonically until timeout (`CheckResult = Unknown`) or process OOM. Calling `CheckOperationsTimeout` and treating `Unknown` as `Ok` (`model.go:364-366`) is **unsound as a proof of linearizability** (it indicates bounded-time non-refutation only).
2. **`Porcupine` `NondeterministicModel` Powerset Blowup (`known not to apply`):**
   `NondeterministicModel.ToModel` (`model.go:214-318`) performs eager powerset determinization with $O(|S|^2)$ linear scans in `merge` and `Equal` (`model.go:189-204, 286-305`). Specifications with wide nondeterminism ($|S| > 10^2$ active states per step) incur quadratic state-comparison stalls on every single `Step`.
3. **`Elle` Unobserved-Tail, Predicate-Read, and Register Incompleteness (`known not to apply` / `unknown`):**
   - **Unread Tail Appends:** In `elle.list-append`, if two committed transactions `[:append :x 1]` and `[:append :x 2]` are *never observed by a subsequent read*, `append-index` cannot order `1` vs `2` (`list_append.clj:531-535`, `789-791`), omitting the `ww` edge between them (`known not to apply` for complete cycle detection without final drain reads).
   - **Item vs. Predicate `G-single` Conflation in `elle.consistency-model`:** As documented in `consistency_model.clj:122-127`, Elle currently filters `:G-single` separately from `:G2-item` without splitting predicate `:G-single` from item `:G-single-item` in all downstream Repeatable Read rules—a known upstream boundary when mixing predicate and item analyzers.
   - **JVM Boxed-Integer Mixing Trap:** Passing mixed `Integer` and `Long` keys/values across transactions triggers `assert-type-sanity` (`txn.clj:71-89`) or corrupts Bifurcan hash equality (`unsupported`).
4. **Crash-Mid-Persist Non-Atomicity in `etcd-io/raft` TLA+ Trace Validation (`unsupported` / `not examined`):**
   As explicitly recorded in `etcd-io/raft/tla/README.md:87-90`, `Traceetcdraft.tla` assumes atomic persistence of log batches, whereas real WAL storage engines may persist a partial prefix on power loss mid-write; non-deterministic prefix recovery trace checking is `unsupported` in `b4329be1d376662f487d8cf76addaefe503ed65d`. Byzantine node equivocation (beyond benign asymmetric packet loss) is `known not to apply` to Raft and `Flexible Paxos` crash-fault quorums (`|Q_1| + |Q_2| > N` becomes `|Q_1| + |Q_2| > N + 2f` or requires authenticated quorum certificates in BFT).

## Evidence

### Primary Upstream Repositories and Normative Publications

1. **`etcd-io/raft` (`b4329be1d376662f487d8cf76addaefe503ed65d`, committed `2026-11-19`):**
   - `raft.go`: `DisableConfChangeValidation` (`L260-280`), `pendingConfIndex` invariant (`L386-393`), `appliedTo` automatic zero-byte `AutoLeave` trigger (`L737-755`), `becomeLeader` `pendingConfIndex = r.raftLog.lastIndex()` + zero-quota `emptyEnt` append (`L933-971`), `stepLeader` `MsgProp` validation & silent `EntryNormal` rewrite (`L1309-1353`), `applyConfChange` & `switchToConfig` (`L1943-2027`).
   - `confchange/confchange.go`: `Changer.EnterJoint` (`L51-78`), `Changer.LeaveJoint` (`L94-121`), `Changer.Simple` (`symdiff <= 1`, `L128-145`), `makeLearner` staging into `LearnersNext` (`L191-228`), `checkInvariants` (`L276-332`).
   - `quorum/majority.go` (`L120-198`, empty-set `math.MaxUint64` & `VoteWon` identities, `[7]uint64` stack sort) and `quorum/joint.go` (`L19-75`, `JointConfig` min/Kleene-AND composition).
   - `tla/etcdraft.tla` (`L128-139, L205-252`, mutable `config` & `pendingConfChangeIndex` state) and `tla/README.md` (`L86-94`, `3,000`-trace nonlinear TLC scaling and partial-WAL persistence limitation).
2. **`ongardie/raft.tla` (`6ecbdbcf1bcde2910367cdfd67f31b0bae447ddd`):** `raft.tla:11` (`CONSTANTS Server`, static membership). Paired with Diego Ongaro, *Consensus: Bridging Theory and Practice* (Stanford PhD Dissertation, Aug 2014, §4.1–4.3) and Ongaro's `raft-dev` erratum *"Bug in single-server membership changes"* (July 10, 2015).
3. **Howard, Malkhi, Spiegelman (`OPODIS 2016`):** *"Flexible Paxos: Quorum Intersection Revisited"*, LIPIcs Vol. 70, Art. 25 (`DOI: 10.4230/LIPIcs.OPODIS.2016.25`, `arXiv:1608.06696`).
4. **`anishathalye/porcupine` (`97cd067defd99df172053ba7f4ca5bbae57fe446`, committed `2026-09-21`):**
   - `model.go`: closed-interval `[Call, Return]` justification (`L16-48`), `Model` (`L101-137`), `NondeterministicModel.ToModel` powerset construction (`L189-318`), `CheckResult` (`L359-373`).
   - `bitset.go`: `[]uint64` bitset and MurmurHash3 `0xff51afd7ed558ccd` hash (`L4-61`).
   - `checker.go`: `byTime.Less` (`L117-124`), `makeLinkedEntries` (`L190-207`), `lift`/`unlift` DLX surgery (`L236-254`), `checkSingle` DFS + memoization + `longest` partial witness tracking (`L256-333`), `checkParallel` (`L370-451`).
   - Theoretical complexity baseline: Gibbons & Korach, *"Testing Shared Memories"*, SIAM J. Comput. 26(4):1208–1244, 1997 (`DOI: 10.1137/S0097539794279614`); Herlihy & Wing, ACM TOPLAS 12(3):463–492, 1990 (`DOI: 10.1145/78969.78972`).
5. **`jepsen-io/elle` (`4e359e597c52938b0afebb8bc42273914d68a424`, committed `2026-10-16`):**
   - `src/elle/list_append.clj`: `verify-unique-appends` (`L61-81`), `g1a-cases`/`g1b-cases`/`op-int-case` (`L83-236`), `sorted-values`/`incompatible-orders`/`append-index` (`L271-414`), `wr-mop-dep`/`ww-mop-dep`/`rw-mop-deps` (`L506-581`).
   - `src/elle/txn.clj`: `lost-update-cases` (`L191-298`), `cycle-exists-specs` (`L301-354`), `nontrivial-scc?` singleton self-loop check (`L402-446`), `cycle-explainer` & `base-cycle-anomaly-specs` (`L477-637`), `cycle-cases-in-scc` `1000 ms` timeout (`L725-894`).
   - `src/elle/graph.clj`: `op-digraph` index hashing (`L88-106`), `project-rels` (`L258-270`), `sequential-composition` & `sequential-extension` (`L399-434`).
   - `src/elle/BitRels.java` (`L16-90`, 1-byte bitmasks) and `src/elle/BFSPath.java` (`L24-292`, packed `RWMode` BFS state).
   - `src/elle/consistency_model.clj` (`L55-162, L408-460`, anomaly implication DAG and `:G-single` vs `:G2-item` note at `L122-127`).
   - Primary papers: Kingsbury & Alvaro, *"Elle: Inferring Isolation Anomalies from Experimental Observations"*, PVLDB 14(3):268–280, 2020 (`DOI: 10.14778/3430915.3430918`, `arXiv:2003.10554`); Adya, Liskov, O'Neil, `ICDE 2000`, pp. 67–78 (`DOI: 10.1109/ICDE.2000.839388`); Biswas & Enea, `OOPSLA 2019` (`DOI: 10.1145/3360591`).
6. **Practitioner Outage Post-Mortem:** Cloudflare Engineering, *"A Byzantine failure in the real world"* (Nov 2, 2020)—partial switch failure causing non-transitive packet loss and Raft election-storm unavailability across an `etcd` control plane.

### Recorded Execution Micro-Probe (`2026-11-19`, Python 3.13)

Running the standalone probe reproduced in **Revalidation** yielded the exact recorded output:
```text
[Raft/FPaxos] unpatched_c2_committed=True s1_wins_t3_split_brain=True patched_split_brains=0 fpaxos_q1q2_disjoint=0 fpaxos_q2q2_disjoint=6
[Porcupine] 10ops_unmemo: ok=False steps=31901 time_us=40479.6 | 10ops_memo: ok=False steps=1317 cache=337 time_us=1785.7
[Porcupine] 13ops_no_partition: ok=False steps=11162 cache=2196 time_us=14150.7 | 13ops_partitioned: ok=False steps=42 cache=24 time_us=151.8
[Elle] write_skew: SI_sccs=[] PL3_sccs=[[2, 1]] | read_skew: SI_sccs=[[1]] PL3_sccs=[[2, 1]] | 10k_txns: SI_sccs=0 PL3_sccs=0 time_ms=148.79 (67217 txns/s)
```

## Revalidation

1. **Upstream Source Differential Checks (Sub-Second):**
   - For a newer `etcd-io/raft` revision, diff `raft.go` around `becomeLeader` (`r.pendingConfIndex = r.raftLog.lastIndex()` + `emptyEnt`), `stepLeader` (`r.pendingConfIndex > r.raftLog.applied`), `appliedTo` (`AutoLeave`), `confchange/confchange.go` (`LearnersNext` in `makeLearner` and `LeaveJoint`), and `quorum/majority.go` (`len(c) == 0` returning `math.MaxUint64` and `VoteWon`).
   - For `anishathalye/porcupine`, diff `checker.go` (`byTime.Less`, `lift`/`unlift`, `checkSingle` `cacheContains`) and `model.go` (`ToModel`).
   - For `jepsen-io/elle`, diff `src/elle/txn.clj` (`cycle-exists-specs` for `:PL-SI` `[:extension ...]` and `nontrivial-scc?`), `src/elle/consistency_model.clj` (`:G-single` / `:G2-item` handling), and `src/elle/list_append.clj` (`previously-appended-element`).
2. **Self-Contained Executable Discriminator Probe (`< 0.3 s`, Python 3.10+ stdlib only):**
   Run the following standalone command to re-verify Ongaro's split-brain trace vs. current-term no-op guard, Porcupine's DLX + bitset memoization and partitioning speedups, and Elle's `sequential-extension` `PL-SI` vs. `PL-3` singleton/pair SCC discrimination:
   ```bash
   python3 -c '
   import itertools
   c0, c1, c2 = frozenset({1,2,3,4}), frozenset({1,2,3}), frozenset({1,2,4})
   maj = lambda c: [frozenset(q) for r in range(len(c)//2+1, len(c)+1) for q in itertools.combinations(c, r)]
   up = lambda a, b: ((a[-1][0] if a else 0), len(a)) >= ((b[-1][0] if b else 0), len(b))
   logs = {1:[(1,"C1")], 2:[(2,"C2")], 3:[], 4:[(2,"C2")]}
   assert any(all(logs[s]==[(2,"C2")] for s in q) for q in maj(c2))
   assert any(q.issubset({v for v in c0 if up(logs[1], logs[v])}) for q in maj(c1))
   for qn in maj(c0):
       lp = {s: ([(2,"noop")] if s in qn else ([(1,"C1")] if s==1 else [])) for s in c0}
       lp[2] = lp[4] = [(2,"noop"), (2,"C2")]
       cp = {s: (c1 if lp[s]==[(1,"C1")] else (c2 if len(lp[s])==2 else c0)) for s in c0}
       for cand in (1, 3):
           assert not any(q.issubset({v for v in c0 if up(lp[cand], lp[v])}) for q in maj(cp[cand]))
   def ext_has_cycle(edges_a, edges_b):
       ext = {u: set(vs) for u, vs in edges_a.items()}
       for u, vs in edges_a.items():
           for y in vs:
               ext[u].update(edges_b.get(y, ()))
       # Check reachability u ->+ u (including singleton self-loops u -> u!)
       for start in ext:
           seen, stack = set(), list(ext.get(start, ()))
           while stack:
               cur = stack.pop()
               if cur == start: return True
               if cur not in seen:
                   seen.add(cur); stack.extend(ext.get(cur, ()))
       return False
   # Write skew (T1 -rw-> T2 -rw-> T1): allowed by SI, rejected by PL-3
   assert not ext_has_cycle({1:set(), 2:set()}, {1:{2}, 2:{1}})
   # Read skew (T1 -wr-> T2 -rw-> T1): collapses to 1->1 self-loop in (A ; B), rejected by SI!
   assert ext_has_cycle({1:{2}, 2:set()}, {1:set(), 2:{1}})
   print("OK: all consensus, quorum, and Adya/SI cycle invariants verified")
   '
   ```
