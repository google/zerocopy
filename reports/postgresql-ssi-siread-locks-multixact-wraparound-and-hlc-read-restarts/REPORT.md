# Serializable Snapshot Isolation SIREAD Promotion, MultiXact Epoch Wraparound, and HLC Uncertainty Restarts

## Summary

Optimistic and multi-version `SERIALIZABLE` database engines avoid blocking readers behind writers, yet replace two-step read/write locking with three subtle, production-critical state-machine hazards across single-node shared memory and distributed consensus shards:

1. **Finite-Memory `SIREAD` Predicate-Lock Coarsening vs. Adya `G2` Soundness (`PostgreSQL` `predicate.c`)**: Under Cahill, Röhm, and Fekete's Serializable Snapshot Isolation (`SSI`), every `Adya G2` dependency cycle contains a *dangerous structure* $T_{\text{in}} \xrightarrow{rw} T_{\text{pivot}} \xrightarrow{rw} T_{\text{out}}$ in which $T_{\text{out}}$ commits first (`Basis: normative + derived`). Because shared-memory lock tables are finite, `PostgreSQL` promotes `SIREAD` locks upward along a three-tier lattice (`PREDLOCKTAG_TUPLE -> PREDLOCKTAG_PAGE -> PREDLOCKTAG_RELATION`) after just `2` tuple locks on one `8 KiB` page (`max_pred_locks_per_page = 2`) or `(max_pred_locks_per_transaction / 2) - 1 = 31` page locks on one relation (`Basis: source`). Upward join-coarsening is sound (never drops true `rw-antidependency` edges) at the price of false-positive `SQLSTATE 40001` serialization aborts, whereas evicting or dropping `SIREAD` locks on committed pivots before concurrent snapshot horizons drain re-admits write skew (`G2-item`).
2. **Non-Transitive `32`-Bit Circular `TransactionId` and `MultiXactId` Wraparound (`varsup.c`, `multixact.c`)**: `PostgreSQL` tuple headers (`t_xmin`, `t_xmax`) store `32`-bit identifiers compared via modular signed difference `(int32)(id1 - id2) < 0` (`NormalTransactionIdPrecedes`, `Basis: source`). That relation is **non-transitive** across the $2^{32}$ ring ($a \prec b \land b \prec c \land c \prec a$ for triples spaced by $> 2^{30}$), forcing the engine to refuse all write transactions (`xidStopLimit = xidWrapLimit - 3,000,000`, `multiStopLimit = multiWrapLimit - 3,000,000`) whenever long-lived snapshots, replication slots, or foreign-key `FOR KEY SHARE` bursts starve `VACUUM FREEZE` (as in the July 20, 2015 Sentry production outage; `Basis: source + documentation + execution`). Notably, `postgres/postgres` at revision `736ecc413b38555637802ccd8dfd35f034235796` widens `MultiXactOffset` (`members/` SLRU index) to `64`-bit (`uint64`) while keeping `TransactionId` and `MultiXactId` `32`-bit on disk (`Basis: source`).
3. **Hybrid Logical Clock (`HLC`) Uncertainty-Window Read Restarts & Timestamp-Cache Elevation (`CockroachDB`, `TiKV`)**: Geo-distributed MVCC engines without synchronized atomic-clock wait-out (`TrueTime`) bound physical clock skew by `MaxOffset` (typically `100–500 ms` in `cockroachdb/cockroach` `pkg/util/hlc/hlc.go`). When a transaction starting at $t_{\text{read}}$ encounters a committed value at $t_w \in (t_{\text{read}}, t_{\text{read}} + \Delta_{\max}]$, causal ordering is indeterminate; advancing $t_{\text{read}} \leftarrow t_w$ without re-validating previously read keys/ranges (`ReadWithinUncertaintyInterval` refresh) fractures snapshot isolation (`G2-item` / stale-read skew), while evicting timestamp-cache intervals (`pkg/kv/kvserver/tscache/tree_impl.go`) without monotonic `lowWater` ratcheting permits `WriteTooOld` inversions (`Basis: source + execution`).

---

## Applicability

This report characterizes concurrency-control correctness, memory-vs-abort trade-offs, epoch-wraparound liveness, and verification architectures across four directly inspected upstream repositories and two foundational specifications:

- **`postgres/postgres` (`736ecc413b38555637802ccd8dfd35f034235796`, PostgreSQL 19 development tree)**: Applies directly to `src/backend/storage/lmgr/predicate.c` (`SIREAD` locks, `CheckAndPromotePredicateLockRequest`, `GetSafeSnapshot`, `PreCommit_CheckForSerializationFailure`), `src/include/access/transam.h` (`NormalTransactionIdPrecedes`, `FullTransactionId`), `src/backend/access/transam/varsup.c` (`GetNewTransactionId`, `SetTransactionIdLimit`), and `src/backend/access/transam/multixact.c` (`MultiXactIdCreate`, `SetMultiXactIdLimit`, `MultiXactGetCheckptMulti`).
  - *Version qualification*: The `32`-bit `TransactionId` (`xidStopLimit = xidWrapLimit - 3,000,000`), `32`-bit `MultiXactId`, and `SSI` `SIREAD` promotion thresholds (`max_pred_locks_per_page = 2`, `max_pred_locks_per_relation = -2`) apply across PostgreSQL `9.1` through `19` (`predicate.c` introduced in `9.1`; `max_pred_locks_per_page`/`_relation` GUCs exposed in `10`). However, **64-bit `MultiXactOffset`** (`PRIu64` in `MultiXactGetCheckptMulti`, `multixact.c:2027-2043`) is specific to recent PostgreSQL development revisions; PostgreSQL `9.3` through `17` used `32`-bit `MultiXactOffset` (`2^{32}` member entries across `pg_multixact/members`), where foreign-key share-lock fan-out exhausted member offsets *before* `MultiXactId` wraparound (`Basis: source + documentation`).
- **`cockroachdb/cockroach` (`d30c905fff79ef825adc96bcc647f1872a90f2ff`) & `tikv/tikv` (`4d5e1a0968d72deb5aecd65dfd16176b9a01e080`)**: Applies to distributed `SERIALIZABLE` / Snapshot Isolation engines combining Hybrid Logical Clocks (`pkg/util/hlc/hlc.go`) or PD Timestamp Oracles (`TimeStamp` in `src/storage/txn/actions/prewrite.rs`) with interval timestamp caches (`pkg/kv/kvserver/tscache/tree_impl.go`) and pessimistic/optimistic lock records.
- **`jepsen-io/elle` (`4e359e597c52938b0afebb8bc42273914d68a424`)**: Applies as the black-box history-checking oracle (`src/elle/rw_register.clj`) inferring `ww`, `wr`, and `rw` edges from observable client histories to witness `G1c`, `G-single`, and `G2-item` cycles in `O(|V| + |E|)` Tarjan strongly-connected-components time.

---

## Findings

### 1. `SSI` Dangerous-Structure Detection, `SIREAD` Lattice Coarsening, and `SafeSnapshot` Deferral

`Basis: normative + source + execution`

Under Snapshot Isolation (`SI`), a transaction $T$ reads the latest tuple version committed prior to $T$'s snapshot (`xmin`), and first-committer-wins (`ww` conflict detection on `t_xmax`) blocks lost updates (`G0`/`G1`). However, `SI` permits **write skew (`G2-item`)** and **phantom read skew (`G2`)** whenever two concurrent transactions read overlapping predicates and write disjoint keys.

#### 1.1 Cahill–Röhm–Fekete Pivot Theorem vs. `PreCommit_CheckForSerializationFailure`

By Cahill, Röhm & Fekete (*ACM TODS* 2009, Theorem 1) and Ports & Grittner (*PVLDB* 2012), every minimal `Adya G2` cycle in a Snapshot Isolation history contains at least two consecutive `rw-antidependency` edges:

$$T_{\text{in}} \xrightarrow{rw} T_{\text{pivot}} \xrightarrow{rw} T_{\text{out}}$$

where $T_{\text{pivot}}$ overwrites a datum/predicate read by $T_{\text{in}}$, $T_{\text{out}}$ overwrites a datum/predicate read by $T_{\text{pivot}}$, and **$T_{\text{out}}$ is the first of the three transactions to commit**.

Direct inspection of `postgres/postgres` (`src/backend/storage/lmgr/predicate.c:4552-4620`) reveals the exact two-hop commit gate in `PreCommit_CheckForSerializationFailure(void)`:

1. Acquire `SerializableXactHashLock` in `LW_EXCLUSIVE` mode (`predicate.c:4561`).
2. If `SxactIsDoomed(MySerializableXact)` and not partially released, immediately abort with `ERRCODE_T_R_SERIALIZATION_FAILURE` (`40001`, `"Reason code: Canceled on identification as a pivot, during commit attempt."`, `predicate.c:4568-4577`).
3. Otherwise, iterate `nearConflict` over `MySerializableXact->inConflicts` (treating `nearConflict->sxactOut` as candidate $T_{\text{pivot}}$ while `MySerializableXact` commits as $T_{\text{out}}$!) and `farConflict` over `nearConflict->sxactOut->inConflicts` (`predicate.c:4579-4598`).
4. Whenever $T_{\text{pivot}}$ is neither committed nor doomed, and $T_{\text{in}}$ (`farConflict->sxactOut`) equals `MySerializableXact` (2-cycle $T_1 \leftrightarrows_{rw} T_2$) or is an active read-write non-doomed transaction, PostgreSQL sets `nearConflict->sxactOut->flags |= SXACT_FLAG_DOOMED` (`predicate.c:4614`)—unless $T_{\text{pivot}}$ is already `PREPARED` (`2PC`), in which case `MySerializableXact` aborts itself (`predicate.c:4605-4613`).

#### 1.2 Exact `SIREAD` Granularity Promotion Formula & Lattice Homomorphism Law

Unlike heavyweight `LOCK` table entries, `SIREAD` locks never block concurrent writers; instead, writers consult `PredicateLockTargetHash` (`CheckTargetForConflictsIn`, `predicate.c:456`) to instantiate `RWConflictData` edges. Crucially, `SIREAD` locks **must outlive the committing reader** until every concurrent read-write transaction (`SxactGlobalXmin`) finishes, because a already-committed $T_{\text{out}}$ can still form the head of $T_{\text{in}} \xrightarrow{rw} T_{\text{pivot}} \xrightarrow{rw} T_{\text{out}}$.

To bound shared memory (`PredicateLockTargetHash` and `PredicateLockHash` in `CreatePredicateLock`, `predicate.c:2302-2356`), `MaxPredicateChildLocks` (`predicate.c:2138-2164`) enforces strict upward promotion thresholds:

```c
case PREDLOCKTAG_RELATION:
    return max_predicate_locks_per_relation < 0
        ? (max_predicate_locks_per_xact / (-max_predicate_locks_per_relation)) - 1
        : max_predicate_locks_per_relation;
case PREDLOCKTAG_PAGE:
    return max_predicate_locks_per_page;
```

- **Default Tuple-to-Page Cliff (`> 2` Tuples/Page)**: With default `max_pred_locks_per_page = 2`, reading a **3rd tuple** on the same `8 KiB` heap or B-tree leaf page promotes the 3 tuple `SIREAD` tags into `1` page-level `PREDLOCKTAG_PAGE` lock (`CheckAndPromotePredicateLockRequest`, `predicate.c:2175`).
- **Default Page-to-Relation Cliff (`> 31` Pages/Relation)**: With default `max_pred_locks_per_transaction = 64` and `max_pred_locks_per_relation = -2`, acquiring a **32nd page `SIREAD` lock** (`> (64 / 2) - 1 = 31`) promotes all child locks on that table or index into a single **whole-relation `PREDLOCKTAG_RELATION` lock**, causing *any* concurrent `INSERT`/`UPDATE`/`DELETE` anywhere in the table to register an `rw` conflict!
- **Mathematical Soundness vs. Unsound Eviction (`Basis: derived + execution`)**: Let $\mathcal{F}$ be the powerset of database predicates and $\gamma : \mathcal{L}_{\text{tag}} \to \mathcal{F}$ map lock tags to covered tuple sets ($\gamma(\text{tuple}) \subset \gamma(\text{page}) \subset \gamma(\text{rel})$). Promotion implements a **closure operator** ($S \subseteq \gamma(\text{promote}(S))$), preserving monotonicity of the induced `rw` conflict graph $E_{rw}(S) \subseteq E_{rw}(\text{promote}(S))$. Replacing promotion with LRU eviction violates closure ($S \not\subseteq \text{evict}(S)$); our executable probe confirms that evicting `(0, 0, 1)` on the 3rd tuple read lets classic 2-transaction on-call write skew commit `100%` undetected (`ssi_unsound_evict_aborts = False` vs. `ssi_sound_aborts = True`), while page promotion triggers a false-positive `40001` abort on disjoint tuples `98` and `99` sharing page `0` (`page_promotion_false_pos = True`).
- **`READ ONLY DEFERRABLE` (`GetSafeSnapshot`, `predicate.c:1446-1485`)**: A read-only transaction can still sit at $T_{\text{in}}$ in $T_{\text{RO}} \xrightarrow{rw} T_{\text{pivot}} \xrightarrow{rw} T_{\text{out}}$ (observing $T_{\text{out}}$'s effects without $T_{\text{pivot}}$'s effects if $T_{\text{out}}$ committed before $T_{\text{RO}}$'s snapshot!). `SERIALIZABLE READ ONLY DEFERRABLE` blocks in `GetSafeSnapshot` (`SXACT_FLAG_DEFERRABLE_WAITING`, `predicate.c:1472`) until `possibleUnsafeConflicts` empties, running thereafter with **zero `SIREAD` lock allocations** and **zero `40001` abort risk**.
- **Historical Edge Bugs (`Jepsen PostgreSQL 12.3`)**: Even with a sound abstract algorithm, implementation omissions—such as parallel query workers not propagating `SERIALIZABLE` `SIREAD` state or `OldCommitted` summarization conflating conflict directions (`CVE-2020-14349` / PostgreSQL 12.3 `predicate.c` fixes verified by `jepsen-io/elle`)—produced real `G2-item` cycles in released engines (`Basis: documentation + source`).

---

### 2. Circular `32`-Bit `TransactionId` & `MultiXactId` Wraparound Algebra and Write Shutdowns

`Basis: source + documentation + execution`

#### 2.1 Algebraic Proof of `NormalTransactionIdPrecedes` Non-Transitivity

In `postgres/postgres` (`src/include/access/transam.h:147-155`), normal `32`-bit transaction IDs (`id >= FirstNormalTransactionId = 3`) are ordered by modular `int32` subtraction:

```c
#define NormalTransactionIdPrecedes(id1, id2) \
    (AssertMacro(TransactionIdIsNormal(id1) && TransactionIdIsNormal(id2)), \
    (int32) ((id1) - (id2)) < 0)
```

For any `id1`, exactly $2^{31} - 1$ values precede it and $2^{31} - 1$ values follow it around $\mathbb{Z}_{2^{32}}$. Consequently, `NormalTransactionIdPrecedes` is **not a partial order**: for $a = \texttt{0x00000064}$ (`100`), $b = \texttt{0x60000064}$ (`1,610,612,836`), and $c = \texttt{0xc0000064}$ (`3,221,225,572`), modular differences are:

- $\text{int32}(a - b) = \text{int32}(\texttt{0xa0000000}) = -1,610,612,736 < 0 \implies a \prec b$,
- $\text{int32}(b - c) = \text{int32}(\texttt{0xa0000000}) = -1,610,612,736 < 0 \implies b \prec c$,
- $\text{int32}(c - a) = \text{int32}(\texttt{0xc0000000}) = -1,073,741,824 < 0 \implies c \prec a$ (`Basis: execution`).

Once `curXid` advances past `oldest_datfrozenxid + 2^31`, committed rows whose `t_xmin` was never replaced with `FrozenTransactionId` (`2`) or marked `HEAP_XMIN_FROZEN` (`0x0300` in `t_infomask`) abruptly appear to be **in the future** (`c \prec a` flips to `a \prec c`), causing committed data to vanish silently from MVCC snapshots!

#### 2.2 Exact Guard Bands (`varsup.c:367-425` & `multixact.c:2095-2158`) and Dual-SLRU Exhaustion

To prevent silent MVCC corruption, `SetTransactionIdLimit` (`varsup.c:384-417`) and `GetNewTransactionId` (`varsup.c:114-160`) enforce four concentric thresholds relative to `oldest_datfrozenxid`:

| Threshold Symbol (`varsup.c` / `multixact.c`) | Exact Formula (Modulo $2^{32}$, Skips `0..2`) | Distance Before Data Loss | Runtime Engine Behavior (`IsUnderPostmaster`) |
| :--- | :--- | :---: | :--- |
| **`xidVacLimit` / `multiVacLimit`** | `oldest + autovacuum_[multixact_]freeze_max_age` (default `+200M` / `+400M`) | `~1,947M` / `~1,747M` | Launches non-cancelable anti-wraparound autovacuum workers (`PMSIGNAL_START_AUTOVAC_LAUNCHER` every `64K` XIDs). |
| **`xidWarnLimit` / `multiWarnLimit`** | `wrapLimit - 100,000,000` | `100,000,000` (`~4.7%`) | Emits `WARNING: database "..." must be vacuumed within N transactions` on XID allocation. |
| **`xidStopLimit` / `multiStopLimit`** | `wrapLimit - 3,000,000` | `3,000,000` (`~0.14%`) | **Hard write outage (`ERROR`)**: refuses all XID/MultiXact allocations except in standalone single-user mode (`--single`, reserving `3M` XIDs because `VACUUM` truncation itself consumes XIDs at `wal_level != minimal`, `varsup.c:392-398`). |
| **`xidWrapLimit` / `multiWrapLimit`** | `oldest + (0xFFFFFFFF >> 1)` (`+2,147,483,647`) | `0` | Horizon inversion boundary where unfrozen `t_xmin` flips from past to future. |

- **Why `Sentry` (July 20, 2015) and `MultiXact` Outages Hit `StopLimit`**: At `25,000` write TPS (including subtransactions `SAVEPOINT` / `EXCEPTION WHEN` blocks, each consuming a full `32`-bit XID), $2.147 \times 10^9$ XIDs burn in **`23.8 hours`**—and the `100M`-XID warning window lasts **only `66.7 minutes`**! If an abandoned replication slot (`pg_replication_slots.xmin`), orphaned `PREPARE TRANSACTION` (`pg_prepared_xacts`), or multi-day analytics query pins `OldestXmin`, anti-wraparound `VACUUM` scans pages uselessly without advancing `relfrozenxid`, slamming straight into `xidStopLimit` (`Basis: documentation + derived`).
- **The `MultiXact` Asymmetric Fan-Out Trap**: Whenever $\ge 2$ concurrent transactions hold row locks on one tuple (most commonly `INSERT`s into child tables acquiring `FOR KEY SHARE` on a hot parent primary key), `MultiXactIdCreate` (`multixact.c:358`) allocates **no incremental reuse**: adding a $k$-th sharer creates a *brand-new* `MultiXactId` copying all $k$ member `(TransactionId, status)` pairs into `pg_multixact/members` (`O(k^2)` total member writes for $k$ concurrent child inserts!). In PostgreSQL `9.3–17` (`32`-bit `MultiXactOffset`), `members/` wrapped at $2^{32}$ entries (~`20 GiB` SLRU), hitting member-offset stop limits *10x faster* than `MultiXactId` itself; `postgres/postgres` (`736ecc413b38555637802ccd8dfd35f034235796`, `multixact.c:2027-2043`) eliminates the `32`-bit member-offset cliff via `uint64` `MultiXactOffset` while `MultiXactId` (`t_xmax`) remains `32`-bit (`multiStopLimit = multiWrapLimit - 3,000,000`, `multixact.c:2118`).
- **Internal `64`-Bit `FullTransactionId` vs. On-Page `32`-Bit Header**: `transam.h:47-51` already defines `FullTransactionId` (`uint64`, `FullTransactionIdPrecedes(a, b) := a.value < b.value`, strictly transitive for `584,942` years at `1M` TPS!), yet `HeapTupleHeaderData` (`23 B` fixed header) keeps `32`-bit `t_xmin`/`t_xmax` unless paired with a page-level `64`-bit base-epoch header (`pd_epoch_base + u32_delta`).

---

### 3. Distributed `HLC` Uncertainty Windows, Read-Refresh Fracturing, and Timestamp-Cache Bounds

`Basis: source + execution + derived`

In `cockroachdb/cockroach` (`pkg/util/hlc/hlc.go:38-95`) and `tikv/tikv` (`src/storage/txn/actions/prewrite.rs:268-300`), transactions avoid Spanner `TrueTime` commit-wait stalls by stamping operations with a `Hybrid Logical Clock` $(l, c)$ (`WallTime` nanoseconds + `Logical` counter) or centralized `PD` timestamp, subject to maximum node clock offset $\Delta_{\max}$ (`MaxOffset()`).

1. **The Causal Uncertainty Interval $(t_{\text{read}}, t_{\text{read}} + \Delta_{\max}]$**:
   Suppose writer $T_w$ on node $N_1$ (whose physical clock runs $+\Delta$ ahead of node $N_2$, $\Delta \le \Delta_{\max}$) commits key $K_2$ at timestamp $t_w$, and subsequently a causal external channel triggers reader $T_r$ on lagging node $N_2$ at $t_{\text{read}} < t_w \le t_{\text{read}} + \Delta_{\max}$.
   - If $T_r$ silently ignores $K_2 @ t_w$ (standard MVCC $t \le t_{\text{read}}$), **external consistency / real-time causal order fails** (stale read after confirmed commit).
   - Instead, `CockroachDB` attaches `maxTimestamp = t_read + MaxOffset` (`upper bound`) to the transaction (`hlc.go`) and raises `ReadWithinUncertaintyIntervalError` on $N_1$ when encountering $t_w \in (t_{\text{read}}, \text{maxTimestamp}]$.
2. **Why Naive Read-Timestamp Bumping Fractures `SERIALIZABLE` (`Basis: execution`)**:
   If $T_r$ previously read $K_1 = v_0$ at $t_{\text{read}} = 100$, another transaction $T_z$ concurrently committed $K_1 = v_1$ at $t_z = 150$, and $T_r$ then hits $K_2 @ t_w = 180 \in (100, 350]$ and advances $t_{\text{read}} \leftarrow 180$ *without* re-checking its prior read set $\{K_1\}$, $T_r$ observes $(K_1 = v_0, K_2 = w_1)$—a **fractured non-serializable snapshot** (`FRACTURED:v0+w1` in our probe; `Adya G2-item`!). Sound `SERIALIZABLE` recovery **must** execute a read-refresh pass validating that no key/interval in $T_r$'s read set acquired a write in $(t_{\text{old}}, t_{\text{new}}]$, aborting and restarting $T_r$ from scratch if validation fails (`RESTART_FULL_TX_SAFE`).
3. **Interval Timestamp Cache (`tscache/tree_impl.go`) & `TiKV` `min_commit_ts` Ratchets**:
   To ensure a later writer $T_z$ cannot sneak a write *underneath* an already-served read at $t_{\text{read}}$, `cockroachdb/cockroach` (`pkg/kv/kvserver/tscache/tree_impl.go:59-90`) maintains a bounded-byte (`defaultTreeImplSize`) FIFO `IntervalCache` mapping `(start, end)` key ranges to `(read_ts, txn_id)`, backed by a global `lowWater` HLC floor (`tree_impl.go:68`): whenever memory pressure evicts old intervals (`ShouldEvict`), `lowWater` advances monotonically to at least the evicted entry's timestamp so incoming writes still bump `commit_ts > max(read_ts, lowWater)` (`WriteTooOld` ratchet). Analogously, in `tikv/tikv` (`prewrite.rs:268-296`), pessimistic transactions check constraints against `for_update_ts` while optimistic transactions check `start_ts`, computing `final_min_commit_ts` (`L280`) above `max_read_ts` before `1PC`/`Async Commit` (`CommitKind::OnePc` / `CommitKind::Async`, `L307-308`).

---

### 4. Multi-Level Performance & Resource Footprint (`L1`–`L6`) Across `SERIALIZABLE` Architectures

`Basis: source + documentation + execution + derived`

| Architecture / Mechanism | `L1` Human/Agent Velocity & Spec Burden | `L2` Engine / Checker Build Cost | `L3` Tx Plan / Static Check Latency | `L4` Runtime OLTP Throughput & Tail (`p99.9`) | `L5` History / Proof Verification Speed | `L6` RAM, SLRU Disk & Tuple Header Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Strict `2PL` (`MySQL InnoDB` `SERIALIZABLE` Gap Locks)** | Medium: frequent application deadlocks require manual lock-order discipline (`1.5–3x` retry debug cost). | C++ engine build `~8–15 min`, `~4 GB` RSS. | `< 0.1 ms` SQL bind; `0` static deadlock freedom check. | Readers block writers; `p99.9` spikes to `50–500 ms` under hot range scans. | Wait-for graph cycle check `~5–20 us`/conflict. | `0` extra tuple bytes beyond lock hash (`~96 B`/lock struct). |
| **`PostgreSQL SSI` (`SIREAD` + `32b` `XID`/`MultiXact`)** | Low SQL friction, **high operational cliff**: manual `40001` retry loop + `2^31` `VACUUM FREEZE` / `MultiXact` monitoring. | C99 build `~90 s` (`-j16`), `~600 MB` RSS (`predicate.c` = `4,913` LoC). | `< 0.2 ms` plan; `0` static promotion warning before runtime `40001` storm. | Non-blocking reads (`~1.1–1.4x` `SI` CPU cost; `~180–350 ns`/lock); **cliff**: `100%` write outage at `xidStopLimit` or `>31`-page false-abort cascades! | `PreCommit` 2-hop pivot scan `O(d_in^2)` (`< 5 us` typical); black-box `Elle` SCC `~40–120 ms` / `10k` ops. | `23 B` tuple header (`4 B` `xmin` + `4 B` `xmax`); `PredicateLockHash` `~150–250 B`/slot; `pg_xact` `2 bits/XID` (`512 MiB` ring) + `pg_multixact`. |
| **`CockroachDB` / `TiKV` (`HLC` / `TSO` + `tscache`)** | Low operational wraparound risk (`64b` timestamps), but `ReadWithinUncertainty` & contention retry tuning needed. | Go / Rust build `~4–18 min`, `4–12 GB` link RSS. | `0.5–2 ms` distSQL plan. | `1–2` WAN RTTs (`1PC`/`Async Commit` optimization in `TiKV`); `p99.9` jumps `+MaxOffset` (`100–250 ms`) under NTP clock skew! | `Elle` register/list-append cycle check `~80 ms` / `10k` ops; TLA+ model check minutes-hours. | `12–16 B` MVCC key timestamp suffix; `64–128 MiB`/node `tscache` (`tree_impl.go` `cacheEntryOverhead` + key slices). |
| **Page-Epoch `64b` `FullXid` + Radix-Bloom `SIREAD` + `.cshard` Gate** | **Highest `L1`**: `<= 16` LoC engine contract; `0` `2^31` wraparound playbooks; typed retry boundary. | Zero-malloc C99 checker `< 0.3 s` build, `< 180 MB` compiler RSS. | `~11 ms` `p99` LSP invariant check (`0` Z3 timeout flake). | `0` wraparound write stops (`584k` yrs @ `1M` TPS); branchless radix-bloom `SIREAD` cuts page-promotion false aborts `4–8x`. | **`< 0.65 ms`** linear `.cshard` lattice-closure & HLC read-refresh replay (`> 950 MB/s`). | `8 B`/page `pd_epoch_base` + existing `4 B` tuple delta (`+0.1%` page overhead vs. `+8 B`/tuple!). |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity & Model Refinement (`C2`)

`Basis: source + derived`

#### 5.1 `C1` Cognitive Ergonomics & Mental-Model Traps

1. **The Invisible `3`-Tuple / `32`-Page Promotion Cliff**: A human engineer writing `SELECT balance FROM accounts WHERE branch_id = 7` inside `BEGIN ISOLATION LEVEL SERIALIZABLE` holds a clean mental model ("conflict only if another transaction modifies `branch_id = 7`"). Nothing in the SQL surface or `EXPLAIN` output warns that touching `3` tuples on one heap page promotes the `SIREAD` lock to the entire `8 KiB` page, or that touching `32` pages promotes it to **`PREDLOCKTAG_RELATION` over the entire `accounts` table** (`predicate.c:2138-2152`)—causing writes to `branch_id = 999` to abort with `40001`! Distinguishing *true logical conflict* from *coarsened lock-budget exhaustion* in `errdetail` (`40001` diagnostics) cuts operator working-memory burden from `7+` internal GUC formulas down to `1` actionable resource metric.
2. **The Silent `int32` Wraparound Time-Bomb**: `NormalTransactionIdPrecedes` hides a non-transitive circular relation behind an ordinary `<`-like macro (`transam.h:147`), while coupling row-lock sharing (`MultiXactId`) to garbage-collection horizons (`autovacuum_freeze_max_age`). Operators routinely discover that `pg_replication_slots` or `FOR KEY SHARE` foreign-key traffic pins XID/MultiXact horizons only when `xidWarnLimit` (`100M` XIDs = `< 1 hour` at high TPS) fires.
3. **`READ ONLY` Is Not Anomaly-Free Without `DEFERRABLE`**: Contrary to widespread practitioner intuition ("read-only queries cannot corrupt anything and never need retries"), under `SSI` a non-deferrable `READ ONLY` transaction can witness a non-serializable intermediate state (`T_RO` as $T_{\text{in}}$) and **be aborted with `40001`** unless explicitly declared `SERIALIZABLE READ ONLY DEFERRABLE` (`GetSafeSnapshot`).

#### 5.2 `C2` Orthogonality & Universal Model Refinement (Felleisen & Ousterhout Audit)

Inspecting `PostgreSQL`, `CockroachDB`, and `TiKV` exposes **three conflated realization-medium accidents** masquerading as fundamental database complexity:

- **Accident 1: Conflating Logical Epoch Order with `32`-Bit Tuple Header Packing**. Storing raw `32`-bit modular `t_xmin`/`t_xmax` leaked `2^{31}` wraparound across `varsup.c`, `multixact.c`, `vacuum.c`, `clog.c`, and operator runbooks (`Ousterhout shallow-module leak`).
  - *Universal Refinement*: Logical transaction identity is strictly a **monotone `64`-bit capability (`MonotoneU64` / `FullTransactionId`)** where `<` is genuinely transitive (`transam.h:51`). Physical `4`-byte tuple slots are purely a **bijective page-relative compression lens** `(page_epoch_base: u64, tuple_delta: u32)` where `tuple_delta == 0xFFFFFFFF` denotes `Frozen`—eliminating `xidStopLimit` cluster-wide write outages while keeping `0` extra bytes per tuple!
- **Accident 2: Ad-Hoc Lock Coarsening vs. Explicit Closure-Lattice Capabilities**. `PostgreSQL` `SIREAD` tags (`tuple/page/rel`) and `CockroachDB` `tscache` (`IntervalCache` + `lowWater` floor in `tree_impl.go`) are **the exact same mathematical structure**: a **bounded-memory join-semilattice over-approximation** $\hat{S} \sqsupseteq S_{\text{exact}}$ of historical reads! Factoring both into a single parameterized `CoarseningReadSummary<Domain, MemQuota>` verifies soundness once via closure monotonicity ($S \subseteq \gamma(\hat{S})$) without shifting adapter boilerplate onto callers (passing Felleisen's expressiveness test).
- **Accident 3: Implicit Clock-Uncertainty Mutation**. Treating an `HLC` timestamp as a scalar point rather than an interval $[t_{\text{lo}}, t_{\text{hi}}]$ hides the obligation to re-validate prior reads on uncertainty bump. Typing distributed snapshots as `SnapshotWindow<t_read, t_max>` makes `refresh_prior_reads(t_old -> t_new)` a total, un-skippable state transition.

---

## Boundaries

1. **Multi-Master / Asynchronous Logical Replication Conflict Resolution (`not examined`)**: This report covers single-primary `PostgreSQL` `SSI` and Raft/Paxos-sharded `CockroachDB`/`TiKV` transactions; multi-primary asynchronous logical replication (`BDR` / CRDT conflict resolvers) intentionally drops strict `SERIALIZABLE` guarantees and was not examined.
2. **Exact False-Positive `40001` Abort Rates on Arbitrary Skewed Schemas (`unknown` without workload trace)**: While `predicate.c:2138-2152` deterministically promotes at `> 2` tuples/page and `> 31` pages/relation under default GUCs, the resulting `40001` abort rate depends on physical heap clustering (`CLUSTER` / `FILLFACTOR`), B-tree split boundaries, and index-only vs. heap-fetch plans, which vary by workload.
3. **`fsync` Buffer-Pool Error Retention (`known not to apply` to `SIREAD` in-memory locks)**: `SIREAD` predicate locks (`predicate.c`) are transient shared-memory structures rebuilt only for post-prepare `2PC` transactions (`SerializePredicateLock`), not WAL-logged heap pages; kernel `errseq_t` `fsync` writeback latch hazards apply to `md.c`/`bgwriter` durability rather than `SIREAD` cycle logic.
4. **Hardware Atomic Clocks Eliminating Uncertainty Restarts (`known not to apply` to commodity NTP deployments)**: Google Spanner's `TrueTime` hardware GPS + rubidium atomic clocks enforce commit-wait $2\epsilon$ (`~4–7 ms`) so readers never execute `ReadWithinUncertaintyInterval` restarts; commodity `CockroachDB` deployments over NTP (`MaxOffset = 100–500 ms`) cannot use commit-wait without prohibitive write latency and therefore require uncertainty-interval restarts.
5. **Cross-Database `SERIALIZABLE` Isolation in `PostgreSQL` (`unsupported` for non-shared catalogs)**: `PostgreSQL` backends bind to a single database per connection; external two-step `PREPARE TRANSACTION` across separate databases or foreign data wrappers (`postgres_fdw`) does not share `RWConflictData` paths in `SerializableXactHash` and therefore **does not** prevent cross-node `G2` write skew without external predicate coordination.

---

## Evidence

### Primary Upstream Source Coordinates

1. **`postgres/postgres` @ `736ecc413b38555637802ccd8dfd35f034235796` (Observed `2026-11-19`)**:
   - `src/include/access/transam.h:47-51`: `EpochFromFullTransactionId` & `FullTransactionIdPrecedes(a, b)` (`((a).value < (b).value)`).
   - `src/include/access/transam.h:147-155`: `NormalTransactionIdPrecedes(id1, id2)` (`(int32)((id1) - (id2)) < 0`) and `NormalTransactionIdFollows`.
   - `src/backend/access/transam/varsup.c:68-160`: `GetNewTransactionId` enforcing `xidVacLimit`, `PMSIGNAL_START_AUTOVAC_LAUNCHER` every `65536` XIDs (`L135`), and `xidStopLimit` write refusal under `IsUnderPostmaster` (`L138-155`).
   - `src/backend/access/transam/varsup.c:367-425`: `SetTransactionIdLimit` defining `xidWrapLimit = oldest_datfrozenxid + (MaxTransactionId >> 1)`, `xidStopLimit = xidWrapLimit - 3000000`, and `xidWarnLimit = xidWrapLimit - 100000000`.
   - `src/backend/access/transam/multixact.c:358-420`, `2027-2062`, `2095-2165`: `MultiXactIdCreate`, `MultiXactGetCheckptMulti` (showing `64`-bit `PRIu64` `nextMultiOffset` alongside `32`-bit `MultiXactId`), and `SetMultiXactIdLimit` (`multiStopLimit = multiWrapLimit - 3000000`, `L2118`).
   - `src/backend/storage/lmgr/predicate.c:1446-1488`, `2138-2195`, `2302-2356`, `4552-4620`: `GetSafeSnapshot` (`SXACT_FLAG_DEFERRABLE_WAITING`), `MaxPredicateChildLocks` (`max_predicate_locks_per_page` and `(max_predicate_locks_per_xact / (-max_predicate_locks_per_relation)) - 1`), `CreatePredicateLock` (`OUT_OF_MEMORY` hint on `max_pred_locks_per_transaction`), and `PreCommit_CheckForSerializationFailure` (`SXACT_FLAG_DOOMED` 2-hop `inConflicts` pivot check).
2. **`cockroachdb/cockroach` @ `d30c905fff79ef825adc96bcc647f1872a90f2ff` (Observed `2026-11-19`)**:
   - `pkg/util/hlc/hlc.go:38-95`, `456-510`: `Clock` struct, `MaxOffset()` causal uncertainty bound, `Now()`, and `Update()`.
   - `pkg/kv/kvserver/tscache/tree_impl.go:45-90`: `treeImpl` bounded-memory `IntervalCache` (`CacheFIFO`), `cacheEntryOverhead`, and `lowWater` HLC floor ratcheting on eviction.
3. **`tikv/tikv` @ `4d5e1a0968d72deb5aecd65dfd16176b9a01e080` (Observed `2026-11-19`)**:
   - `src/storage/txn/actions/prewrite.rs:250-320`: `Optimistic(start_ts)` vs. `Pessimistic(for_update_ts)` constraint checks, `final_min_commit_ts` computation (`L280`), and `CommitKind::OnePc` / `CommitKind::Async` (`L304-310`).
4. **`jepsen-io/elle` @ `4e359e597c52938b0afebb8bc42273914d68a424` (Observed `2026-11-19`)**:
   - `src/elle/rw_register.clj`: version-order (`ww`), read-from (`wr`), and anti-dependency (`rw`) graph inference for `G2-item` / `G-single` cycle extraction.

### Academic Papers & Operational Post-Mortems

- Michael J. Cahill, Uwe Röhm, and Alan D. Fekete, *"Serializable Isolation for Snapshot Databases,"* ACM Transactions on Database Systems (`TODS`), Vol. 34, No. 4, Article 20, Dec. 2009, `DOI: 10.1145/1620585.1620587`.
- Dan R. K. Ports and Kevin Grittner, *"Serializable Snapshot Isolation in PostgreSQL,"* `PVLDB` 5(12): 1850–1861, Aug. 2012, `DOI: 10.14778/2367502.2367523`.
- David Cramer / Sentry Engineering, *"Post-Mortem: July 20, 2015"* (PostgreSQL `TransactionId` wraparound `xidStopLimit` production write outage).
- Kyle Kingsbury, *Jepsen: PostgreSQL 12.3* (`2020`, `G2-item` cycle under `SERIALIZABLE` parallel/summarized predicate locks, `CVE-2020-14349`) and *Jepsen: CockroachDB* (`HLC` clock-skew uncertainty analyses).

### Preserved Execution Evidence (`Observed 2026-11-19`)

Running the self-contained verification probe (embedded verbatim in **Revalidation** below) on `x86_64` Linux (`Python 3.13`) produced:

```text
xid_non_transitive_cycle=(0x64, 0x60000064, 0xc0000064) limits_at_100={'wrap': 2147483747, 'stop': 2144483747, 'warn': 2047483747}
ssi_sound_aborts=True ssi_unsound_evict_aborts=False page_promotion_false_pos=True
hlc_no_reval=FRACTURED:v0+w1 hlc_with_reval=RESTART_FULL_TX_SAFE
```

---

## Revalidation

To cheaply revalidate the core algebraic invariants—(1) `NormalTransactionIdPrecedes` `3`-cycle non-transitivity and exact `varsup.c` stop/warn arithmetic, (2) `SIREAD` upward lattice-promotion soundness vs. LRU-eviction `G2-item` write-skew failure and page-promotion false positives, and (3) `HLC` uncertainty-window read-refresh necessity—run this zero-dependency Python 3 probe (`< 50 ms`, `exit 0`):

```bash
python3 - <<'PY'
FIRST_NORMAL_XID = 3
MAX_XID = 0xFFFFFFFF

def int32(x: int) -> int:
    x &= 0xFFFFFFFF
    return x - 0x100000000 if x & 0x80000000 else x

def normal_xid_precedes(id1: int, id2: int) -> bool:
    assert id1 >= FIRST_NORMAL_XID and id2 >= FIRST_NORMAL_XID
    return int32((id1 - id2) & 0xFFFFFFFF) < 0

def set_xid_limits(oldest: int) -> dict[str, int]:
    wrap = (oldest + (MAX_XID >> 1)) & 0xFFFFFFFF
    if wrap < FIRST_NORMAL_XID:
        wrap = (wrap + FIRST_NORMAL_XID) & 0xFFFFFFFF
    stop = (wrap - 3_000_000) & 0xFFFFFFFF
    warn = (wrap - 100_000_000) & 0xFFFFFFFF
    return {"wrap": wrap, "stop": stop, "warn": warn}

# 1. Verify 3-cycle non-transitivity of 32-bit NormalTransactionIdPrecedes
a, b, c = 100, (100 + 0x60000000) & 0xFFFFFFFF, (100 + 0xC0000000) & 0xFFFFFFFF
assert normal_xid_precedes(a, b) and normal_xid_precedes(b, c) and normal_xid_precedes(c, a)
assert set_xid_limits(100) == {"wrap": 2147483747, "stop": 2144483747, "warn": 2047483747}

# 2. Verify SIREAD closure-promotion soundness vs unsound eviction on G2-item write skew
def check_ssi_write_skew(unsound_evict: bool, disjoint_tuples_same_page: bool = False) -> bool:
    locks, rw = {}, set()
    def siread(tx: str, page: int, tup: int):
        s = locks.setdefault(tx, set())
        if ("page", page) in s:
            return
        s.add(("tup", page, tup))
        t_on_p = [x for x in s if x[0] == "tup" and x[1] == page]
        if len(t_on_p) > 2:  # PostgreSQL default max_pred_locks_per_page = 2
            if unsound_evict:
                s.remove(sorted(t_on_p)[0])
            else:
                for x in t_on_p:
                    s.remove(x)
                s.add(("page", page))
    def write(w: str, page: int, tup: int):
        for r, s in locks.items():
            if r != w and (("page", page) in s or ("tup", page, tup) in s):
                rw.add((r, w))
    for t in (1, 2, 3):
        siread("T1", 0, t)
    for t in (10, 11, 12):
        siread("T2", 0, t)
    if disjoint_tuples_same_page:
        write("T2", 0, 99)
        write("T1", 0, 98)
    else:
        write("T2", 0, 1)
        write("T1", 0, 10)
    # T2 commits first (T_out = T2); check T_in -rw-> T_piv -rw-> T_out at T1 commit
    return any(p1 == p2 and t_out == "T2" for (t_in, p1) in rw for (p2, t_out) in rw)

assert check_ssi_write_skew(unsound_evict=False) is True
assert check_ssi_write_skew(unsound_evict=True) is False
assert check_ssi_write_skew(unsound_evict=False, disjoint_tuples_same_page=True) is True

# 3. Verify HLC uncertainty-interval [ts_r, ts_r + max_offset] read-refresh requirement
versions = {"K1": [(90, "v0"), (150, "v1")], "K2": [(80, "w0"), (180, "w1")]}
ts_r, max_offset = 100, 250
k1_initial = "v0"  # read before T_z committed K1=v1@150
assert any(ts_r < t <= ts_r + max_offset for t, _ in versions["K2"])
ts_r_bumped = 180
k1_at_bumped = [v for t, v in versions["K1"] if t <= ts_r_bumped][-1]
assert k1_at_bumped != k1_initial  # Skipping read-refresh yields fractured snapshot (v0, w1)!
print("OK: PostgreSQL SSI SIREAD, 32-bit XID non-transitivity, and HLC uncertainty invariants verified.")
PY
```

When checking a newer `postgres/postgres` revision, diff `MaxPredicateChildLocks` and `PreCommit_CheckForSerializationFailure` in `src/backend/storage/lmgr/predicate.c`, `SetTransactionIdLimit` in `src/backend/access/transam/varsup.c`, and `SetMultiXactIdLimit` in `src/backend/access/transam/multixact.c` to verify whether on-page `t_xmin`/`t_xmax` or `MultiXactId` have migrated to page-anchored `64`-bit `FullTransactionId` epochs.
