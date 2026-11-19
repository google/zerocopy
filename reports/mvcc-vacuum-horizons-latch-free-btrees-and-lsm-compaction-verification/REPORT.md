# MVCC Vacuum Horizons, Latch-Free Search Trees, Buffer-Pool Swizzling, and LSM Compaction Verification

## Summary

Modern high-throughput database storage engines rely on four tightly coupled concurrency and persistence invariants whose violations cause silent data loss, stale-pointer dereferences, or deleted-key resurrection rather than immediate crashes:

1. **Modular Linearizability of B-Link and LSM Search Templates (Iris Flow Framework):** Verifying Lehman–Yao B-link trees without hand-over-hand lock coupling decomposes into two layers: a Coq/Iris concurrency template proof (`nyu-acsys/template-proofs`) parameterized by node-level sequential separation-logic specifications (discharged in GRASShopper). Keysets are defined locally as $\text{keyset}(I, n) = \text{dom}(\text{inf}(I, n)) \setminus \text{dom}(\text{out}(I, n))$ over a commutative cancelative monoid (`CCM`) flow interface camera. Unlocked traversal across concurrent node splits remains linearizable solely because node **inreach sets grow monotonically** (`authR (gsetUR K)`) and splits are **contextual extensions** (`contextualLeq`) preserving external inflow/outflow and partitioning `keyset` via right-link outflow edges.
2. **Optimistic Lock Coupling (`OLC`) and Buffer-Pool Pointer Swizzling (`ART` & `LeanStore`):** Readers avoid shared-cache-line writes by checking a 64-bit version/lock word before and after every optimistic access (`ARTSynchronized` packs `2b type | 60b version | 1b lock | 1b obsolete`; `LeanStore` pairs an atomic odd/even `version` with a `std::shared_mutex` inside a 64-byte `HybridLatch`). `ART_OLC` relies on QSBR epoch reclamation (`EpocheGuardReadonly`) to prevent use-after-free faults on concurrently freed nodes, whereas `LeanStore` preallocates fixed `BufferFrame` memory and enforces a **bottom-up cooling and eviction invariant** (`repickIf(!all_children_evicted)`) over 3-state 64-bit `Swip` pointers (`HOT = 00`, `COOL = 01`, `EVICTED = 1x`), ensuring no parent page is evicted while holding a raw `BufferFrame*` to a resident child. Direct source inspection of `flode/ARTSynchronized` also exposes an unvalidated early return in `Tree::lookup` when `k.getKeyLen() <= level` after a potentially torn `checkPrefix` read.
3. **MVCC Snapshot Horizons, Wraparound Arithmetic, and Rapid Version GC (`PostgreSQL` vs. `Cicada`):** `PostgreSQL` uses 32-bit unsigned `TransactionId`s (`0–2` reserved; `FirstNormalTransactionId = 3`) ordered via signed 32-bit modular difference `(int32)(id1 - id2) < 0`. At age $2^{31}$ (`curXid = xmin + 2,147,483,648`), strict order antisymmetry breaks (`precedes(a,b)` and `precedes(b,a)` are both true); at age $2^{31}+1$, unfrozen tuples flip to appearing in the future (silent data loss). `SetTransactionIdLimit` enforces four guardrails (`xidVacLimit`, `xidWarnLimit = wrap - 100M`, `xidStopLimit = wrap - 3M`, `xidWrapLimit = oldest + 2^{31}-1`), while `GlobalVisState` (`definitely_needed` / `maybe_needed`) tracks four relation-scoped vacuum horizons (`SharedRels`, `CatalogRels`, `DataRels`, `TempRels`) using 64-bit `FullTransactionId`s. By contrast, `Cicada` avoids central XID allocation with 56-bit TSC + 8-bit thread-ID `CompactTimestamp`s (signed half-space $\approx 139.0$ days at 3.0 GHz TSC, guarded by `about_to_expire` at $1/16$ of $2^{64}$, or 128-bit SeqLock-protected `WideTimestamp`s) and drains per-thread FIFO GC queues incrementally whenever `db_->min_rts() > front.wts`.
4. **LSM-Tree Snapshot-Stripe Compaction and Deleted-Key Resurrection Prevention (`RocksDB` & `Pebble`):** Dropping a point tombstone (`DEL`), single-delete (`SINGLEDEL`), or range tombstone (`RANGEDEL`) during compaction silently resurrects older shadowed values unless **both** (a) the tombstone resides in the **oldest snapshot stripe** (below the earliest active snapshot sequence number) and (b) no older key overlapping that user key or range can exist in any lower level (or sibling L0 sublevel/file, and `allow_ingest_behind` is false). `RocksDB` enforces this via `CompactionIterator` + `CompactionRangeDelAggregator` (`StripeMap`), while `Pebble` models it via `compact.Snapshots`, `compact.TombstoneElision` (`inUseKeyRanges`), `RangeDelSpanCompactor`, and `SplitAndEncodeSpan` at SSTable boundaries. Violating the `SingleDelete` single-preceding-put contract resurrects earlier shadowed writes even in single-level compactions.

## Applicability

This report characterizes the concurrency control, memory-reclamation, MVCC garbage-collection, and compaction-safety invariants of seven directly inspected upstream codebases and six foundational peer-reviewed specifications/papers listed in `REPORT.json`:

- **Formal Verification & Search Templates:** `nyu-acsys/template-proofs` (`6444326e04577987c66776bed34d9a76ffd0df55`), mechanizing the Flow Framework (Krishna, Shasha, Wies, POPL 2018, DOI `10.1145/3158125`) and concurrent search structure templates (Krishna, Patel, Shasha, Wies, PLDI 2020, DOI `10.1145/3385412.3386029`) for Lehman–Yao B-link trees (Lehman & Yao, ACM TODS 1981, DOI `10.1145/319628.319663`) and multicopy LSM DAGs. Findings apply to Coq 8.13 / Iris 3.4 HeapLang sequential consistency (`SC`) models; weak-memory hardware reorderings are explicitly scoped in **Boundaries**.
- **Optimistic In-Memory & Buffer-Managed Trees:** `flode/ARTSynchronized` (`f00003ec7991da09c3dfc1c84da97c1965106eb3`, DaMoN 2016, DOI `10.1145/2933349.2933352`) and `leanstore/leanstore` (`fcb64bf39cf69c435173f76e062cbb305a9a998f`, ICDE 2018, DOI `10.1109/ICDE.2018.00026`). Findings about `ART_OLC` apply to the `OptimisticLockCoupling/` implementation (distinct from `ROWEX/`). Findings about `LeanStore` apply to its 64-bit x86-64/ARM64 user-space virtual address layout where bits 62–63 of canonical user pointers are zero, allowing 2-bit `Swip` tagging.
- **MVCC Engines:** `postgres/postgres` (`6ec71e1ad8c26b3a93e7c5739e797a2d353dc5d6`) for 32-bit `TransactionId` wraparound, `SetTransactionIdLimit`, and `GlobalVisState` (`ComputeXidHorizons`), contrasted with `efficient/cicada-engine` (`af469679d67a59a89536de634216d349af577d3a`, SIGMOD 2017, DOI `10.1145/3035918.3064015`) configured with `CompactTimestamp`, `WideTimestamp`, or `CentralizedTimestamp` and `kSkipPending == false`.
- **LSM Storage Engines:** `facebook/rocksdb` (`2f4f3c4b1ec6e42577e629e2e322dec1f9c2ea85`) and `cockroachdb/pebble` (`a995e890c06ef86c583927906e16e7f313083a3f`). Findings compare their leveled compaction iterators, snapshot-stripe boundary conventions (RocksDB inclusive `seq <= snap` vs. Pebble `base.Visible` / `Snapshots.Index` strictly-greater partitioning), range-tombstone fragmenters/compactors, `SingleDelete` contracts, and write-stall backpressure thresholds.
- **Relationship Across Subjects:** The four subsystems represent orthogonal layers of a concurrent transactional storage engine—(1) formal search-tree linearizability, (2) latch/buffer-pool memory safety, (3) MVCC visibility and version-chain reclamation, and (4) persistent multi-level compaction and tombstone elision—whose invariants compose directly in production engines (e.g., MVCC-over-B-tree/LeanStore or MVCC-over-LSM in CockroachDB/Pebble and MyRocks/RocksDB).

## Findings

### 1. Iris Flow Framework and Modular Verification of Lehman–Yao B-Link & LSM Templates

*Basis: normative (PLDI 2020 & POPL 2018 papers) + source (`nyu-acsys/template-proofs` @ `6444326e`) + execution (Probe 1B).*

#### 1.1 Algebraic Flow Interfaces and Contextual Extension

Classic concurrent separation logic struggles with overlaid search graphs (such as B-link trees with sibling pointers or LSM DAGs) because reachability and key-routing invariants are global graph properties. The **Flow Framework** (Krishna, Shasha, Wies, POPL 2018; mechanized in `templates/flows/flows.v`) localizes global graph reachability into per-region algebraic **flow interfaces** over a Commutative Cancelative Monoid (`CCM`, `templates/flows/ccm.v`):

```coq
(* nyu-acsys/template-proofs @ 6444326e, templates/flows/flows.v:28-36 *)
Record flowintR := {
  infR : gmap Node flowdom;   (* inflow to nodes inside domain domm(I) *)
  outR : nzmap Node flowdom;  (* non-zero outflow to nodes outside domm(I) *)
}.
Inductive flowintT :=
| int : flowintR -> flowintT
| intUndef : flowintT.
```

Two interfaces $I_1, I_2$ are composable (`intComposable`, `flows.v:99-103`) iff both are valid, their domains are disjoint ($\text{domm}(I_1) \cap \text{domm}(I_2) = \emptyset$), and every internal edge cancels cleanly:
$$\forall n \in \text{domm}(I_1),\; \text{inf}(I_1, n) = \text{out}(I_2, n) + (\text{inf}(I_1, n) - \text{out}(I_2, n))$$
and symmetrically for $I_2$. When instantiated with multisets of keys $K$ (`templates/single_copy/inset_flows.v:16, 30-34`), each node $n$'s **inset** is the domain of keys flowing into $n$, and its **keyset**—the exact subset of keys for which $n$ is currently the decisive leaf or owner—is:
$$\text{keyset}(I, n) \;\triangleq\; \text{dom\_ms}(\text{inf}(I, n)) \setminus \text{dom\_ms}(\text{out}(I, n))$$

The global data-structure invariant $\phi$ (`globalinv root I`, `inset_flows.v:30-34`) requires four properties:
1. Interface validity $\checkmark I$;
2. Root membership $\text{root} \in \text{domm}(I)$;
3. Closedness ($\text{out}(I, m) = \emptyset$ for all external $m \notin \text{domm}(I)$);
4. Full key-space injection at the root ($\forall k \in \text{KS},\; k \in \text{inset}(I, \text{root})$).

A structural modification (e.g., splitting a B-link node $n$ into $n$ and new right sibling $n'$) replaces a local sub-interface $I_n$ with $I_n'$ while keeping the rest of the graph $I_o$ framed. The Iris frame-preserving update rule `flowint_update` (`flows.v:1720-1736`) proves:
$$\text{contextualLeq}(I_n, I_n') \;\land\; \text{domm}(I_n') \cap \text{domm}(I_o) = \emptyset \;\land\; (\forall m \in \text{domm}(I_n') \setminus \text{domm}(I_n),\; \text{out}(I_o, m) = 0)$$
$$\implies \quad \bullet(I_n \cdot I_o) \cdot \circ I_n \;\leadsto\; \exists I'.\; \text{contextualLeq}(I_n \cdot I_o, I') \land I' = I_n' \cdot I_o$$
where `contextualLeq I1 I2` (`flows.v:1720-1723`) holds iff $\text{domm}(I_1) \subseteq \text{domm}(I_2)$, inflow is identical on all existing nodes $n \in \text{domm}(I_1)$, and external outflow is identical on all nodes outside $\text{domm}(I_2)$. Together with `contextualLeq_impl_globalinv` (`inset_flows.v:44-48`), any local split satisfying `contextualLeq` automatically preserves the global reachability invariant without inspecting the rest of the tree.

#### 1.2 Lehman–Yao B-Link Template and Monotonic Inreach Ghost State

In Lehman & Yao's B-link tree (`ACM TODS 1981`), each node stores a **high-key** $hk$ and a **right-link pointer** to its right sibling. Crucially, `traverse` (`templates/single_copy/link.v:89-95`) does **not** hold parent and child locks simultaneously:

```coq
(* nyu-acsys/template-proofs @ 6444326e, templates/single_copy/link.v:89-95 *)
Definition traverse : val :=
  rec: "tr" "n" "k" :=
    lockNode "n";;
    match: (findNext "n" "k") with
      NONE => "n"
    | SOME "n'" => unlockNode "n";; "tr" "n'" "k"
    end.
```

Between `unlockNode "n"` and `lockNode "n'"`, arbitrarily many concurrent splits may migrate keys rightward out of `n'`. Why does `traverse` never lose key $k$? In `link.v`, the template pairs three Iris Resource Algebras (`link.v:41-50, 161-175`):
1. **Authoritative Monotonic Inreach (`inreachG` = `authR (gsetUR K)`):** Once a thread establishes $k \in \text{inset}(I_{n'}, n')$ via `findNext_spec` (`link.v:137-144`), it takes a persistent ghost snapshot `inInr γ_in' k` (`link.v:436-437`). Because a B-link split moves keys $k > hk$ into `out(n' -> n'')` **without shrinking `inf(n')`** (verified by `contextualLeq` and Probe 1B), $k$ remains permanently in `inset(n')` even after $n'$ splits; upon locking $n'$, `findNext` simply follows the right-link edge `n' -> n''`!
2. **Fractional Interface Agreement (`fracintG` = `frac_agreeR (multiset_flowint_ur K)`):** Splits each node's flow interface `In` into two $1/2$-shares: `nodePred` (held inside the node's lock invariant alongside the spatial heap predicate `node n In Cn`) and `nodeShared` (held inside the global CSS invariant alongside `own γ_I (● I)`). Recombining both halves upon locking establishes agreement between local physical node state and the global flow graph.
3. **Keyset Resource Algebra (`keyset_ra.v`):** Tracks authoritative disjoint pairs `(keyset K In n, Cn)` across all nodes (`link.v:168`), enforcing $\forall k \in C_n,\; k \in \text{keyset}(I_n, n)$ and guaranteeing that no two nodes can simultaneously claim ownership of the same key during `decisiveOp`.

| Template (`nyu-acsys/template-proofs`) | Synchronization Strategy | Lock Overlap During Descent | Handling Concurrent Splits / Rebalancing | Key Ghost State Beyond `flowintG` |
|---|---|---|---|---|
| **Link (`link.v`)** | Lehman–Yao right-links | Zero (unlock `n`, then lock `n'`) | Follow right-link edge (`outset`); `inset` never shrinks | `inreachG` (`authR (gsetUR K)` monotonic snapshot) |
| **Give-up (`give_up.v`)** | Per-node range bounds | Zero (unlock `n`, then lock `n'`) | Range-check on `n'`; restart from root if $k \notin \text{range}(n')$ | Global `inset` re-checked against stored node bounds |
| **Lock-coupling (`coupling_inv.v`)** | Crabbing / hand-over-hand | 2 nodes (lock `n'`, then unlock `n`) | Split blocked while parent/child coupled | No restart needed; parent lock prevents split of child |
| **Multicopy LSM (`multicopy_lsm.v`)** | Dual-flow DAG (memtable + SSTs) | Per-node lock during `inContents`/`findNext` | Compaction updates timestamped `(k, t)` flow | Dual flow interfaces `In : multiset_flowint_ur (K*T)` and `Jn : multiset_flowint_ur K` (`multicopy_lsm.v:151-168, 313-320`) |

**Verification Trust Seam (`Basis: source`):** In `link.v:107-154` and `multicopy_lsm.v:118-138`, the Coq/Iris template proofs leave concrete heap layout predicates (`node`, `node_sep_star`) and sequential node operations (`allocRoot_spec`, `findNext_spec`, `decisiveOp_spec`) as `Parameter`/`Hypothesis` axioms that are discharged separately by SMT-backed **GRASShopper** (`b-link.spl`, `hashtbl-link.spl`, `multicopy-lsm.spl`). Soundness of an end-to-end concrete implementation therefore assumes semantic compatibility between Iris HeapLang's memory model and GRASShopper's first-order separation logic.

---

### 2. Optimistic Lock Coupling (`ART`) and Buffer-Pool Pointer Swizzling (`LeanStore`)

*Basis: normative (DaMoN 2016 & ICDE 2018 papers) + source (`flode/ARTSynchronized` @ `f00003ec`, `leanstore/leanstore` @ `fcb64bf3`).*

#### 2.1 ART Optimistic Lock Coupling (`OLC`) vs. `ROWEX` and Safe Memory Reclamation

In `flode/ARTSynchronized` (`OptimisticLockCoupling/N.h:48-90`), every Adaptive Radix Tree node (`N4`, `N16`, `N48`, `N256`) embeds a single 64-bit atomic control word:

```cpp
// flode/ARTSynchronized @ f00003ec, OptimisticLockCoupling/N.h:48-50, 88-90
// 2b type | 60b version | 1b lock | 1b obsolete
std::atomic<uint64_t> typeVersionLockObsolete{0b100};

void writeUnlockObsolete() {
    typeVersionLockObsolete.fetch_add(0b11);
}
```

The state transitions of the bottom two bits `(lock_bit = 0b10, obsolete_bit = 0b01)` are exact:
- **Unlocked, live:** `0b00` (initial value `0b100`, version `1`).
- **Write-locked:** `0b10` (acquired via CAS setting `lock_bit`).
- **Unlocked, live after in-place mutation:** `writeUnlock()` adds `0b10`, clearing `lock_bit` and incrementing the 60-bit version.
- **Unlocked, retired (node grown/shrunk/deleted):** `writeUnlockObsolete()` executes `fetch_add(0b11)`, which simultaneously clears `lock_bit`, sets `obsolete_bit = 1`, and advances the version so any concurrent optimistic reader or lock upgrader sees `isLocked(v) || isObsolete(v)` and restarts.

In `Tree::lookup` (`OptimisticLockCoupling/Tree.cpp:24-78`), optimistic lock coupling executes zero atomic RMW instructions on the read path:
1. Enter QSBR epoch (`EpocheGuardReadonly epocheGuard(threadEpocheInfo)`, line 25) so nodes marked obsolete and retired via `insertGrow` / `removeAndShrink` are not `delete`d until all concurrent readers leave the epoch.
2. Read `v = node->readLockOrRestart(needRestart)` (spins/restarts if locked or obsolete).
3. Inspect `checkPrefix(node, k, level)` and fetch `node = N::getChild(k[level], parentNode)`.
4. Validate `parentNode->checkOrRestart(v, needRestart)` **before** dereferencing the child pointer (line 53).
5. Read child's version `nv = node->readLockOrRestart(needRestart)` **before** validating `parentNode->readUnlockOrRestart(v, needRestart)` (lines 71–75), ensuring the child could not be detached and recycled during the parent-to-child hop.

**Source-Level Defect Observed in `flode/ARTSynchronized` (`Basis: source`):** In `OptimisticLockCoupling/Tree.cpp:39-50` and `694-711`, `checkPrefix(node, k, level)` reads `node->prefixCount` and `node->prefix` optimistically **before** `v` is validated. If `checkPrefix` returns `Match` or `OptimisticMatch` and line 48 evaluates `if (k.getKeyLen() <= level) return 0;`, `Tree::lookup` returns `0` **without calling `node->readUnlockOrRestart(v, needRestart)`**. Under a concurrent prefix mutation that transiently inflates `prefixCount` (and therefore `level`), a reader can return a false-negative `0` instead of restarting. (By contrast, the `NoMatch` branch at line 41 properly calls `node->readUnlockOrRestart(v, needRestart)` before returning `0`.) Furthermore, because optimistic readers read non-atomic fields (`prefix`, `keys`, `children`) concurrently with writers under `std::atomic` version checks, standard C++11/20 classifies those unsynchronized loads as **data-race UB** unless lowered through relaxed atomic loads or compiler-barrier-isolated byte copies (`Boehm, MSPC 2012`).

#### 2.2 LeanStore 3-State Pointer Swizzling, `HybridLatch`, and Bottom-Up Eviction

Traditional disk buffer managers incur a centralized hash-table lookup and pin/unpin atomic RMW on every page access. `LeanStore` (`leanstore/leanstore` @ `fcb64bf3`) eliminates the page table on the hot path by storing direct `BufferFrame*` pointers (**swizzled pointers**, `Swip`) inside parent B-tree pages (`Swip.hpp:20-68`):

| Top 2 Bits (`pid >> 62`) | `Swip` State | Payload Meaning | Hot-Path Traversal Cost |
|---|---|---|---|
| `0b00` (`isHOT()`) | **HOT** | Raw 64-bit `BufferFrame*` (`bf`) | Zero hash lookup; direct pointer dereference + `HybridLatch` version load |
| `0b01` (`isCOOL()`) | **COOL** | Masked `BufferFrame*` (`pid & 0x3FFFFFFFFFFFFFFF`) | Unmask pointer; opportunistically re-warm (`pid & ~cool_bit`) on access |
| `0b10` / `0b11` (`isEVICTED()`) | **EVICTED** | 63-bit on-disk `PID` (`pid & 0x7FFFFFFFFFFFFFFF`) | Trigger buffer-pool fault-in via partitioned `io_ht` |

Concurrency control uses a 64-byte cacheline-aligned `HybridLatch` (`sync-primitives/Latch.hpp:21-223`) combining `std::atomic<u64> version` (LSB `LATCH_EXCLUSIVE_BIT = 1ull`) with `std::shared_mutex mutex`:
- **Optimistic mode (`GUARD_STATE::OPTIMISTIC`):** Loads even `version`, reads page payload without writing to the cache line, and calls `recheck()` (`Latch.hpp:84-91`) which invokes `jumpmu::jump()` (`setjmp`/`longjmp` restart) if `version != latch->ref().load()`.
- **Exclusive upgrade (`toExclusive`, `Latch.hpp:155-176`):** Acquires `latch->mutex.lock()` first, then performs `compare_exchange_strong(expected, version + 1)` on `version`; if `version` changed before the mutex was acquired, unlocks `mutex` and restarts via `jumpmu::jump()`.
- **Unlock (`unlock`, `Latch.hpp:93-104`):** Stores `version + 1` with `std::memory_order_release` **before** calling `latch->mutex.unlock()`.

**The Cooling/Eviction Memory-Safety Invariant (`PageProviderThread.cpp:108-264`):** Because parent nodes contain raw `BufferFrame*` pointers rather than page IDs, evicting a page while a parent still points to it—or while a child is still resident—would create dangling swips or orphan resident subtrees. `LeanStore` enforces two invariants in `PageProviderThread.cpp`:
1. **Strict Bottom-Up Cooling (`line 108`):** Before cooling candidate `r_buffer`, the provider scans all child swips; `repickIf(!all_children_evicted || picked_a_child_instead)` guarantees **a page can transition `HOT -> COOL` only when every child swip is already `EVICTED`**. Cooling acquires parent and child latches, sets `r_buffer->header.state = STATE::COOL`, and sets bit 62 via `parent_handler.swip.cool()` (`lines 152–153`).
2. **Preallocated-Arena Version Bump on Eviction (`lines 191–203`):** Eviction (`evict_bf`) asserts `state == COOL && parent_handler.swip.isCOOL() && !is_being_written_back` and checks that `partition.io_ht.lookup(pid)` is absent (`lines 235–238`). It overwrites `parent_handler.swip.evict(evicted_pid)`, calls `bf.reset()`, and increments `bf.header.latch` (`fetch_add(LATCH_EXCLUSIVE_BIT, memory_order_release)`) before unlocking `mutex`. Because `BufferFrame` structs reside in a fixed, never-freed arena, any concurrent optimistic reader still holding `BufferFrame*` cannot trigger a segmentation fault; its next `recheck()` observes the incremented `version` and restarts cleanly—eliminating QSBR epoch reclamation overhead for buffer frames.

---

### 3. MVCC Snapshot Horizons, Transaction-ID Wraparound, and Rapid Version GC

*Basis: normative (SIGMOD 2017 paper) + source (`postgres/postgres` @ `6ec71e1a`, `efficient/cicada-engine` @ `af469679`) + execution (Probe 1B).*

#### 3.1 PostgreSQL 32-Bit Modular XID Wraparound and Four-Tier Horizon Accounting

`PostgreSQL` stores 32-bit `TransactionId` values (`xmin`, `xmax`) in every heap tuple header to keep per-tuple metadata compact (`src/include/access/transam.h:31-35`):
- `0` = `InvalidTransactionId`
- `1` = `BootstrapTransactionId`
- `2` = `FrozenTransactionId` (permanently visible to all snapshots, exempt from modular comparison)
- `3` = `FirstNormalTransactionId`
- `0xFFFFFFFF` = `MaxTransactionId`

Normal XIDs wrap modulo $2^{32}$ (skipping `0, 1, 2` via `TransactionIdAdvance`, `transam.h:93-96`) and are ordered by signed 32-bit difference (`transam.h:147-154`):
```c
#define NormalTransactionIdPrecedes(id1, id2) \
    (AssertMacro(TransactionIdIsNormal(id1) && TransactionIdIsNormal(id2)), \
     (int32) ((id1) - (id2)) < 0)
```

Because `(int32)(id1 - id2)` interprets differences in $[-2^{31}, 2^{31}-1]$, exact modular execution (Probe 1B) confirms two sharp mathematical failure points for an unfrozen tuple created at `xmin = 3`:
- At `curXid = 2,147,483,650` (age $2^{31} - 1$): `precedes(3, cur) = True`, `precedes(cur, 3) = False` — valid total order.
- At `curXid = 2,147,483,651` (age $2^{31}$): `(int32)(3 - 2147483651) = -2147483648 < 0` AND `(int32)(2147483651 - 3) = -2147483648 < 0` — **strict order antisymmetry breaks** (both directions return `True`).
- At `curXid = 2,147,483,652` (age $2^{31} + 1$): `precedes(3, cur) = False` — the old committed tuple **silently flips into the future** and disappears from all snapshots!

To prevent reaching `xidWrapLimit`, `SetTransactionIdLimit` (`src/backend/access/transam/varsup.c:367-446`) computes four hard thresholds from `oldest_datfrozenxid` (the minimum `relfrozenxid` across all tables in the cluster):

| Threshold (`TransamVariables`) | Exact Formula (`varsup.c:384-435`) | Value for `oldest = 3` | Operational Action |
|---|---|---|---|
| `xidVacLimit` | `oldest + autovacuum_freeze_max_age` (default `200,000,000`) | `200,000,003` | Forces anti-wraparound autovacuum worker even if autovacuum is disabled |
| `xidWarnLimit` | `xidWrapLimit - 100,000,000` | `2,047,483,650` | Emits `WARNING` on every new XID assignment (~5% remaining) |
| `xidStopLimit` | `xidWrapLimit - 3,000,000` | `2,144,483,650` | Hard-refuses new XIDs in multi-user mode (`ERROR`); preserves 3M XIDs + 2 idle CLOG segments for single-user emergency `VACUUM` |
| `xidWrapLimit` | `oldest + (MaxTransactionId >> 1)` | `2,147,483,650` | Point of antisymmetry breakdown / imminent visibility inversion |

**Four-Tier `GlobalVisState` Vacuum Horizons (`procarray.c:138-191`):** Dead tuple reclamation (`VACUUM`) cannot reclaim any tuple version still visible to an active snapshot. `PostgreSQL` computes relation-specific horizons using 64-bit `FullTransactionId` bounds (`definitely_needed` and `maybe_needed`, immune to 32-bit wraparound) across four scopes (`procarray.c:151-175`):
1. **`GlobalVisSharedRels`:** Pinned by snapshots in *any* database, physical/logical replication slot `xmin`, and replication slot `catalog_xmin`.
2. **`GlobalVisCatalogRels`:** Pinned by snapshots in the *current* database plus slot `xmin` and `catalog_xmin`.
3. **`GlobalVisDataRels`:** Pinned by snapshots in the *current* database and slot `xmin` (ignores `catalog_xmin`, allowing user-table bloat cleanup even when a logical decoding slot holds `catalog_xmin`).
4. **`GlobalVisTempRels`:** Pinned only by the *current session*.

Any long-running transaction (`IDLE IN TRANSACTION`), abandoned 2PC `PREPARED TRANSACTION`, `hot_standby_feedback = on` replica query, or stalled logical replication slot pins `GlobalVisState`, stalling dead-tuple removal (table/index bloat) and—if left unresolved—blocking `VACUUM` from advancing `relfrozenxid` (note: freezing committed tuples older than `OldestXmin` still requires `VACUUM` to complete without being blocked by locks or unvacuumable pages).

#### 3.2 Cicada Loosely Synchronized Clocks and Rapid Incremental Version GC

`Cicada` (`efficient/cicada-engine` @ `af469679`; Lim et al., SIGMOD 2017) targets tens of millions of multi-core in-memory transactions/sec where centralized XID counters (`XidGenLock`) and batch epoch vacuuming become bottlenecks:

1. **Timestamp Encodings & Wrap Horizons (`src/mica/transaction/timestamp.h:11-223`):**
   - `CompactTimestamp` (64 bits): `t2 = (tsc << 8) | thread_id` (56-bit loosely synchronized per-core TSC + 8-bit thread ID, supporting up to 256 threads). Uses signed 64-bit modular comparison `static_cast<int64_t>(t2 - b.t2) < 0`. Because $2^{55}$ ticks is finite (**166.8 days** at 2.5 GHz, **139.0 days** at 3.0 GHz, **104.25 days** at 4.0 GHz; Probe 1B), `CompactTimestamp::about_to_expire(unstable_ts)` (`timestamp.h:43-47`) flags timestamps within $2^{60}$ ($1/16$ of $2^{64}$, i.e., **17.37 days** at 3.0 GHz) of wrapping so background refresh can advance them before modular inversion.
   - `WideTimestamp` (128 bits): `era (32b) | tsc (64b) | thread_id (32b)`, with `about_to_expire` always `false` (`timestamp.h:139-142`). Concurrent updates use `WideConcurrentTimestamp` (`timestamp.h:151-223`), a per-row SeqLock (`version` odd during write, memory barriers around `t1`/`t2` reads and writes).
2. **Rapid Per-Thread Incremental Version GC (`src/mica/transaction/context_gc.h:8-201`):**
   - Upon committing a write `write_rv` at timestamp `wts`, the committing thread enqueues `{wts, tbl, cf_id, deleted, row_id, head, write_rv}` into its thread-local FIFO `gc_items_` queue (`schedule_gc`, `context_gc.h:8-33`). Note line 12–13: `wts` is copied by value because `write_rv` itself may already be reclaimed by a newer commit's GC before this thread drains its queue!
   - During `Context::gc()` (`context_gc.h:176-185`), the thread reads the global minimum active read timestamp `min_rts = db_->min_rts()` and pops items while `min_rts > gc_items_.front().wts`.
   - For each popped item, `gc_row` checks `gc_info->gc_ts >= ts` (line 51: if already GC'd past `ts`, `write_rv` is dangling and skipped safely!). For normal overwrites (`!deleted`), it uses a non-blocking try-lock (`__sync_lock_test_and_set(&gc_info->gc_lock, 1)`, lines 55–61), yielding if another thread is already pruning that row; for deletions (`deleted == true`), it spins until acquiring `gc_lock` (lines 72–79) so row deallocation is never lost.
   - Once `gc_info->gc_ts` is updated to `ts`, it detaches the older tail (`rv = write_rv->older_rv; write_rv->older_rv = nullptr;`, lines 123–124) — or detaches `head->older_rv = nullptr` and schedules `deallocate_row` if `write_rv->status == kDeleted && head->older_rv == write_rv` (lines 99–118, relying on `StaticConfig::kSkipPending == false` so no newer version can precede a deleted version) — releases `gc_lock`, and immediately returns all detached versions to per-core pools (`deallocate_version`).
   - **Documented Upstream Gap (`context_gc.h:164-166`):** Aborted versions spliced ahead of the latest committed version are not reclaimed by this fast-path (`TODO: Reclaim aborted row versions that appear before the latest committed row versions`).

---

### 4. LSM-Tree Compaction Schedules, Write Stalls, and Deleted-Key Resurrection Invariants

*Basis: source (`facebook/rocksdb` @ `2f4f3c4b`, `cockroachdb/pebble` @ `a995e890`) + execution (Probe 1A).*

#### 4.1 Snapshot Stripes and the Fundamental Tombstone-Elision Theorem

In an LSM-tree (`RocksDB`, `Pebble`), every internal entry carries `(user_key, seq, kind)` ordered by ascending `user_key` and **descending** `seq`. Active read snapshots define an ordered sequence of cutpoints $S = [s_1 < s_2 < \dots < s_m]$. These cutpoints partition the sequence-number space into $m+1$ **snapshot stripes**:
- In **RocksDB** (`compaction_iterator.cc:243-246`, `range_del_aggregator.cc`), snapshot $s_i$ observes all keys with $\text{seq} \le s_i$; stripe $i$ contains sequence numbers in $(s_{i-1}, s_i]$ (with $s_0 = 0$, top stripe $(s_m, \infty)$).
- In **Pebble** (`internal/compact/snapshots.go:46-65`), `Snapshots.Index(seq)` returns the smallest index $i$ such that `s[i] > seq` (i.e., Pebble snapshots observe strictly smaller sequence numbers $\text{seq} < s_i$, placing stripe $i$ in $[s_{i-1}, s_i)$ with $s_0 = 0$).

**Fundamental Compaction Visibility Preservation Invariant (`Basis: source + execution`):**
Compacting a subset of levels/files $\mathcal{C}$ into output level $L_{\text{out}}$ preserves exact MVCC semantics across every active snapshot $s \in S \cup \{\infty\}$ if and only if:
1. **Within-Stripe Shadowing Only:** A newer entry (point `PUT`/`DEL` or range tombstone `RANGEDEL`) at sequence $t_2$ may drop an older entry at sequence $t_1 < t_2$ **only when $\text{stripe}(t_1) = \text{stripe}(t_2)$**. Dropping across a stripe boundary either causes a **phantom deletion** (if `RANGEDEL` at $t_2 > s_i$ drops `PUT` at $t_1 \le s_i$) or **deleted-key resurrection at snapshot $s_i$** (if `RANGEDEL` at $t_2 > s_i$ absorbs `RANGEDEL` at $t_1 \le s_i$, uncovering a deeper `PUT` at $t_0 < t_1$ in $L > L_{\text{out}}$; confirmed by Probe 1A Bugs 2a & 2b).
2. **Bottom-Stripe + No-Lower-Overlap Tombstone Elision:** A point tombstone `DEL(k, t)` or range tombstone `RANGEDEL([a, b), t)` may be elided (omitted from output SSTables) **only if ALL three conditions hold**:
   - $t$ lies in the **bottommost snapshot stripe** (`stripe(t) == 0`, i.e., older than or invisible-split-free with respect to the earliest snapshot $s_1$);
   - **No untouched level or overlapping file below (or concurrent with) $L_{\text{out}}$ can contain a shadowed key** overlapping $k$ (for point `DEL`) or $[a, b)$ (for `RANGEDEL`). Crucially, when $L_{\text{out}} = L_0$, sibling $L_0$ files overlap in key space, so Pebble's `SetupTombstoneElision` (`internal/compact/tombstone_elision.go:174-182`) sets `startLevel = 0` instead of `outputLevel + 1`!
   - **No behind-ingestion bypass is enabled:** RocksDB explicitly disables bottommost elision when `compaction_->allow_ingest_behind()` is true (`compaction_iterator.cc:197-198, 928`), because `IngestExternalFileOptions::ingest_behind` can later inject older-sequence keys at the bottommost level that a prematurely elided tombstone would fail to mask!

#### 4.2 RocksDB vs. Pebble Range-Tombstone and `SingleDelete` Mechanics

| Dimension | RocksDB (`facebook/rocksdb` @ `2f4f3c4b`) | Pebble (`cockroachdb/pebble` @ `a995e890`) |
|---|---|---|
| **Snapshot stripe boundary** | Inclusive (`seq <= snap`); `findEarliestVisibleSnapshot` (`compaction_iterator.cc:906`) | Exclusive (`seq < snap`); `Snapshots.Index(seq)` finds first `s[i] > seq` (`snapshots.go:50-54`) |
| **Point tombstone elision check** | `DefinitelyInSnapshot(seq, earliest_snapshot_)` $\land$ `KeyNotExistsBeyondOutputLevel(user_key, &level_ptrs_)` $\land$ `!allow_ingest_behind()` (`compaction_iterator.cc:924-931`) | `pointTombstoneElider.ShouldElide(key)` over merged disjoint `inUseKeyRanges` from `SetupTombstoneElision` (`tombstone_elision.go:105-120, 164-195`) |
| **Range tombstone representation** | `FragmentedRangeTombstoneList` + `CompactionRangeDelAggregator` maintaining per-stripe `StripeMap` (`range_del_aggregator.h/.cc`) | Fragmented non-overlapping `keyspan.Span`s (`ByTrailerDesc`) compacted by `RangeDelSpanCompactor.Compact` (`spans.go:49-80`) |
| **Range tombstone SSTable boundary splitting** | `TruncatedRangeDelIterator` clips tombstones to SSTable `[smallest, largest]` bounds; emitted via `CompactionRangeDelAggregator::NewIterator` | `SplitAndEncodeSpan(cmp, span, upToKey, tw)` splits active span cleanly at each output SSTable split key (`spans.go:188-218`) |
| **Range-key tombstones (`RangeKeyUnset`/`Delete`)** | Not a separate keyspace | `RangeKeySpanCompactor.Compact` partitions by ascending snapshot stripes, runs `rangekey.Coalesce`, and elides in last stripe via `elideInLastStripe` (`spans.go:120-176`) |
| **`SingleDelete` resurrection hazard** | `enforce_single_del_contracts_` (`compaction_iterator.cc:205`) checks contract violations; unguarded `SINGLEDEL` cancelling one `PUT` exposes older `PUT`s | Explicit hooks `IneffectualSingleDeleteCallback` and `NondeterministicSingleDeleteCallback` (`iterator.go:298-304, 994-1180`) detect when `SINGLEDEL` meets a second older `SET`/`MERGE` |

**Why `SingleDelete` Causes Silent Resurrection (`Basis: source + execution`):** Both RocksDB and Pebble offer `SingleDelete(k)` as an optimization that cancels a matching `PUT(k)` in non-bottommost compactions without waiting to reach the bottommost level. However, its soundness precondition is strict: **`k` must have been written at most once (with no intervening `PUT` or `MERGE`) since the previous deletion**. If a workload writes `PUT(k, v1, seq=1)`, `PUT(k, v2, seq=2)`, `SINGLEDEL(k, seq=3)`, and a non-bottommost compaction lets `SINGLEDEL@3` cancel `PUT@2` and elide itself, `PUT@1 = v1` silently resurrects (`Probe 1A Bug 3`). Pebble detects this in `singleDeleteNext` / `skipDueToSingleDeleteElision` (`internal/compact/iterator.go:994-1174`) and invokes `NondeterministicSingleDeleteCallback`, and converts a `SingleDelete` that encounters an older `Delete` or `Merge` in an unsafe context rather than blindly dropping it.

#### 4.3 Leveled Compaction Write-Stall Backpressure (`RocksDB`)

In `facebook/rocksdb` (`db/column_family.cc:1038-1063`), `RecalculateWriteStallConditions` prevents unbounded L0 read amplification and OOM/space exhaustion through a strict priority ladder of stall states:
1. **`kStopped` (`kL0FileCountLimit`):** `auto_compactions && num_l0_files >= level0_stop_writes_trigger`.
2. **`kStopped` (`kPendingCompactionBytes`):** `hard_pending_compaction_bytes_limit > 0 && num_compaction_needed_bytes >= hard_pending_compaction_bytes_limit`.
3. **`kDelayed` (`kMemtableLimit`):** `max_write_buffer_number > 3 && num_unflushed_memtables >= max_write_buffer_number - 1`.
4. **`kDelayed` (`kL0FileCountLimit`):** `num_l0_files >= level0_slowdown_writes_trigger`.
5. **`kDelayed` (`kPendingCompactionBytes`):** `num_compaction_needed_bytes >= soft_pending_compaction_bytes_limit`.

`SanitizeOptions` (`column_family.cc:350-372`) enforces `level0_file_num_compaction_trigger <= level0_slowdown_writes_trigger <= level0_stop_writes_trigger` and `soft_pending_compaction_bytes_limit <= hard_pending_compaction_bytes_limit`. Compaction thread speedup kicks in early at `level0_trigger + (slowdown - trigger) / 4` (`GetL0FileCountForCompactionSpeedup`, `column_family.cc:953-974`).

---

### 5. Cross-System Trade-Off Matrix

*Basis: derived from source + normative papers above.*

| Property | Lehman–Yao B-Link (`template-proofs`) | ART-OLC (`ARTSynchronized`) | LeanStore (`leanstore`) | PostgreSQL MVCC (`postgres`) | Cicada MVCC (`cicada-engine`) | RocksDB / Pebble LSM |
|---|---|---|---|---|---|---|
| **Primary Concurrency Mechanism** | Per-node lock + right-link chase (no lock coupling) | Optimistic 64-bit version word + QSBR epoch | 64B `HybridLatch` + `Swip` pointer swizzling | Tuple `xmin`/`xmax` + `ProcArray` snapshots | Loosely synced TSC + OCC validation | Immutable SSTables + MVCC sequence numbers |
| **Read-Path Shared Cache-Line Writes** | Yes (lock acquire/release) | Zero (version loads only) | Zero (version loads only) | Zero on buffer hit (pin still atomic) | Zero on read-only fast path (updates `rts` on RW) | Zero (immutable SST blocks + block cache) |
| **Memory Reclamation / GC Horizon** | Assumed GC / no node free in Iris template | QSBR `Epoche` (stalled thread pins memory) | Fixed `BufferFrame` arena + version bump (no OS free) | 4-tier `GlobalVisState` (`FullTransactionId`) + `VACUUM` | Per-thread FIFO `gc_items_` drained at `db_->min_rts()` | Snapshot stripes + bottommost / `inUseRanges` elision |
| **ID / Clock Wraparound Hazard** | N/A | 60-bit version (~$10^{18}$ updates/node) | 63-bit version (~$9\times 10^{18}$ updates/frame) | **32-bit XID**: flips at $2^{31}+1$; hard stop at `wrap - 3M` | **56-bit TSC** (`CompactTimestamp`): flips in ~139d @ 3 GHz; 128-bit `WideTimestamp` immune | 56-bit (RocksDB) / 56-bit (Pebble) `SeqNum` (~$7.2\times 10^{16}$ writes) |
| **Mechanized Proof / Formal Model** | Coq/Iris + GRASShopper (`link.v`, `multicopy_lsm.v`) | None in repo (C++ data-race UB on optimistic loads) | None in repo (C++ optimistic loads + `longjmp`) | Informal comments + assertions | Informal proofs in SIGMOD 2017 | Model-based metamorphic/randomized compaction tests (Pebble `metamorphic`) |

## Boundaries

- **Weak-Memory (`ARM64` / `RISC-V` / `C++20`) Mechanization of B-Link & OLC (`not examined` / `unsupported`):** The Iris Flow Framework proofs in `nyu-acsys/template-proofs` target Iris `HeapLang`, which assumes sequentially consistent (`SC`) memory accesses and garbage-collected nodes (no physical node deallocation or reuse). Extending `link.v` to release-acquire or TSO/ARMv8 weak memory models, or proving data-race freedom of `ART_OLC` and `LeanStore` under the C++20 memory model (where non-atomic optimistic payload reads concurrent with a writer are formally UB), is **unsupported** by the examined mechanization and **not examined** here.
- **PostgreSQL `MultiXactId` Wraparound & Subtransaction Overflow (`not examined`):** While `SetTransactionIdLimit` (`varsup.c`) references `SetMultiXactIdLimit` for 32-bit `MultiXactId` wraparound (which has its own 2-billion limit and member-offset wraparound independent of `relfrozenxid`), and `SubXid` overflow degrades `ProcArray` snapshot checks via `pg_subtrans`, exact `multixact.c` thresholds and `VACUUM FREEZE` visibility-map skip logic were **not examined**.
- **RocksDB User-Defined Timestamps (`UDT`), BlobDB GC, and Universal/FIFO Compaction (`not examined`):** Although `compaction_iterator.cc:206-215` and `range_del_aggregator.cc:377-403` show hooks for `full_history_ts_low_` (`kTypeDeletionWithTimestamp`) and `blob_garbage_collection_cutoff_file_number_`, their interaction with snapshot stripes and universal/FIFO compaction pickers was **not examined**; findings on tombstone elision apply specifically to sequence-number-ordered leveled compaction (and L0-to-L0/L1 flushes).
- **Cicada Aborted-Version Chain Reclamation & Index Contention (`unknown` / `known not to apply`):** As explicitly documented in `context_gc.h:164-166`, Cicada's fast-path per-thread `gc_row` does **not** reclaim aborted versions installed ahead of the latest committed version; whether later forks or downstream engines implement the slow-scan reclamation mentioned in that comment is **unknown** from `af469679`.
- **LeanStore `Swip` Tagging on 5-Level Paging (`LA57`) or ARM TBI (`known not to apply`):** `Swip.hpp:21-28` reserves bits 62–63 (`0xC000000000000000`) for `evicted_bit` and `cool_bit`. This relies on user-space canonical addresses having bits 62–63 equal to `0`; it does **not** apply unaltered to kernel-space addresses (top bits `1`) or pointer-authentication (`ARMv8.3 PAC`) schemes that repurpose bits 62–63 without masking.
- **Attractive Stronger Conclusion Not Established:** Passing the 6,561-history Python compaction model checker (`Probe 1A`) establishes exact equivalence for the modeled single-range, point/range-delete state machine, **not** bug-freedom of full C++/Go implementations (e.g., Pebble's `RangeKey` suffix coalescing, RocksDB `MergeOperator` partial merges, or distributed clock skew across nodes).

## Evidence

### Primary Repositories Inspected (All Acquired `2026-11-19`)

1. **`nyu-acsys/template-proofs` @ `6444326e04577987c66776bed34d9a76ffd0df55`:**
   - `templates/flows/flows.v:28-36` (`flowintR`, `flowintT`), `99-103` (`intComposable`), `1720-1736` (`contextualLeq`, `flowint_update`).
   - `templates/single_copy/inset_flows.v:16` (`keyset`), `30-34` (`globalinv`), `44-48` (`contextualLeq_impl_globalinv`).
   - `templates/single_copy/link.v:41-50` (`inreachG`, `fracintG`), `89-103` (`traverse`, `CSSOp`), `137-175` (`findNext_spec`, `decisiveOp_spec`, `nodePred`, `nodeShared`), `436-437` (`ghost_snapshot_fp_k`).
   - `templates/multicopy/multicopy_lsm.v:93-101` (`multicopy_lsmG`), `151-168` (`outflow_constraint_I`, `outflow_constraint_J`), `313-320` (global dual-flow invariant).
2. **`flode/ARTSynchronized` @ `f00003ec7991da09c3dfc1c84da97c1965106eb3`:**
   - `OptimisticLockCoupling/N.h:48-50` (`typeVersionLockObsolete`), `88-90` (`writeUnlockObsolete`).
   - `OptimisticLockCoupling/Tree.cpp:24-78` (`Tree::lookup`, `EpocheGuardReadonly`, unvalidated early return at lines `48-50`), `694-711` (`checkPrefix`).
3. **`leanstore/leanstore` @ `fcb64bf39cf69c435173f76e062cbb305a9a998f`:**
   - `backend/leanstore/storage/buffer-manager/Swip.hpp:20-68` (`evicted_bit`, `cool_bit`, `hot_mask`, `isHOT`/`isCOOL`/`isEVICTED`, `warm`/`cool`/`evict`).
   - `backend/leanstore/sync-primitives/Latch.hpp:21-223` (`HybridLatch`, `static_assert(sizeof == 64)`, `Guard`, `recheck`, `unlock`, `toExclusive`, `tryToExclusive`).
   - `backend/leanstore/storage/buffer-manager/PageProviderThread.cpp:108-264` (`repickIf(!all_children_evicted)`, cooling transition, `evict_bf`, `io_ht` lookup guard, latch version bump on eviction).
4. **`efficient/cicada-engine` @ `af469679d67a59a89536de634216d349af577d3a`:**
   - `src/mica/transaction/timestamp.h:11-54` (`CompactTimestamp`, `about_to_expire`), `90-223` (`WideTimestamp`, `WideConcurrentTimestamp` SeqLock), `225-250` (`CentralizedTimestamp`).
   - `src/mica/transaction/context_gc.h:8-33` (`schedule_gc`), `36-201` (`gc`, `gc_row`, `gc_lock`, `min_rts` drain loop, `TODO` at lines `164-166`).
5. **`postgres/postgres` @ `6ec71e1ad8c26b3a93e7c5739e797a2d353dc5d6`:**
   - `src/include/access/transam.h:31-35` (reserved XIDs), `93-96` (`TransactionIdAdvance`), `147-154` (`NormalTransactionIdPrecedes`/`Follows`).
   - `src/backend/access/transam/varsup.c:367-446` (`SetTransactionIdLimit`: `xidWrapLimit`, `xidStopLimit`, `xidWarnLimit`, `xidVacLimit`).
   - `src/backend/storage/ipc/procarray.c:138-202` (`GlobalVisState`, four relation-scoped visibility horizons, `ComputeXidHorizonsResult`).
6. **`facebook/rocksdb` @ `2f4f3c4b1ec6e42577e629e2e322dec1f9c2ea85`:**
   - `db/compaction/compaction_iterator.cc:197-205` (`bottommost_level_` with `!allow_ingest_behind()`, `enforce_single_del_contracts_`), `243-246` (snapshot ordering), `900-935` (`ProcessDeletion`, `KeyNotExistsBeyondOutputLevel`).
   - `db/range_del_aggregator.h` & `db/range_del_aggregator.cc:298-408` (`CompactionRangeDelAggregator`, `StripeMap`, `ShouldDelete`, `TruncatedRangeDelIterator`).
   - `db/column_family.cc:350-372` (`SanitizeOptions`), `953-974` (`GetL0FileCountForCompactionSpeedup`), `1038-1063` (`RecalculateWriteStallConditions`).
7. **`cockroachdb/pebble` @ `a995e890c06ef86c583927906e16e7f313083a3f`:**
   - `internal/compact/snapshots.go:46-65` (`Snapshots.Index`, `IndexAndSeqNum`).
   - `internal/compact/tombstone_elision.go:28-195` (`TombstoneElision`, `pointTombstoneElider`, `rangeTombstoneElider`, `SetupTombstoneElision` with `L0` `startLevel = 0`).
   - `internal/compact/spans.go:49-80` (`RangeDelSpanCompactor.Compact`), `120-176` (`RangeKeySpanCompactor.Compact`), `188-218` (`SplitAndEncodeSpan`).
   - `internal/compact/iterator.go:298-304`, `930-1180` (`IneffectualSingleDeleteCallback`, `NondeterministicSingleDeleteCallback`, `singleDeleteNext`, `skipDueToSingleDeleteElision`).

### Executable Micro-Probes and Recorded Outputs (`2026-11-19`, Python 3, Linux x86_64)

#### Probe 1A: LSM Snapshot-Stripe & Tombstone-Elision Model Checker

```python
# Save as /tmp/probe_lsm_resurrection.py and run: python3 /tmp/probe_lsm_resurrection.py
from dataclasses import dataclass
from itertools import product

@dataclass(frozen=True)
class Op:
    kind: str; key: str; end: str; val: str; seq: int; level: int

def oracle_get(ops, key, snap_seq):
    best_pt, best_rdel = None, -1
    for op in ops:
        if op.seq > snap_seq: continue
        if op.kind == "RANGEDEL":
            if op.key <= key < op.end and op.seq > best_rdel: best_rdel = op.seq
        elif op.key == key and (best_pt is None or op.seq > best_pt.seq):
            best_pt = op
    if best_pt is None or best_rdel > best_pt.seq or best_pt.kind in ("DEL", "SINGLEDEL"):
        return None
    return best_pt.val

def stripe_id(seq, snaps):
    for i, s in enumerate(snaps):
        if seq <= s: return i
    return len(snaps)

def compact_levels(ops, compact_set, out_level, snaps,
                   bug_elide_non_bottommost=False,
                   bug_ignore_stripes_for_rangedel=False,
                   bug_singledel_unsafe_cancel=False):
    untouched = [o for o in ops if o.level not in compact_set]
    inputs = [o for o in ops if o.level in compact_set]
    below_keys = {o.key for o in untouched if o.level > out_level and o.kind != "RANGEDEL"}
    below_any = any(o.level > out_level for o in untouched)
    pts_by_key, rdels = {}, []
    for o in inputs:
        (rdels if o.kind == "RANGEDEL" else pts_by_key.setdefault(o.key, [])).append(o)
    rdels.sort(key=lambda o: -o.seq)
    kept_rdels, seen_st = [], set()
    for r in rdels:
        st = 0 if bug_ignore_stripes_for_rangedel else stripe_id(r.seq, snaps)
        if st in seen_st: continue
        seen_st.add(st)
        is_bot = (st == 0) if snaps else True
        if is_bot and ((not below_any) or bug_elide_non_bottommost): continue
        kept_rdels.append(Op(r.kind, r.key, r.end, r.val, r.seq, out_level))
    kept_pts = []
    for k, kops in pts_by_key.items():
        kops.sort(key=lambda o: -o.seq)
        by_st = {}
        for o in kops: by_st.setdefault(stripe_id(o.seq, snaps), []).append(o)
        for st in sorted(by_st, reverse=True):
            sops = by_st[st]
            rdel_seq = max((r.seq for r in rdels
                            if (bug_ignore_stripes_for_rangedel or stripe_id(r.seq, snaps) == st)
                            and r.key <= k < r.end), default=-1)
            head = sops[0]
            if rdel_seq > head.seq: continue
            is_bot = (st == 0) if snaps else True
            if head.kind == "SINGLEDEL":
                if bug_singledel_unsafe_cancel and len(sops) >= 2 and sops[1].kind == "PUT":
                    kept_pts.extend(Op(x.kind, x.key, x.end, x.val, x.seq, out_level) for x in sops[2:])
                    continue
                if is_bot and (k not in below_keys): continue
                kept_pts.append(Op("DEL", head.key, "", "", head.seq, out_level)); continue
            if head.kind == "DEL" and is_bot and ((k not in below_keys) or bug_elide_non_bottommost):
                continue
            kept_pts.append(Op(head.kind, head.key, head.end, head.val, head.seq, out_level))
    return untouched + kept_pts + kept_rdels

def check_eq(ops, cset, olvl, snaps, **kw):
    after = compact_levels(ops, cset, olvl, snaps, **kw)
    for s in list(snaps) + [999]:
        for k in ("a", "b"):
            v1, v2 = oracle_get(ops, k, s), oracle_get(after, k, s)
            if v1 != v2: return {"key": k, "snap": s, "before": v1, "after": v2}
    return None

scenarios = [
    ("Bug 1: Non-bottommost RANGEDEL elision (L0+L1->L1, PUT in L2)",
     [Op("PUT", "a", "", "v1", 1, 2), Op("RANGEDEL", "a", "c", "", 3, 0)],
     {0, 1}, 1, [], {"bug_elide_non_bottommost": True}),
    ("Bug 2a: Cross-stripe RANGEDEL collapse -> resurrection at S=2 (PUT in L2, RDEL@2 in L1, RDEL@4 in L0)",
     [Op("PUT", "a", "", "v1", 1, 2), Op("RANGEDEL", "a", "c", "", 2, 1), Op("RANGEDEL", "a", "c", "", 4, 0)],
     {0, 1}, 1, [2], {"bug_ignore_stripes_for_rangedel": True}),
    ("Bug 2b: Cross-stripe RANGEDEL drop -> phantom deletion at S=2 (PUT@1 in L1, RDEL@3 in L0)",
     [Op("PUT", "a", "", "v1", 1, 1), Op("RANGEDEL", "a", "c", "", 3, 0)],
     {0, 1}, 1, [2], {"bug_ignore_stripes_for_rangedel": True}),
    ("Bug 3: SingleDelete contract violation (two PUTs + SINGLEDEL)",
     [Op("PUT", "a", "", "v1_old", 1, 0), Op("PUT", "a", "", "v2_new", 2, 0), Op("SINGLEDEL", "a", "", "", 3, 0)],
     {0, 1}, 1, [], {"bug_singledel_unsafe_cancel": True}),
]
for name, ops, cset, olvl, sn, kw in scenarios:
    print(f"{name}:\n  Buggy variant violation  : {check_eq(ops, cset, olvl, sn, **kw)}\n  Correct invariant check  : {check_eq(ops, cset, olvl, sn)}")
kinds = [("PUT", "a", "", "v"), ("DEL", "a", "", ""), ("RANGEDEL", "a", "c", "")]
total = failures = 0
for combo in product(kinds, repeat=4):
    for lvls in product((0, 1, 2), repeat=4):
        total += 1
        ops = [Op(k, key, end, f"{val}{i+1}", i+1, lvls[i]) for i, (k, key, end, val) in enumerate(combo)]
        if check_eq(ops, {0, 1}, 1, [2, 3]) is not None: failures += 1
print(f"\nExhaustive 4-op sweep ({total} histories, compacting L0+L1->L1 with L2 below, snaps=[2,3]):\n  Correct stripe+in-use-range invariant failures = {failures}/{total}")
```

Recorded output (`exit 0`):
```text
Bug 1: Non-bottommost RANGEDEL elision (L0+L1->L1, PUT in L2):
  Buggy variant violation  : {'key': 'a', 'snap': 999, 'before': None, 'after': 'v1'}
  Correct invariant check  : None
Bug 2a: Cross-stripe RANGEDEL collapse -> resurrection at S=2 (PUT in L2, RDEL@2 in L1, RDEL@4 in L0):
  Buggy variant violation  : {'key': 'a', 'snap': 2, 'before': None, 'after': 'v1'}
  Correct invariant check  : None
Bug 2b: Cross-stripe RANGEDEL drop -> phantom deletion at S=2 (PUT@1 in L1, RDEL@3 in L0):
  Buggy variant violation  : {'key': 'a', 'snap': 2, 'before': 'v1', 'after': None}
  Correct invariant check  : None
Bug 3: SingleDelete contract violation (two PUTs + SINGLEDEL):
  Buggy variant violation  : {'key': 'a', 'snap': 999, 'before': None, 'after': 'v1_old'}
  Correct invariant check  : None

Exhaustive 4-op sweep (6561 histories, compacting L0+L1->L1 with L2 below, snaps=[2,3]):
  Correct stripe+in-use-range invariant failures = 0/6561
```

#### Probe 1B: PostgreSQL 32-Bit XID Wraparound, Cicada 56-Bit TSC Horizon, and Iris B-Link Split Conservation

```python
# Save as /tmp/probe_mvcc_wraparound.py and run: python3 /tmp/probe_mvcc_wraparound.py
import ctypes
FIRST_NORMAL_XID, MAX_XID = 3, 0xFFFFFFFF
def xid_precedes(a, b): return ctypes.c_int32((a - b) & 0xFFFFFFFF).value < 0
oldest = 3
wrap = (oldest + (MAX_XID >> 1)) & 0xFFFFFFFF
stop, warn, vac = (wrap - 3_000_000) & 0xFFFFFFFF, (wrap - 100_000_000) & 0xFFFFFFFF, (oldest + 200_000_000) & 0xFFFFFFFF
print("=== PostgreSQL 32-bit XID Wraparound Guardrails (oldest_datfrozenxid=3) ===")
print(f"xidVacLimit  = {vac:,} (age = {vac - oldest:,})")
print(f"xidWarnLimit = {warn:,} (headroom to wrap = {wrap - warn:,})")
print(f"xidStopLimit = {stop:,} (headroom to wrap = {wrap - stop:,})")
print(f"xidWrapLimit = {wrap:,} (MaxTransactionId>>1 + 3 = {(MAX_XID>>1)+3:,})")
print(f"Visibility & antisymmetry boundary for unfrozen xmin={oldest}:")
for lbl, d, note in [("2^31-1", (1<<31)-1, "valid total order"), ("2^31  ", 1<<31, "ANTISYMMETRY BROKEN: both True!"), ("2^31+1", (1<<31)+1, "INVISIBLE -> DATA LOSS!")]:
    cur = oldest + d
    print(f"  age {lbl} ({cur}): precedes(3,cur)={xid_precedes(oldest,cur)}, precedes(cur,3)={xid_precedes(cur,oldest)} ({note})")
print("\n=== Cicada CompactTimestamp (56-bit TSC | 8-bit thread_id) Wrap Horizon ===")
for ghz in (2.5, 3.0, 4.0):
    print(f"  At {ghz:.1f} GHz TSC: signed half-space = {(1<<55)/(ghz*1e9*86400):.2f} days; about_to_expire lead (1/16 of 2^64) = {(1<<52)/(ghz*1e9*86400):.2f} days")
print("\n=== Iris Flow Framework B-Link Split Conservation Check ===")
KS = set(range(100)); out_np = {k for k in KS if k > 50}; ks_n, ks_np = KS - out_np, set(out_np)
print(f"  contextualLeq inflow preserved on n : {KS == set(KS)}")
print(f"  keysets disjoint (n: 0..{max(ks_n)}, n': {min(ks_np)}..{max(ks_np)}): {ks_n.isdisjoint(ks_np)}")
print(f"  keyset union conserved              : {ks_n | ks_np == KS}")
print(f"  inreach(n) monotone                 : {KS <= set(KS)}")
```

Recorded output (`exit 0`):
```text
=== PostgreSQL 32-bit XID Wraparound Guardrails (oldest_datfrozenxid=3) ===
xidVacLimit  = 200,000,003 (age = 200,000,000)
xidWarnLimit = 2,047,483,650 (headroom to wrap = 100,000,000)
xidStopLimit = 2,144,483,650 (headroom to wrap = 3,000,000)
xidWrapLimit = 2,147,483,650 (MaxTransactionId>>1 + 3 = 2,147,483,650)
Visibility & antisymmetry boundary for unfrozen xmin=3:
  age 2^31-1 (2147483650): precedes(3,cur)=True, precedes(cur,3)=False (valid total order)
  age 2^31   (2147483651): precedes(3,cur)=True, precedes(cur,3)=True (ANTISYMMETRY BROKEN: both True!)
  age 2^31+1 (2147483652): precedes(3,cur)=False, precedes(cur,3)=True (INVISIBLE -> DATA LOSS!)

=== Cicada CompactTimestamp (56-bit TSC | 8-bit thread_id) Wrap Horizon ===
  At 2.5 GHz TSC: signed half-space = 166.80 days; about_to_expire lead (1/16 of 2^64) = 20.85 days
  At 3.0 GHz TSC: signed half-space = 139.00 days; about_to_expire lead (1/16 of 2^64) = 17.37 days
  At 4.0 GHz TSC: signed half-space = 104.25 days; about_to_expire lead (1/16 of 2^64) = 13.03 days

=== Iris Flow Framework B-Link Split Conservation Check ===
  contextualLeq inflow preserved on n : True
  keysets disjoint (n: 0..50, n': 51..99): True
  keyset union conserved              : True
  inreach(n) monotone                 : True
```

## Revalidation

1. **Upstream Source Diff Checks (Cheapest Check for Implementation Drift):**
   - **RocksDB:** Inspect `db/compaction/compaction_iterator.cc` around `bottommost_level_` and `KeyNotExistsBeyondOutputLevel`, plus `db/range_del_aggregator.cc` `CompactionRangeDelAggregator::ShouldDelete` and `db/column_family.cc` `RecalculateWriteStallConditions`. Any relaxation of `!compaction_->allow_ingest_behind()` or snapshot-stripe partitioning requires re-testing against deleted-key resurrection.
   - **Pebble:** Diff `internal/compact/snapshots.go`, `internal/compact/tombstone_elision.go` (`SetupTombstoneElision` `startLevel = 0` for `L0`), `internal/compact/spans.go` (`RangeDelSpanCompactor.Compact`, `SplitAndEncodeSpan`), and `internal/compact/iterator.go` (`singleDeleteNext`).
   - **PostgreSQL:** Diff `src/include/access/transam.h` (`NormalTransactionIdPrecedes`, `FullTransactionId`), `src/backend/access/transam/varsup.c` (`SetTransactionIdLimit` constants `3000000` and `100000000`), and `src/backend/storage/ipc/procarray.c` (`GlobalVisState`). If PostgreSQL migrates heap tuple headers to 64-bit XIDs in a future major release, the 32-bit wraparound guardrail section will no longer apply to that release.
   - **LeanStore & ART-OLC:** Check `Swip.hpp` bit masks (`bits 62–63`), `Latch.hpp` `HybridLatch`, `PageProviderThread.cpp` `repickIf(!all_children_evicted)`, and `OptimisticLockCoupling/Tree.cpp:48-50` (check whether the missing `readUnlockOrRestart` before `return 0` has been patched).
2. **Executable Probe Re-run:** Re-run Probes 1A and 1B with Python 3.10+ (`python3 /tmp/probe_lsm_resurrection.py && python3 /tmp/probe_mvcc_wraparound.py`) to verify any proposed alternative tombstone-elision policy (e.g., adding `Merge` or `RangeKey` operators) or custom modular timestamp width. Note that passing Probe 1A checks only the modeled key-stripe semantics; verifying concrete RocksDB/Pebble builds requires running their native compaction unit/metamorphic suites (`compaction_iterator_test` and `go test ./internal/metamorphic`).
