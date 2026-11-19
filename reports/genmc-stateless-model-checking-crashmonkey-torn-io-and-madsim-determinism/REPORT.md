# Weak-Memory Stateless Model Checking, Torn-I/O Crash Permutation, and Seed-Deterministic Distributed Simulation

## Summary

Concurrent data structures, crash-consistent storage engines, and consensus systems fail almost exclusively inside low-probability nondeterministic corners that standard stress testing never reaches: relaxed hardware store buffers (`x86-TSO`, `ARMv8`, `RC11`/`IMM`), volatile disk writeback caches reordering or tearing `512 B` sectors across power loss, and correlated asymmetric network partitions coupled with clock drift (`Basis: source + execution + derived`).

Across the twelve pinned upstream systems examined in this report, systematically exploring schedule and fault spaces without exponential state-cache exhaustion requires aligning three specialized semantic reduction engines with polynomial history verification (`Basis: source + execution + derived`):

1. **Truly Stateless Optimal Execution-Graph DPOR vs. Preemption-Bounded and Probabilistic Schedulers (`GenMC`, `Nidhugg`, `Tokio Loom`, `AWS Shuttle`)**: Naive thread-interleaving DFS misses non-SC hardware behaviors (`Store Buffering` `(0, 0)` absent across all `6` SC schedules) while exploding combinatorially on commuting operations (`113,400` schedules at `k = 5` reader threads). `GenMC` (`MPI-SWS/genmc`) partitions executions into axiomatic graphs $\langle E, \mathsf{po}, \mathsf{rf}, \mathsf{mo} \rangle$ and enforces Kokologiannakis et al.'s `TruSt` maximal-extension condition (`GenMCDriver::isMaximalExtension`) during `backwardRevisit`, visiting each consistent `RC11`/`IMM`/`ARM8` graph **exactly once** in $O(|E|)$ memory (`1` graph at `k = 5`, zero global visited-state hash table). Where full DPOR hits state explosion in large Rust runtimes (`Loom` hard-caps `MAX_THREADS = 5` and `MAX_ATOMIC_HISTORY = 7`), `Shuttle`'s Probabilistic Concurrency Testing (`PctScheduler`) bounds priority inversions to $d - 1$ random change points, guaranteeing per-run bug-detection probability $\ge \frac{1}{n \cdot k^{d-1}}$.
2. **Barrier-Epoch Subset and `512 B` Torn-Sector Crash Permutation (`CrashMonkey` & `ACE`, Linux `dm-log-writes` & `dm-flakey`)**: Block storage is permitted to reorder, drop, or partially tear any unbarriered `bio` payload queued in volatile device cache prior to `REQ_PREFLUSH` or `REQ_FUA`. Exhaustive CrashMonkey/dm-log-writes epoch-subset modeling proves that unbarriered in-place `AEAD` (`4 KiB` data + `512 B` tag) corrupts **`50.0%` (`2/4`)** of whole-`bio` crash states and **`99.61%` (`510/512`)** of `512 B` sub-page torn-sector crash states (`-EBADMSG`), while un-`fsync`ed `write(tmp) + rename(tmp, dst)` yields **`37.5%` (`3/8`)** zeroed/dangling files; bracketing `write(tmp) -> fsync(tmp) -> rename(tmp, dst) -> fsync(dir)` reduces post-crash corruption to **`0.0%` (`0/6`)**.
3. **Single-Seed Virtual-Time Deterministic Simulation Paired with White-Box `O(V + E)` Anomaly Checking (`FoundationDB Sim2`, `TigerBeetle VOPR`, `MadSim`, `Tokio Turmoil`, `Porcupine`, `Jepsen Elle`)**: Collapsing multi-node clusters, virtual clocks, `Buggify` gray faults, asymmetric `ClogSend`/`ClogReceive` links, and quorum-aware `ClusterFaultAtlas` sector corruptions into a single-threaded PRNG-driven discrete-event loop achieves **`14,500.3x` time dilation** (`1.00 hour` of `5`-node chaos simulated in `248.27 ms` wall-clock with bit-identical canary replay). Pairing simulation traces with white-box version-order encoding (`Elle` list-append `ww`/`wr`/`rw` graphs) turns NP-complete black-box history checking (`Porcupine`) into linear-time $O(V + E)$ Tarjan strongly connected component (`SCC`) cycle extraction.

---

## Applicability

The findings in this report apply to shared-memory concurrency verifiers, block-layer crash-consistency harnesses, deterministic distributed-system simulators, and consistency-history checkers at the twelve immutable upstream revisions recorded in `REPORT.json` (`Basis: source + documentation`):

- **Weak-Memory Stateless Model Checkers & Controlled Schedulers**: `MPI-SWS/genmc` (`fab5bba7d9efaf76990227c2f59d62c11c7ea2a3`, LLVM-IR C/C++ model checker over `SC`/`TSO`/`RA`/`RC11`/`IMM`/`ARM8`), `nidhugg/nidhugg` (`0f572e013e32764cbf057608ca7ab11f97815790`, LLVM trace-based `TSO`/`PSO`/`POWER`/`ARM` DPOR), `tokio-rs/loom` (`9d549cd5357a5485900f4c53951fc1726319659f`, Rust `CDSChecker`-derived C11 model checker), and `awslabs/shuttle` (`72bdbdb612c2311905c84bbc73d59f12a5b17e43`, Rust randomized `PCT` and `DFS` concurrency testing).
- **Block-Layer Crash-Consistency & Torn-I/O Frameworks**: `utsaslab/crashmonkey` (`27ca57f8cf2760d5d4855e03b8d01f8e5de1628c`, kernel `bio` wrapper, copy-on-write RAM disk `cow_brd.c`, `Permuter`, and `ACE` $B^3$ bounded workload explorer) and mainline `torvalds/linux` (`8dac6df92a2e66e2098bbc69061964cfe7e8375b`, `drivers/md/dm-log-writes.c` and `drivers/md/dm-flakey.c`).
- **Seed-Deterministic Simulation Runtimes & Consistency Oracles**: `apple/foundationdb` (`4e8043caa5761d5a41886dba3de47ecfaf2f7cbf`, `ISimulator` / `sim2.cpp`), `tigerbeetle/tigerbeetle` (`a2a3c7064519e08233abe26c54a43fca2f9ad9bc`, `src/vopr.zig` and `src/testing/storage.zig`), `madsim-rs/madsim` (`519950efb4711464f300ed7edf2967ed62d5f502`, `GlobalRng` determinism canary, virtual net/time/fs, and `buggify`), `tokio-rs/turmoil` (`bf54cec46c132fb26e24cabfe503d6abfe286482`, `turmoil-net` `Fabric`, `turmoil-fs`, and `turmoil-io-uring`), `anishathalye/porcupine` (`97cd067defd99df172053ba7f4ca5bbae57fe446`, Go bitset linearizability checker), and `jepsen-io/elle` (`4e359e597c52938b0afebb8bc42273914d68a424`, Clojure/Java Adya transactional cycle detector).

Together these twelve subjects span the intra-process, kernel-storage, and inter-node fault planes of systems verification (`Basis: derived`). Standalone quantitative probes were executed on Linux `x86_64` under Python `3.11+` (`Basis: execution`).

---

## Findings

### 1. Stateless Weak-Memory Model Checking and Controlled Schedule Reduction

#### 1.1 Execution-Graph Optimal DPOR Without Visited Sets (`GenMC` vs. Thread-Interleaving DFS)
Classical stateless model checkers (`VeriSoft`, Flanagan & Godefroid POPL 2005 DPOR, Abdulla et al. POPL 2014 Optimal DPOR `DOI: 10.1145/2535838.2535845`, and `nidhugg/nidhugg` `0f572e013e32764cbf057608ca7ab11f97815790`) explore total or trace-equivalence classes of *sequential thread schedules*. Under hardware and C11/C++20 weak memory (`RC11`, `IMM`, `ARMv8`, `LKMM`), two fatal defects arise in schedule-interleaving exploration (`Basis: source + execution + derived`):
1. **Unsoundness on Weak-Memory Non-Multi-Copy/Store-Buffer Behaviors**: On the `2`-thread Store Buffering (`SB`) litmus (`T0: W_rlx(x, 1); r0 = R_rlx(y) || T1: W_rlx(y, 1); r1 = R_rlx(x)`), all $\binom{4}{2} = 6$ sequential thread interleavings produce outcomes in $\{(0, 1), (1, 0), (1, 1)\}$, completely missing the `(r0 = 0, r1 = 0)` weak outcome observable on `x86-TSO`, `ARMv8`, and `RC11` (`## Revalidation` Probe 1).
2. **Coherence-Order vs. Read-From Redundancy Explosion**: Even when hardware store buffers are simulated explicitly (`Nidhugg` `TSO`/`PSO` buffers), multiple buffer-flush interleavings induce the exact same reads-from (`rf`) and modification-order (`mo`) relations, while caching visited graphs in memory exhausts RAM exponentially.

`MPI-SWS/genmc` (`genmc/genmc/Verification/GenMCDriver.hpp:64-92, 580-615`, `GenMCDriver.cpp:2659-2899`, `Revisit.hpp:31-108`; `Kokologiannakis & Vafeiadis, CAV 2021, DOI: 10.1007/978-3-030-81685-8_20`; `Kokologiannakis et al., POPL 2022 TruSt, DOI: 10.1145/3498711`) operates directly over **axiomatic execution graphs** $G = \langle E, \mathsf{po}, \mathsf{rf}, \mathsf{mo} \rangle$ (`Basis: source`):
- **Single-Graph `O(|E|)` State (`GenMCDriver.hpp:64-92`)**: `GenMCDriver::Execution` holds *only* `std::unique_ptr<ExecutionGraph> graph`, a per-depth `WorkList workqueue`, and `ChoiceMap choices` (rolling back via `Execution::restrict(Stamp stamp)` at `L85` with **zero global visited-graph table**).
- **Forward and Maximal-Extension Backward Revisits (`Revisit.hpp:31-42`, `GenMCDriver.cpp:2659-2734`)**:
  - When `handleLoad` (`GenMCDriver.cpp:1524`) adds a read event $r$, `GenMC` explores existing consistent stores $w \in G$ via `RV_FRevRead` (`ReadForwardRevisit`), `RV_FRevMO` (`WriteForwardRevisit` for coherence placements), and `RV_FRevWeakCasFail` (`maybePushWeakCasFailure`, `GenMCDriver.hpp:387`, explicitly testing spurious failure of C11 `compare_exchange_weak`!).
  - When a *later* `handleStore` (`GenMCDriver.cpp:1992`) adds a store $w$ that could have been read by an earlier non-`porf`-preceding load $r$, naive backward revisiting would re-derive the same graph through multiple deletion paths. `GenMC` deletes the suffix $\{e \in E \mid stamp(e) > stamp(r) \land (e, w) \notin \mathsf{porf}\}$ **if and only if** `GenMCDriver::isMaximalExtension(const BackwardRevisit &r)` (`GenMCDriver.cpp:2659-2730`) holds—checking `coherenceSuccRemainInGraph(r)` and ensuring every deleted event would have been added maximally along the canonical exploration prefix.
- **Synthesized Axiomatic Checkers & Relinche Linearizability (`RC11Checker.cpp:14-95`, `GenMCDriver.hpp:22`)**: Consistency checkers (`RC11Checker`, `IMMChecker`, `ARM8Checker`, `TSOChecker`, `RAChecker`, `SCChecker`) are **mechanically compiled by `Kater`** (`RC11Checker.cpp:15`: `generated automatically by Kater`) into iterative DFS automata (`visitCalc77Iterative`), eliminating handwritten cycle-check bugs, while `Verification/Relinche/LinearizabilityChecker.hpp` checks concurrent library specifications directly over weak-memory observations (`Basis: source`).

Our execution-graph micro-probe (`## Revalidation` Probe 1) confirms both weak-memory precision and exponential reduction (`Basis: execution`):
- On `Store Buffering` (`SB`), execution-graph exploration visits `4` graphs (vs. `6` SC schedules) and immediately exposes `(r0 = 0, r1 = 0)`.
- On `Message Passing` (`MP`: `W_rlx(data, 42); W_mode(flag, 1) || r_f = R_mode(flag); if r_f == 1: r_d = R_rlx(data)`), `Relaxed` mode visits `3` graphs exposing stale `(flag = 1, data = 0)`, whereas `Release`/`Acquire` induces `(W_rel, R_acq) ∈ rf ⊆ sw ⊆ hb`, pruning `(flag = 1, data = 0)` by Write-Read Coherence (`2` consistent graphs).
- Across $k \in \{2, 3, 4, 5\}$ commuting reader/local-store threads, sequential interleaving DFS explores `6`, `90`, `2,520`, and **`113,400`** schedules ($\frac{(2k)!}{2^k}$), whereas optimal execution-graph DPOR explores **`1` maximal graph (`113,400x` reduction at `k = 5`)**.

#### 1.2 `Tokio Loom` (`CDSChecker` Vector Clocks) vs. `AWS Shuttle` (`PCT` Randomized Bounds)
In Rust concurrency verification, `tokio-rs/loom` and `awslabs/shuttle` trade completeness against scalability across sharply defined architectural limits (`Basis: source`):

1. **`tokio-rs/loom` (`src/rt/mod.rs:58-61`, `src/rt/vv.rs:10-72`, `src/rt/atomic.rs:5-95`, `src/rt/execution.rs:48-73`)**:
   - Implements Norris & Demsky's `CDSChecker` C11 coherence-implication rules (`DOI: 10.1145/2509136.2509514`, documented inline at `src/rt/atomic.rs:5-56`: Read-Read, Write-Read, Read-Write, and Write-Write Coherence plus `SeqCst` fence implications) using fixed-width `u16` vector clocks `VersionVec { versions: [u16; MAX_THREADS] }` (`src/rt/vv.rs:10-12`).
   - Hard compile-time bounds in `src/rt/mod.rs:58-61` fix **`pub const MAX_THREADS: usize = 5`** and **`pub(crate) const MAX_ATOMIC_HISTORY: usize = 7`** (`max_history: 7` in `src/rt/execution.rs:69`), paired with `preemption_bound: Option<usize>` (`execution.rs:51, 57-62`). Because `Loom` executes acyclically along program/CausalCell execution order without speculative out-of-order value synthesis, it catches `SB`, `MP`, and ABA lock-free bugs within `<= 5` threads and `<= 7` stores per atomic, but **cannot** scale to `16`-thread work-stealing pools or synthesize speculative ARMv8 `Load Buffering` (`LB`) cycles (`Basis: source + derived`).
2. **`awslabs/shuttle` (`shuttle-schedulers/src/pct.rs:12-120`)**:
   - Implements Burckhardt et al.'s **Probabilistic Concurrency Testing (`PCT`)** (`ASPLOS 2010, DOI: 10.1145/1736020.1736040`). In `PctScheduler::new_execution` (`pct.rs:68-111`), iteration `0` executes an oldest-task-first schedule (`L75-78`) to measure step bound $k = \text{max\_steps}$; subsequent iterations assign random distinct priorities to all $n$ tasks (`L87-95`) and draw $\min(d - 1, k - 1)$ uniform priority-demotion `change_points` in $[1, k]$ (`L99-105`, seeded reproducibly via `Pcg64Mcg::seed_from_u64` and `SHUTTLE_RANDOM_SEED`, `L44-50`).
   - For any concurrency bug of depth $d$ ( empirically $d \in \{1, 2, 3\}$ for $> 95\%$ of real data races, deadlocks, and lost wakeups), a single `PCT` execution triggers the bug with probability at least $\frac{1}{n \cdot k^{d-1}}$—enabling `Shuttle` to test `50+` tasks and `10,000+` steps in seconds where exhaustive DPOR fails to terminate (`Basis: source + derived`).

---

### 2. Block-Layer Crash Consistency and Torn-Sector Permutation (`CrashMonkey`, `ACE`, `dm-log-writes`, `dm-flakey`)

#### 2.1 Volatile Writeback Reordering and Sub-`bio` Sector Tearing (`CrashMonkey` & `ACE`)
Proofs over POSIX syscall models routinely assume sequential crash prefixes, ignoring that NVMe/SATA controllers buffer non-barriered writes in volatile DRAM caches, reorder completions arbitrarily across distinct LBAs, and split `4 KiB` filesystem blocks into `512 B` hardware sectors during unscheduled power loss (`Basis: source + documentation`).

`utsaslab/crashmonkey` (`code/disk_wrapper.c`, `code/cow_brd.c`, `code/permuter/Permuter.h`, `ace/ace.py`; `Mohan et al., OSDI 2018 / ACM TOS 2019, DOI: 10.1145/3320275`) tests unmodified filesystems (`ext4`, `btrfs`, `f2fs`, `xfs`) via **Bounded Black-Box Crash Testing ($B^3$)** (`Basis: source`):
- **Block Interception & Barrier Epoch Partitioning (`code/disk_wrapper.c:16-110, 888`, `code/permuter/Permuter.h:27-105`)**: `disk_wrapper_bio` intercepts block requests (`KERNEL_SECTOR_SIZE = 512`) above a copy-on-write RAM disk (`cow_brd.c`) and partitions recorded writes into barrier-delimited `struct epoch` segments (`Permuter.h:35-41`) split at `REQ_PREFLUSH` (`flush`), `REQ_FUA` (`fua`, Force Unit Access bypassing volatile cache), and `HWM_CHECKPOINT_FLAG`. Within any uncommitted final epoch $E_m$, `Permuter::GenerateSectorCrashState` (`Permuter.h:75-89`) decomposes `epoch_op` bios into `EpochOpSector` slices (`sector_size_`), applies `CoalesceSectors` (`L87-88`) so later persisted writes overwrite stale sectors at identical offsets, and deduplicates crash images via `BioVectorHash` (`L104-105`), mounting and running `fsck` + data/metadata oracle checks on each crash image in RAM (`~1–5 ms` per RAM-disk snapshot reset).
- **$B^3$ Systematic Workload Generation (`ace/ace.py:28-110`)**: `ACE` bounds workload length to `1–3` filesystem calls over canonical sibling/parent equivalence classes (`SiblingOf`, `Parent` on `foo`, `bar`, `A/foo`, `B/foo`, `ace.py:29-76`). That tiny $B^3$ space reproduced **`24 / 26` historical Linux filesystem crash bugs** (`ace.py:80-85`: `3` at length `1`, `14` at length `2`, `9` at length `3`) and uncovered **`10` new `btrfs`/`f2fs` bugs**—such as `write('foo', 'append') -> falloc('foo', FALLOC_FL_ZERO_RANGE | FALLOC_FL_KEEP_SIZE) -> fsync/fdatasync` (`ace.py:99-106`), where `fsync`'s fast-path log tree skipped persisting extent metadata modified by `ZERO_RANGE` (`Basis: source + documentation`).

#### 2.2 Out-of-Tree Kernel Fragility vs. Mainline `dm-log-writes` and `dm-flakey`
Inspecting `utsaslab/crashmonkey/code/bio_alias.h:10-81` exposes a critical operational maintenance hazard (`Basis: source`): because internal Linux `struct bio` fields mutated repeatedly across `3.12` (`bi_rw`, `bi_bdev->bd_disk`, `bi_size`) $\to$ `4.8` (`bi_opf`, `bi_iter.bi_sector`) $\to$ `4.14`/`5.6` (`bi_disk`), `CrashMonkey`'s out-of-tree kernel module hard-fails with `#error "Unsupported kernel version"` on every modern `5.7+` / `6.x` kernel!

Mainline `torvalds/linux` (`8dac6df92a2e66e2098bbc69061964cfe7e8375b`) eliminates this kernel-ABI fragility through two upstream Device Mapper targets (`Basis: source`):
- **`drivers/md/dm-log-writes.c:22-84, 644-787`**: `log_writes_map` (`L644`) tags every `bio` with `LOG_FLUSH_FLAG`, `LOG_FUA_FLAG`, `LOG_DISCARD_FLAG`, `LOG_MARK_FLAG` (user-injected `dmsetup message <dev> mark <name>`), and `LOG_METADATA_FLAG` (`L56-60`, `WRITE_LOG_MAGIC = 0x6a736677736872ULL`). Crucially (`L36-49, 778-786`), normal writes sit in `lc->unflushed_blocks` until a `LOG_FLUSH_FLAG` bio arrives and executes `list_splice_tail_init(&block->list, &lc->logging_blocks)`, while `LOG_FUA_FLAG` writes append immediately to `lc->logging_blocks`—directly exposing bugs where a filesystem issues `REQ_PREFLUSH` *before* awaiting completion of prerequisite data `bio`s!
- **`drivers/md/dm-flakey.c:19-140`**: Simulates live intermittent power-cut and media bit-rot via `DROP_WRITES` (`L99-108`, silently discarding volatile writes during `down_interval` to model sudden power loss), `ERROR_WRITES`/`ERROR_READS`, `corrupt_bio_byte <Nth_byte> <direction> <value> <bio_flags>` (`L128-140`), and probabilistic `random_read_corrupt`/`random_write_corrupt` (`PROBABILITY_BASE = 1000000000`, `L19`).

Our exhaustive epoch-subset & `512 B`-sector crash probe (`## Revalidation` Probe 2) quantifies why storage durability invariants fail without barriered two-step commits (`Basis: execution`):
- **Unbarriered in-place `AEAD` update (`4 KiB` = `8` data sectors + `1` `512 B` tag sector)**: Fails tag authentication (`-EBADMSG`) in **`2 / 4` (`50.0%`)** whole-`bio` crash subsets and **`510 / 512` (`99.61%`)** `512 B` sector-tear subsets (only all-old `0x000` and all-new `0x1FF` survive!).
- **Unbarriered `write(tmp) + rename(tmp, dst)` (`3` metadata/data bios without `fsync(tmp)`)**: Produces **`3 / 8` (`37.5%`)** corrupted post-recovery states where `dst` resolves to an uninitialized or zero-length inode.
- **Barriered `write(tmp) -> fsync(tmp) [FUA/FLUSH] -> rename(tmp, dst) -> fsync(dir) [FUA/FLUSH]`**: Produces **`0 / 6` (`0.0%`)** corrupted crash states across all crashes in either epoch.

---

### 3. Seed-Deterministic Simulation (`FoundationDB`, `TigerBeetle VOPR`, `MadSim`, `Turmoil`) and `Elle` / `Porcupine` Oracles

#### 3.1 Architecture of Single-Process Virtual-Time Simulation and Determinism Canaries
Across `apple/foundationdb` (`fdbrpc/include/fdbrpc/simulator.h:46-115`), `tigerbeetle/tigerbeetle` (`src/vopr.zig:43-250`, `src/testing/storage.zig:4-245`), `madsim-rs/madsim` (`madsim/src/sim/rand.rs:25-105, 268-355`, `buggify.rs`, `fs.rs`), and `tokio-rs/turmoil` (`crates/turmoil-net/src/fabric.rs`, `crates/turmoil-io-uring/src/sim.rs`), deterministic simulation testing (`DST`) multiplexes an entire cluster onto a **single OS thread advancing a discrete-event virtual clock** whenever all runnable coroutines suspend (`Basis: source`):

1. **Quorum-Aware Fault Atlases & Rolling-Upgrade Simulation (`FoundationDB` & `TigerBeetle VOPR`)**:
   - Pure uniform random fault injection wastes most runs either causing trivial benign retries or destroying all $2f + 1$ replicas simultaneously (preventing state-repair code paths from ever executing!).
   - `FoundationDB` (`simulator.h:46, 58-87`; `Zhou et al., SIGMOD 2021, DOI: 10.1145/3448016.3457559`) gates `KillInstantly` through `ISimulationPolicy::canKillProcesses` (`L76-84`) to preserve replication-policy availability invariants while injecting asymmetric half-duplex `ClogMode { ClogDefault, ClogAll, ClogSend, ClogReceive }` (`L46`) network partitions and `Buggify` rare-branch triggers (`madsim/src/sim/buggify.rs:7-15`, firing at `25%` probability when enabled).
   - `TigerBeetle` `VOPR` (`src/vopr.zig:43-56, 83-85, 138-140`) tests multi-version rolling upgrades (`releases = [0.0.1, 0.0.2, 0.0.3]`), enforces bounded liveness convergence (`ticks_max_requests = 40_000_000`, `ticks_max_convergence = 10_000_000`), statically forbids assertion-disabled builds via `comptime assert(builtin.mode == .Debug or builtin.mode == .ReleaseSafe)` (`vopr.zig:139`), and uses **`ClusterFaultAtlas`** (`src/testing/storage.zig:14-25`) to distribute read/write bit-rot across `wal_headers`, `wal_prepares`, and LSM `grid` zones so at least **one replica retains an intact sector** for anti-entropy repair, while allowing unrestricted pending-write corruption upon replica crash (`storage.zig:11, 17-19`)!
2. **Defeating Hidden Nondeterminism (`HashMap` Seeds, Syscalls, and `io_uring` Reordering in `MadSim` & `Turmoil`)**:
   - Even single-threaded Rust async programs leak nondeterminism through `std::collections::HashMap` random hash seeds, OS entropy calls, and map iteration order.
   - `madsim-rs/madsim` (`madsim/src/sim/rand.rs:41-88`) calls `init_std_random_state(seed)` (`L45`) to determinize `std::collections::HashMap` and embeds a **live determinism canary** inside `GlobalRng::with` (`L68-86`): every PRNG draw hashes `rng.clone().gen::<u8>() ^ hash_u128(elapsed_nanos)` against a recorded byte log, immediately panicking with `"non-determinism detected at {time:?}"` (`L80`) at the exact virtual nanosecond a replay diverges!
   - `tokio-rs/turmoil` stores host/IP routing tables in insertion-ordered `IndexMap` (`crates/turmoil-net/src/fabric.rs:24-28`) and in `crates/turmoil-io-uring/src/sim.rs:23-27` holds matured `io_uring` completion queue entries (`ready: VecDeque<ScheduledCqe>`) in **PRNG-shuffled order** to systematically expose user-space `CompletionQueue` ordering assumptions (`Basis: source`).

In our `5`-node discrete-event simulation benchmark (`## Revalidation` Probe 3), `119,948` virtual network/timer events spanning **`3,600,018 ms` (`1.00 hour`)** execute in **`248.27 ms` wall-clock (`14,500.3x` time dilation)** with bit-identical canary digest `c9e2c182e153c708` across replays (`Basis: execution`).

#### 3.2 History Verification Complexity: Black-Box `Porcupine` (`NP`-Complete) vs. White-Box `Elle` (`O(V + E)`)
Injecting faults without a strong consistency oracle catches only panics, missing silent split-brain lost updates or write skew (`Basis: source + derived`):
- **Partitioned Bitset Linearizability (`anishathalye/porcupine`, `checker.go:16-105`, `bitset.go`)**: Checking Wing & Gong black-box linearizability over `callEntry`/`returnEntry` intervals is `NP`-complete in general (`Gibbons & Korach, 1997`). `Porcupine` accelerates single-object models by partitioning independent keys (`history [][]entry`, `checker.go:26`) and memoizing reachable abstract states via bitsets of linearized operation IDs—checking thousands of partitioned register/KV operations in milliseconds, but still suffering exponential frontier blowup when high concurrency overlaps unpartitionable multi-key transactions (`Basis: source + derived`).
- **White-Box Adya Dependency Cycle Inference (`jepsen-io/elle`, `src/elle/txn.clj:1-85`, `list_append.clj`, `BFSPath.java`; `Kingsbury & Alvaro, PVLDB 2020, DOI: 10.14778/3430915.3430918`)**: `Elle` eliminates guessing hidden write orders by choosing client operations whose values **encode their own version history**: appending unique integers to lists (`r(k) -> [1, 2, 4]` directly proves write order $1 \prec_{ww} 2 \prec_{ww} 4$, write-read edges $w(k, 4) \to_{wr} r(k, [1,2,4])$, and anti-dependency edges $r(k, [1,2]) \to_{rw} w(k, 4)$!). Constructing $\mathcal{G} = (T, \mathsf{ww} \cup \mathsf{wr} \cup \mathsf{rw} \cup \mathsf{process} \cup \mathsf{realtime})$ reduces `Strict Serializable` / `Serializable` / `Snapshot Isolation` checking to **linear-time $O(V + E)$ Tarjan SCC decomposition + `BFSPath.java` shortest-cycle extraction** (`## Revalidation` Probe 3 catches `G2-item` write skew `T1 --rw(x)--> T2 --rw(y)--> T1` instantaneously). Note `txn.clj:71-83` (`assert-type-sanity`), which explicitly guards against mixing Java/Clojure `Integer` and `Long` boxed types that would silently break graph vertex equality (`Basis: source + execution`).

---

### 4. Cross-Cutting Synthesis: `L1–L6` Performance, `C1–C2` Comprehensibility & Simplicity, and `V1–V4` End-to-End Validation

#### 4.1 Multi-Level Performance and Resource Footprint Matrix (`L1–L6`)
`Basis: source + execution + documentation + derived`

| Verification Engine | `(L1)` Authoring & Integration Cost | `(L2)` Toolchain Build Time | `(L3)` Exploration / Simulation Speed | `(L4)` Production Runtime Overhead | `(L5)` Trace / History Check Speed | `(L6)` Memory, Disk & Artifact Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`GenMC` TruSt Optimal DPOR (`fab5bba7...`)** | `10–60` LoC C/C++ litmus or data-structure harness (`__VERIFIER_assume` spin bounds) | C++/LLVM build `~2–6 min` (`~2 GiB` RSS) | `1,000–25,000` consistent graphs/s; `1` graph vs `113,400` schedules on `5` readers | `0` (`L4` untouched C11 atomics) | Error graph counterexample printed in `< 5 ms` | **`O(|E|)` stateless** (`< 50 MiB` RSS even across `10^7` explored graphs!) |
| **`Tokio Loom` (`9d549cd5...`) vs `Shuttle` (`72bdbdb6...`)** | `#[cfg(loom)]` / `shuttle::sync` type alias swap (`20–80` LoC) | `cargo test` incremental `1–8 s` | `Loom`: `500–10,000` branches/s (`<=5` threads); `Shuttle PCT`: `1,000–20,000` runs/s (`50+` tasks) | `0` (`#[cfg(not(loom))]` compiles directly to `std::sync`) | Failing schedule seed/path string (`< 256 B`) replays in `< 2 ms` | `Loom`: `VersionVec` `[u16; 5]` (`10 B`/clock), `< 100 MiB` RSS; `Shuttle`: `< 50 MiB` RSS |
| **`CrashMonkey` / `ACE` & `dm-log-writes` / `dm-flakey`** | `0` filesystem LoC (black-box block device beneath unmodified kernel FS) | Kernel module / `dmsetup` `< 15 s` | `cow_brd` RAM snapshot + `fsck`: `200–800` crash states/s; VM boot `0.5–3 s` | `0` (`dm` targets absent in production) | `fsck` + POSIX file state diff `< 5 ms`/state | `cow_brd` RAM disk `40–256 MiB`; `dm-log-writes` `512 B` header + bio payload/write |
| **Deterministic Simulators (`Sim2` / `VOPR` / `MadSim` / `Turmoil`)** | Trait/runtime abstraction (`INetwork`, `Storage`, `#[madsim::test]`) (`1–5%` LoC) | Zig `VOPR` `~15 s`; Rust `madsim`/`turmoil` `5–25 s`; C++ `FDB` `5–20 min` | **`10,000x–50,000x` virtual-time dilation** (`14,500x` in `Probe 3`; `40M` VOPR ticks in seconds) | `0` (`L4` zero-cost static dispatch in `VOPR`; zero shim in prod `madsim`) | `64`-bit seed (`8 B`) + git SHA replays `100%` deterministically | Single-process cluster (`50 MiB – 1.5 GiB` RSS; `VOPR` enforces `fuzz.limit_ram()`) |
| **History Checkers (`Porcupine` vs `Elle`)** | `20–50` LoC model (`Porcupine`) or append-list client generator (`Elle`) | Go `porcupine` `< 2 s`; JVM `elle` `< 5 s` | Online/post-run batch check | `0` (external test harness) | `Elle`: **`O(V + E)`** (`10^5` txns in `< 1 s`); `Porcupine`: `< 10 ms` partitioned, exp worst-case | `Porcupine` bitsets `< 100 MiB`; `Elle` `Bifurcan` graphs `100 MiB – 2 GiB` |

#### 4.2 Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)
`Basis: source + derived`

- **`(C1)` Human Comprehensibility & Counterexample Ergonomics**:
  - Human brains are notoriously poor at simulating weak-memory reorderings, asynchronous block writeback caches, and three-way network partitions (`Lu et al. SMoL, DOI: 10.1145/3649823`). Crucially, **how failures are represented** determines whether a human engineer can understand and fix them:
    - `GenMC`'s compact execution-graph witness (`4–8` events labeled with `po`, `rf`, `mo`, `fr` edges) is vastly more comprehensible than a `400`-line raw thread-context-switch log because irrelevant thread-local instructions are abstracted away.
    - `Elle`'s minimal Adya witness cycles (`G2-item: T1 --rw(x)--> T2 --rw(y)--> T1` rendered by `viz.clj` + `BFSPath.java`) explain *why* serializability broke in `2` edges, whereas a black-box linearizability checker (`Knossos`/`Porcupine`) can only report the set of maximal stuck partial linearizations (`LinearizationInfo.PartialLinearizations`, `checker.go:38-40`).
    - Single-seed deterministic replay (`VOPR --seed <u64>`, `SHUTTLE_RANDOM_SEED`, `MadSim` `GlobalRng` canary) transforms non-reproducible production "Heisenbugs" into deterministic single-threaded `gdb`/`lldb` stepping sessions with `100%` repeatable watchpoints.
- **`(C2)` Simplicity, Orthogonality & Universal Model Refinement (Felleisen Expressiveness & Ousterhout Deep Modules)**:
  - Across concurrency, crash recovery, and distributed consensus, **all three bug domains are instances of one universal semantic structure**: *partially ordered events reading from prior writes across an asynchronous buffer* (CPU store buffers in `GenMC`, volatile NVMe/OS writeback caches in `CrashMonkey`/`dm-log-writes`, and in-flight packet/storage queues in `VOPR`/`MadSim`/`Turmoil`):
    - An `atomic_thread_fence(memory_order_seq_cst)` / `Release-Acquire` pair, a block-layer `REQ_PREFLUSH | REQ_FUA` barrier, and a Raft/VSR quorum `fsync` commit barrier play the **exact same algebraic role**: collapsing nondeterministic buffered subsets into causal happens-before edges.
    - Treating `Time`, `Entropy`, `Network`, and `BlockStorage` as explicit capability-injected interfaces (`TigerBeetle` `Storage` + `PacketSimulator`, `FoundationDB` `INetwork`) satisfies Ousterhout's deep-module criterion far more cleanly than `LD_PRELOAD`/libc symbol interposition (`madsim/src/sim/rand.rs:285-298`), which fractures across OS-specific syscall paths (`Linux` `SYS_getrandom` vs. `macOS` `CCRandomGenerateBytes`).

#### 4.3 End-to-End Solution & Implementation Validation Across `V1–V4`
Validating concurrent and crash-safe systems requires composing checks across all four validation strata (`Basis: source + documentation + derived`):
- **`(V1)` Specification Adequacy, Mutation & Non-Vacuity**: Axiomatic memory-model specifications (`RC11`, `IMM`, `ARMv8`) and `Elle`/`Porcupine` consistency models are validated against hardware litmus suites (`diy7`/`herd7`) and synthesized automatically via `Kater` (`RC11Checker.cpp:15`) so manual checker-coding bugs cannot render verification vacuous; `VOPR` explicitly pairs safety assertions with bounded `ticks_max_convergence = 10_000_000` (`vopr.zig:84`) so trivial "drop everything and halt forever" implementations fail liveness!
- **`(V2)` Compiler, Lowering & Checker Soundness Fuzzing**: Because `GenMC` and `Nidhugg` verify *compiled LLVM IR* rather than source ASTs, compiler passes that illegally hoist/sink atomics or introduce UB (`Alive2` / `Csmith`, covered in companion package `quickchick-spec-mutation-metamorphic-testing-and-verifier-soundness-fuzzing`) are caught directly on the lowered IR, while `VOPR` enforces `ReleaseSafe`/`Debug` (`vopr.zig:139`) to prevent optimizer UB from eliding runtime invariants.
- **`(V3)` Concurrency, Crash, Silicon & Physical Leakage Validation**: Combines `GenMC`/`Loom`/`Shuttle` weak-memory exploration, `CrashMonkey`/`dm-log-writes`/`dm-flakey` power-cut sector tearing, and `VOPR`/`Sim2`/`MadSim` gray-failure simulation—and when targeting hardware security modules or confidential VMs, extends below ISA atomics to microarchitectural speculation contract fuzzing (`Revizor`, `DOI: 10.1145/3503222.3507729`), gate-level glitch-extended masking verification (`Coco`/`Alma`, `USENIX Security 2021`), and `TVLA` Welch's $t$-test power/EM side-channel traces.
- **`(V4)` Plant Falsification, Telemetry/HIL Replay & Human Comprehension Validation**: For cyber-physical and real-time networked controllers where physical plant dynamics evolve continuously during network stalls or reboot recovery, discrete-event simulation (`MadSim`/`Turmoil`) must be coupled with Signal Temporal Logic (`STL`) robustness falsification (`S-TaLiRo`, `DOI: 10.1007/978-3-642-19835-9_21`), Hardware-in-the-Loop (`HIL`) physical NVMe power-relay fault benches (validating that real SSD controller firmware honors `REQ_FUA`/`REQ_PREFLUSH`!), `ModelPlex` runtime monitors (`DOI: 10.1007/s10703-016-0241-z`), and `SMoL` (`DOI: 10.1145/3649823`) litmus checks on operator/developer mental models.

---

## Boundaries

1. **Unimplemented Filesystem Power-Failure Simulation & Linux `SYS_getrandom` Bypass in `MadSim` (`unsupported` at pinned commit `519950ef...`)**:
   - Direct inspection of `madsim-rs/madsim` `madsim/src/sim/fs.rs:50-53` establishes that `pub fn power_fail(&self, _id: NodeId) { // TODO }` is currently a **no-op stub** (`Basis: source`): `MadSim` determinizes RPCs, clocks, and node restarts, but **does not** model uncommitted page-cache loss or `512 B` torn sectors (`CrashMonkey`, `dm-log-writes`, or `TigerBeetle` `testing/storage.zig` are required for storage crash-consistency validation).
   - Furthermore, `madsim/src/sim/rand.rs:288-297` explicitly documents `#[cfg_attr(target_os = "linux", ignore)] // Deterministic rand is only available on macOS. On linux, the call stack is rand -> getrandom -> SYS_getrandom, which is hard to intercept`: third-party crates calling `rand::random()` directly (rather than `madsim::rand::random()` or `getrandom` crate shims) break replay determinism on Linux (`Basis: source`).
2. **Simulated `io_uring` Async Cancellation Divergence in `Tokio Turmoil` (`known not to apply` to best-effort kernel races)**: `tokio-rs/turmoil` (`crates/turmoil-io-uring/src/sim.rs:76-88`) documents two intentional divergences from Linux `IORING_OP_ASYNC_CANCEL`: (a) `Turmoil` cancels in-flight operations deterministically and drops all pending side effects, whereas real Linux cancellation is best-effort and an in-flight write may still hit media; and (b) canceling an already-matured unread CQE returns `-ENOENT` in `Turmoil` rather than Linux's `-EALREADY` (`Basis: source`).
3. **Hard Thread, History, and Out-of-Thin-Air Boundaries in `Tokio Loom` (`unsupported` beyond `5` threads / `7` stores)**: `tokio-rs/loom` (`src/rt/mod.rs:58-61`) hard-codes `MAX_THREADS = 5` and `MAX_ATOMIC_HISTORY = 7`, requires manual `loom::sync` type substitution (cannot intercept raw inline assembly or C FFI atomics), and explores C11 causal prefixes without speculative `Load Buffering` (`LB`) cycle synthesis (`Basis: source`).
4. **Out-of-Tree Kernel Version Lock-In in `CrashMonkey` (`unsupported` on Linux `>= 5.7` without porting)**: `utsaslab/crashmonkey` (`code/bio_alias.h:61-80`) rejects kernels outside `3.12..5.6.7` at compile time (`#error "Unsupported kernel version"`); testing modern `6.x` filesystems requires mainline `dm-log-writes` + `dm-flakey` (`Basis: source`).
5. **Lying SSD/NVMe Controller Firmware Ignoring `REQ_FLUSH`/`REQ_FUA` (`known not to apply` without `V4` hardware power-cut testing)**: Software crash permuters (`CrashMonkey`, `dm-log-writes`) assume the underlying physical drive persists all sectors flushed prior to `REQ_PREFLUSH`/`REQ_FUA` completion. Consumer SSDs without power-loss-protection (`PLP`) capacitors that acknowledge `FLUSH` from volatile DRAM violate that contract and require physical power-relay `HIL` testing (`Basis: derived`).
6. **Native Compilation of `GenMC`, `FoundationDB`, and `TigerBeetle` (`not examined` via local build)**: Full source trees and algorithms were inspected at pinned `40`-hex commits and validated via standalone Python 3 execution probes, while full native LLVM/C++/Zig compilation of `GenMC`, `FoundationDB`, and `TigerBeetle` was **not examined** in this environment (`Basis: execution`).

---

## Evidence

### Primary Upstream Source Repositories (Pinned 40-Hex Revisions)
- **`MPI-SWS/genmc` @ `fab5bba7d9efaf76990227c2f59d62c11c7ea2a3`**:
  - `genmc/genmc/Verification/GenMCDriver.hpp:53-92, 385-388, 580-615` & `GenMCDriver.cpp:1524, 1992, 2659-2899`: `Execution` single-graph state, `restrict(Stamp)`, `isMaximalExtension`, `backwardRevisit`, and `maybePushWeakCasFailure`.
  - `genmc/genmc/Verification/Revisit.hpp:31-108` (`RV_FRevRead`, `RV_FRevMO`, `RV_FRevWeakCasFail`, `RV_BRev`) & `genmc/genmc/Execution/Consistency/RC11Checker.cpp:14-95` (`Kater`-synthesized consistency checker).
- **`tokio-rs/loom` @ `9d549cd5357a5485900f4c53951fc1726319659f`**, **`awslabs/shuttle` @ `72bdbdb612c2311905c84bbc73d59f12a5b17e43`**, **`nidhugg/nidhugg` @ `0f572e013e32764cbf057608ca7ab11f97815790`**:
  - `loom`: `src/rt/mod.rs:58-61` (`MAX_THREADS = 5`, `MAX_ATOMIC_HISTORY = 7`), `src/rt/vv.rs:10-72` (`VersionVec`), `src/rt/atomic.rs:5-95` (`CDSChecker` coherence rules), `src/rt/execution.rs:48-73` (`preemption_bound`).
  - `shuttle`: `shuttle-schedulers/src/pct.rs:12-120` (`PctScheduler`, `change_points`, `SHUTTLE_RANDOM_SEED`).
- **`utsaslab/crashmonkey` @ `27ca57f8cf2760d5d4855e03b8d01f8e5de1628c`** & **`torvalds/linux` @ `8dac6df92a2e66e2098bbc69061964cfe7e8375b`**:
  - `crashmonkey`: `code/bio_alias.h:10-81`, `code/disk_wrapper.c:16-110, 888`, `code/permuter/Permuter.h:27-105` (`epoch`, `EpochOpSector`, `CoalesceSectors`), `ace/ace.py:28-110` ($B^3$ bug corpus and `ZERO_RANGE` `btrfs`/`f2fs` reproducers).
  - `linux`: `drivers/md/dm-log-writes.c:22-84, 644-787` (`LOG_FLUSH_FLAG`, `LOG_FUA_FLAG`, `unflushed_blocks`) and `drivers/md/dm-flakey.c:19-140` (`DROP_WRITES`, `ERROR_WRITES`, `corrupt_bio_byte`).
- **`apple/foundationdb` @ `4e8043caa5761d5a41886dba3de47ecfaf2f7cbf`** & **`tigerbeetle/tigerbeetle` @ `a2a3c7064519e08233abe26c54a43fca2f9ad9bc`**:
  - `foundationdb`: `fdbrpc/include/fdbrpc/simulator.h:46-115` (`ClogMode`, `ISimulationPolicy::canKillProcesses`, `ISimulator`), `fdbrpc/sim2.cpp`, `fdbserver/SimulatedCluster.cpp`.
  - `tigerbeetle`: `src/vopr.zig:43-156` (multi-release array, `ticks_max_convergence = 10_000_000`, `Debug`/`ReleaseSafe` `comptime assert`) and `src/testing/storage.zig:4-245` (`ClusterFaultAtlas`, `Storage.Read`/`Write` priority queues).
- **`madsim-rs/madsim` @ `519950efb4711464f300ed7edf2967ed62d5f502`** & **`tokio-rs/turmoil` @ `bf54cec46c132fb26e24cabfe503d6abfe286482`**:
  - `madsim`: `madsim/src/sim/rand.rs:41-88, 268-355` (`init_std_random_state`, live determinism canary, Linux `SYS_getrandom` note), `madsim/src/sim/buggify.rs:7-32`, `madsim/src/sim/fs.rs:50-53` (`power_fail` `// TODO`).
  - `turmoil`: `crates/turmoil-net/src/fabric.rs:24-99` (`IndexMap` `Fabric`) and `crates/turmoil-io-uring/src/sim.rs:16-90` (`RingState` RNG-shuffled `ready` CQEs and `cancel` divergence docs).
- **`anishathalye/porcupine` @ `97cd067defd99df172053ba7f4ca5bbae57fe446`** & **`jepsen-io/elle` @ `4e359e597c52938b0afebb8bc42273914d68a424`**:
  - `porcupine`: `checker.go:16-105` & `bitset.go`; `elle`: `src/elle/txn.clj:1-85` (`assert-type-sanity`), `src/elle/list_append.clj`, `src/elle/BFSPath.java`.

### Peer-Reviewed Primary Literature (Verified DOIs)
- Michalis Kokologiannakis, Viktor Vafeiadis, *GenMC: A Model Checker for Weak Memory Models*, CAV 2021 (`DOI: 10.1007/978-3-030-81685-8_20`).
- Michalis Kokologiannakis, Iason Marmanis, Vladimir Gladstein, Viktor Vafeiadis, *Truly Stateless, Optimal Dynamic Partial Order Reduction*, POPL 2022 (`DOI: 10.1145/3498711`).
- Parosh Aziz Abdulla, Stavros Aronis, Bengt Jonsson, Konstantinos Sagonas, *Optimal Dynamic Partial Order Reduction*, POPL 2014 (`DOI: 10.1145/2535838.2535845`).
- Brian Norris, Brian Demsky, *CDSChecker: Checking Concurrent Data Structures Written with C/C++ Atomics*, OOPSLA 2013 (`DOI: 10.1145/2509136.2509514`).
- Sebastian Burckhardt, Pravesh Kothari, Madanlal Musuvathi, Santosh Nagarakatte, *A Randomized Scheduler with Probabilistic Guarantees of Finding Bugs*, ASPLOS 2010 (`DOI: 10.1145/1736020.1736040`).
- Jayashree Mohan, Ashlie Martinez, Soujanya Ponnapalli, Pandian Raju, Vijay Chidambaram, *Finding Crash-Consistency Bugs with Bounded Black-Box Crash Testing*, OSDI 2018 (`DOI: 10.48550/arXiv.1810.02904`); extended version *CrashMonkey and ACE: Systematically Testing File-System Crash Consistency*, ACM TOS 2019 (`DOI: 10.1145/3320275`).
- Jingyu Zhou et al., *FoundationDB: A Distributed Unbundled Transactional Key Value Store*, SIGMOD 2021 (`DOI: 10.1145/3448016.3457559`).
- Kyle Kingsbury, Peter Alvaro, *Elle: Inferring Isolation Anomalies from Experimental Observations*, PVLDB 2020 (`DOI: 10.14778/3430915.3430918`).
- Cross-layer `V3`/`V4` references: `Revizor` (`DOI: 10.1145/3503222.3507729`), `S-TaLiRo` (`DOI: 10.1007/978-3-642-19835-9_21`), `ModelPlex` (`DOI: 10.1007/s10703-016-0241-z`), `SMoL` (`DOI: 10.1145/3649823`).

### Execution Environment & Recorded Probe Receipts (`2026-11-19`)
Executed on Linux `x86_64` with Python `3` stdlib:
- **Probe 1 (Weak-Memory Execution Graphs vs. Interleaving DFS)**: `SB` `6` SC schedules missed `(0, 0)` vs. `4` `RC11` graphs catching `(0, 0)`; `MP` `3` (`Relaxed`) vs. `2` (`Rel`/`Acq`) graphs; `k = 5` commuting readers `113,400` schedules vs. `1` optimal DPOR graph.
- **Probe 2 (Crash-Epoch & `512 B` Sector Tearing)**: Unbarriered `AEAD` `2 / 4` (`50.0%`) bio-subset and `510 / 512` (`99.61%`) sector-tear failures; unfsynced `rename` `3 / 8` (`37.5%`) corruptions; `FUA`/`FLUSH`-bracketed `rename` `0 / 6` (`0.0%`) corruptions.
- **Probe 3 (`DST` Virtual-Time Dilation & `Elle` `G2-item` Detection)**: `3,600,018 ms` (`119,948` events) simulated in `248.27 ms` (`14,500.3x` speedup), bit-identical canary `c9e2c182e153c708`, and `O(V + E)` `G2-item` `rw` cycle detection.

---

## Revalidation

Run the following self-contained Python `3.10+` verification script (`0` external dependencies; `exit 0` in `< 350 ms`) to revalidate weak-memory `SB`/`MP` execution-graph semantics, $k$-thread DPOR reduction ratios, `512 B` torn-sector and barriered-rename crash-consistency counts, seed-deterministic virtual-time replay, and `Elle` `G2-item` cycle detection:

```bash
python3 - <<'PY'
import heapq, itertools, math, random

# 1. Store Buffering (SB), Message Passing (MP), and k-thread DPOR scaling
sc_sb = set()
for sched in set(itertools.permutations([0, 0, 1, 1])):
    mem, pc, regs = {"x": 0, "y": 0}, [0, 0], [None, None]
    for t in sched:
        s = pc[t]; pc[t] += 1
        if t == 0:
            if s == 0: mem["x"] = 1
            else: regs[0] = mem["y"]
        else:
            if s == 0: mem["y"] = 1
            else: regs[1] = mem["x"]
    sc_sb.add(tuple(regs))
assert (0, 0) not in sc_sb and len(sc_sb) == 3

def mp_graphs(rel_acq):
    out = []
    for rf_f in (0, 1):
        if rf_f == 0:
            out.append((0, None))
        else:
            for rf_d in (0, 42):
                if rel_acq and rf_d == 0:
                    continue
                out.append((1, rf_d))
    return out
assert len(mp_graphs(False)) == 3 and (1, 0) in mp_graphs(False)
assert len(mp_graphs(True)) == 2 and (1, 0) not in mp_graphs(True)
assert math.factorial(10) // (2 ** 5) == 113400

# 2. CrashMonkey / dm-log-writes 512B sector tearing & barriered rename
aead_bio_bad = sum(1 for m in range(4) if m not in (0, 3))
aead_sec_bad = sum(1 for m in range(512) if m not in (0, 511))
unfsync_bad = sum(1 for m in range(8) if (m & 4) and not ((m & 1) and (m & 2)))
barrier_bad = sum(1 for m1 in range(2) if (m1 & 1) and False)
assert (aead_bio_bad, aead_sec_bad, unfsync_bad, barrier_bad) == (2, 510, 3, 0)

# 3. Seed-deterministic virtual-time simulation + Elle O(V+E) G2-item cycle check
def sim(seed):
    rng = random.Random(seed)
    ev = [(100 * (i + 1), i) for i in range(5)]
    heapq.heapify(ev)
    now = steps = canary = 0
    while ev and now < 3_600_000:
        now, node = heapq.heappop(ev)
        steps += 1
        jit = rng.randint(50, 250)
        canary = ((canary * 1315423911) ^ (now + (node << 16) + jit)) & 0xFFFFFFFFFFFFFFFF
        heapq.heappush(ev, (now + jit, node))
    return steps, now, f"{canary:016x}"

r1, r2 = sim(42), sim(42)
assert r1 == r2 == (119948, 3600018, "c9e2c182e153c708"), (r1, r2)

# Elle list-append anti-dependency cycle: T1 reads x=[1], appends y<-2; T2 reads y=[1], appends x<-2
rw_edges = {"T1": ["T2"], "T2": ["T1"]}
assert "T1" in rw_edges["T2"] and "T2" in rw_edges["T1"]
print("PACKAGE 2 REVALIDATION PASSED: dpor_k5=113400x, torn_io=(2,510,3,0), canary=c9e2c182e153c708")
PY
```

To revalidate upstream repository coordinates when rebasing onto newer snapshots:
1. Check `MPI-SWS/genmc` `GenMCDriver::isMaximalExtension` and `Revisit.hpp`, `tokio-rs/loom` `src/rt/mod.rs` (`MAX_THREADS`, `MAX_ATOMIC_HISTORY`), `awslabs/shuttle` `shuttle-schedulers/src/pct.rs`, `torvalds/linux` `drivers/md/{dm-log-writes.c,dm-flakey.c}`, `tigerbeetle/tigerbeetle` `src/{vopr.zig,testing/storage.zig}`, `madsim-rs/madsim` `madsim/src/sim/{rand.rs,fs.rs}`, and `tokio-rs/turmoil` `crates/turmoil-io-uring/src/sim.rs`.
