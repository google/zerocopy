# Bounds on retired-but-unreclaimed memory in safe memory reclamation: hazard pointers, epochs, DEBRA/DEBRA+, NBR, interval-based reclamation, hazard eras, Hyaline/Crystalline, VBR, PEBR, HP-BRCU, and the ERA theorem

## Summary

- **What a bound counts differs between papers, so bounds are not directly comparable.** Michael-style hazard pointers bound *all* retired-but-unfreed nodes by a function of thread count and slot count only (O(K·N²) for N threads with K slots each when the scan threshold is a constant multiple of N·K). DEBRA+ bounds limbo-bag contents by O(m·n²) (m = most records removed by one operation). Interval-based reclamation (IBR) bounds only the blocks made *unreclaimable by a stalled set*, by `Emax × epoch_freq × num_threads`, where `Emax` is an absolute epoch number, so the bound grows with execution history. Hyaline-S/-1S bound unreclaimable *nodes* by `δEra × Freq × n(k+1)`. HP-BRCU bounds garbage by `2GN + GN² + H`. Epoch-based reclamation (EBR), plain DEBRA, Hyaline and Hyaline-1 have no bound under an indefinitely stalled participant.
- **Failure models also differ.** "Stalled" (stopped forever) and "starving" (running but not finishing) threads are distinct. IBR and Hyaline-S state that their bound does not cover a starving thread unless operations restart after a bounded number of failed CAS operations. Neutralization schemes (DEBRA+, NBR) replace this assumption with OS signals and restartable read phases.
- **The ERA theorem (Sheffi–Petrank, PODC 2023)** defines robustness (retired nodes ≤ f(i)·N with f = o(max active nodes)), weak robustness (f polynomial in max active nodes), easy integration (five syntactic conditions that, among other things, forbid rollbacks into data-structure code and forbid the scheme from touching data-structure fields), and wide applicability (safety, linearizability and progress preserved for every "access-aware" implementation). It proves that no scheme has all three properties, and in fact that easy integration plus wide applicability excludes even weak robustness. The witness is Harris's linked list with one traverser frozen at the head while another thread alternates `insert(n+1)` / `delete(n)`.
- **Measured on a real harness (`kaist-cp/smr-benchmark`):** with one auxiliary participant that pins once and never repins, the harness's EBR collector accumulated 143.2–208.2 million deferred objects (8.55–12.43 GiB of jemalloc-allocated memory) in 10 s on a hash map with 32 worker threads. The count grew linearly with run length (86.9 M at 5 s, 341.2 M at 20 s), at about 64 bytes per deferred object. Under the same stall, PEBR stayed at 0.23–0.28 M deferred objects (17.8–20.2 MiB) at every run length. Without a stall, EBR peaked at 0.70–1.41 M. Basis: execution on a loaded shared host; throughput figures from these runs are not interpretable.
- **Production libraries limit deferral heuristically, not with proved bounds:**
  - `crossbeam-epoch` has no bound under a pinned stalled thread.
  - Userspace RCU's `defer_rcu` caps each thread's queue at 4096 entries by *blocking* in `synchronize_rcu()`, so it trades progress for memory; `call_rcu` has an unbounded queue.
  - Linux RCU escalates grace-period forcing at 100 ms / 10 s and at 10,000 queued callbacks per CPU, and states that these mechanisms "are not foolproof".
  - Folly's hazard-pointer domain reclaims when its retired count reaches `max(1000, 2 × hazard-pointer count)` or every 2 s.

## Applicability

The report concerns concurrent (unmanaged-memory) safe memory reclamation (SMR) for lock-free data structures: how many retired objects can remain unreclaimed, under which thread-failure assumptions, and how implementations and benchmark harnesses measure and limit that number.

Subjects and how they relate:

- **Papers (normative for their own theorems; no shared specification exists).**
  - Read in full text: the ERA theorem (arXiv v1, November 2022, preprint of PODC 2023); DEBRA/DEBRA+ (arXiv 1712.01044, full version of PODC 2015); NBR (arXiv 2012.14542 v2, PPoPP 2021 version with appendix); IBR (author PDF of the PPoPP 2018 paper); Hyaline (arXiv 1905.07903 v2, the PLDI 2021 version); Crystalline (published PLDI 2024 PDF); HP-BRCU (34-page author version of SPAA 2024); Hazard Eras (an extended LIPIcs-format version in the authors' `pramalhe/ConcurrencyFreaks` repository, pinned below; the SPAA 2017 brief announcement itself was not read); Fraser's thesis; Desnoyers et al. 2012.
  - Abstract or metadata only: Michael 2004, PEBR, the VBR full paper (DISC 2021), and Hart et al. 2007. Claims about these are marked as relayed.
- **Harnesses examined in source:** `kaist-cp/smr-benchmark` (also executed), `urcs-sync/Interval-Based-Reclamation`, `rusnikola/lfsmr`. The smr-benchmark EBR and PEBR drivers link forks of crossbeam in `kaist-cp/crossbeam` at two pinned commits; the EBR fork adds a global garbage counter that upstream crossbeam lacks.
- **Production implementations examined in source:** `crossbeam-rs/crossbeam` (`crossbeam-epoch`), `facebook/folly` (hazard-pointer domain), `urcu/userspace-rcu`, `torvalds/linux` (RCU requirements documentation).
- **Execution environment.** All execution results come from one shared cloud VM: 96 vCPUs, Intel Xeon @ 2.60 GHz, 236 GiB RAM, Linux. The 1-minute load average was 97–155 during runs because of other tenants. The repository pins Rust toolchain `nightly-2025-03-03`; the runs used `nightly-2025-03-02`. Results characterize these pinned revisions under that load; they do not generalize to other harness parameters.

Upstream revisions are as pinned in `REPORT.json`; the observations were made on 2026-11-21.

## Findings

### 1. Vocabulary that changes what a "bound" means

| Term | Meaning as used by the source | Source |
|---|---|---|
| retired node | `retire()` called, not yet unallocated; includes nodes merely not yet processed | ERA §5.1 |
| unreclaimable w.r.t. stalled set T | retired block that stays unreclaimed in *every* extension without steps by T | IBR §4.3.1 |
| robust (IBR, Hyaline) | ∀ history H, stalled set T, ∃k: \|unrec(H,T)\| < k (finite, may depend on H) | IBR §4.3.1; Hyaline fn. 4 |
| robust (ERA Def 5.1) | ∃ f_E with f_E = o(max_active_E) and retired(C_i) ≤ f_E(i)·N for all i | ERA §5.1 |
| weakly robust (ERA Def 5.2) | same, f_E polynomial in max_active_E | ERA §5.1 |
| fault-tolerant (Brown) | crashed processes can prevent only a bounded number of records from being reclaimed | DEBRA introduction |
| stalled vs. starving | stopped indefinitely, vs. running without completing; starving threads may reserve unboundedly in IBR/Hyaline-S unless operations restart | IBR §4.3.1; Hyaline fn. 4 |

Basis: normative (paper definitions). Consequence (derived): IBR is "robust" in its own sense but only *weakly* robust in ERA's sense, because its bound scales with `Emax`. The ERA paper states this classification explicitly.

### 2. Per-scheme bounds

| Scheme | Stated bound on unreclaimed objects | Depends on | Failure model | Status | Data-structure obligations |
|---|---|---|---|---|---|
| Hazard pointers (Michael 2004) | "upper bound on the number of removed nodes not yet freed at any time, regardless of thread failures and delays" (abstract). Restated: scan at nk+Ω(nk) retired ⇒ O(kn²) waiting (Brown); with threshold factor R=1, ≤ MAX_THREADS² × MAX_HPS (Ramalhete–Correia) | N, K, scan threshold | crash, stall | proved in original (body not read; relayed) | protect + validate every traversed pointer; Harris list must be restructured (Michael's variant) |
| EBR (Fraser 2004) | none: "the limbo lists will never be reclaimed and memory cannot be reused" if a process stalls inside an operation | — | any stall inside a critical region blocks | argued | begin/end op only |
| DEBRA (Brown 2015) | none under crash *inside* an operation; crash while quiescent does not block | — | partial fault tolerance | argued | begin/end op |
| DEBRA+ | "at most O(mn²) records are in the limbo bags"; m = largest number of records removed by one operation | n, m | crash, stall; requires OS signals delivered at next step | proved (paper) | recovery code after neutralization (`siglongjmp`) |
| NBR / NBR+ (2021) | Lemma 10: per thread, after a reclamation event at most k(p−1) records stay unreclaimed (Θ(kp)); Corollary 11 restates as Θ(p) treating k as constant. Derived total: ≤ p·(n_hi + k(p−1)) for limbo threshold n_hi | p, k, n_hi | stall, crash; signals | proved (appendix; informal) | split each operation into read and write phases; read phases restart (from root) on neutralization |
| Hazard Eras (2017) | "finite (equation 1)": number of objects x with x.newEra ≤ era ≤ x.delEra for some published era; no closed form | objects alive during published eras | threads that die after publishing an era | argued | like HP (indices per pointer) |
| IBR (POIBR/TagIBR/2GEIBR) | Theorem 2: unreclaimable ≤ `Emax × epoch_freq × num_threads` | Emax (absolute), epoch_freq, threads | stalled only; starving unbounded unless restart | proved | begin/end op + read/write wrappers |
| Hyaline / Hyaline-1 | none: "memory usage can become unbounded if some threads are stalled" | — | — | argued | enter/leave |
| Hyaline-S / -1S | Theorem 5: unreclaimable nodes ≤ `δEra × Freq × n(k+1)`, k ≤ n slots | era spread among stalled slots, Freq, n, k | stalled only | proved | `deref` wrapper; double-width CAS or LL/SC for Hyaline-S |
| Crystalline-L/-LW/-W (2024) | memory usage bounded, including starving threads for -L; wait-free -W | (no closed form found in text read) | stall, starvation | claimed with lemmas on loop bounds | `deref`; WCAS for -W |
| VBR (2021) | ERA states VBR robust with f constant (local retire list size) | retire-list size | stall | relayed | rollbacks at checkpoints; type-preserving allocator |
| PEBR (2020) | abstract: "a non-cooperative thread does not prevent the other threads from reclaiming an unbounded number of blocks" | — | non-cooperative thread | claimed (body not read) | restart after ejection; process-wide fence |
| HP-BRCU (2024) | `2GN + GN² + H`, G = MaxLocalTasks × ForceThreshold, H = shields | N, G, H | stall, long-running ops | proved (paper) | restart on revalidation failure; signals |

Basis: normative for each paper's own statements, documentation for relayed statements, derived where marked.

### 3. The ERA theorem: definitions, proof, and classifications

- **Easy integration (Def 5.3).** All five conditions must hold:
  - the scheme is an object;
  - its API calls appear only at operation entry/exit, as replacements for `alloc`/`retire`, or as replacements for primitive memory accesses;
  - each replaced access is a linearizable implementation of that primitive;
  - the integrated code is well formed, meaning no transfer of control from scheme code back into data-structure code (no rollbacks);
  - the scheme may add node fields but may not access the original ones.
- **Applicability (Def 5.4).** The integrated implementation must be memory-safe, remain linearizable, and preserve the plain implementation's progress guarantee. Wide applicability (Def 5.6) requires this for every "access-aware" implementation, the read-phase/write-phase class taken from NBR. EBR is *strongly* applicable (to every implementation; Appendix A).
- **Theorem 6.1 and proof shape.** T1 begins `delete(3)` and reads `head.next` (node 1). T2 then deletes 1 and loops `insert(n+1)`, `delete(n)`, so at most 4 nodes are ever active while nodes 1..n are retired, each marked and pointing to its successor. Weak robustness forces some node m ≤ n to be reclaimed once n > f·N. Condition 5 keeps the marked `next` chain intact, and Conditions 3 and 4 force T1's solo traversal to follow it until it dereferences m's freed memory without an intervening update, which contradicts safety.
- **Stated scope (discussion):** the impossibility already holds for Harris's list alone, so any weaker applicability notion that includes that list inherits it.

| Scheme | Robust | Easy integration | Wide applicability | Who classifies |
|---|---|---|---|---|
| EBR | no (not even weak) | yes | yes (strong) | ERA |
| HP | yes, if #hazard pointers = o(active nodes) | yes | no (Appendix E) | ERA |
| IBR | weak only | yes (rollback-free variant) | no | ERA |
| HE | not stated | not stated | no | ERA |
| NBR | yes (same hazard-pointer caveat) | no | yes | ERA |
| VBR, AOA | yes | no | not stated | ERA |
| Crystalline | yes | yes | no | Crystalline authors |
| HP-BRCU | yes | no | supported on all 19 structures in its Table 1 (5 without preserving wait-freedom) | HP-BRCU authors |
| Hyaline-1S | yes (Theorem 5) | inferred yes (`deref` wrapper) | no | Crystalline authors (wide); robustness from Hyaline |
| DEBRA+, PEBR | bounded | inferred no (recovery or restart code) | not classified | derived here |

Two caveats about self-containment: the ERA paper notes that several schemes rely on platform features outside its model, namely signals (DEBRA+, NBR), wide CAS (VBR, Hyaline), transactional memory (StackTrack, ThreadScan) and process-wide fences (Dice et al., PEBR).

### 4. Hybrids: what is traded

- **PEBR (source, `kaist-cp/crossbeam` pebr fork).** When forcing epoch advance, a participant pinned in an older epoch is ejected (`local.eject(...)`), and its shields are merged into a summary. A stalled participant therefore protects only its shielded pointers. An ejected participant learns of ejection through `ShieldError::Ejected` and must repin and restart.
- **HP-RCU / HP-BRCU (paper).** Traversals alternate RCU phases with hazard-pointer handoffs, which removes per-node protection cost in RCU phases. BRCU bounds RCU-phase duration by rarely sending signals, which makes stalled threads safe. The quadratic term GN² arises "only in a pessimistic case that every thread is reclaiming nodes at the same time". The authors report measured peaks "well below" that bound and a memory footprint comparable to HP and HP++.
- **NBR vs DEBRA+.** NBR restarts only threads in a read phase; DEBRA+ restarts any non-quiescent thread. The HP-BRCU authors report that NBR "shows performance degradation after reaching 56 threads due to frequent neutralization signals" and that NBR, VBR and PEBR "severely suffer from frequent operation restarts" on long-running reads with key ranges up to 2²⁹.

### 5. How harnesses measure deferred memory

| Harness | Metric | Stall / oversubscription treatment | Source |
|---|---|---|---|
| IBR repo (`parharness`) | at the start of each operation the thread adds its *local* retired-unreclaimed count; reported as average per operation | threads > 72 cores "certain to be stalled" (oversubscription as stall proxy) | `src/rideables/SortedUnorderedMap.hpp` calls `collect_retired_size(memory_tracker->get_retired_cnt(tid), tid)`; paper §5 |
| lfsmr (Hyaline) | same harness (`benchmark/ext/parharness`); "retired objects per operation"; ships recorded CSVs `benchmark/data/hyaline_data/*_result_retired*.csv` | up to 144 threads on 72 cores; epochf=150, emptyf=120, k=128 slots, batch 64..k+1 | Hyaline §6 |
| Crystalline eval | retired objects per operation; prefill 50,000, 10 s, 5 runs | up to 192 threads (4× Xeon E7-8890 v4) | PLDI'24 §6 |
| setbench (NBR) | peak memory usage; jemalloc | one thread begins an operation and sleeps for the 25 s trial | NBR §7 E2 |
| smr-benchmark | jemalloc `stats.allocated` sampled every 1 ms (peak, average); "garbage" from scheme counters | `-n 1/2/3` (repin every 1 ms / 10 ms / never) implemented only for EBR and PEBR | `src/config/map.rs` (non-coop flag; `non_coop_period`), `src/bin/ebr.rs` (aux thread) |

Pitfalls found in source (Basis: source):

- smr-benchmark's VBR driver hard-codes `let garb_acc = 0usize; let garb_peak = 0usize;` (`src/bin/vbr.rs`), so "peak garb: 0" for VBR means *not reported*, not zero garbage.
- The EBR fork's `GLOBAL_GARBAGE_COUNT` is incremented when a full bag is pushed to the global queue and decremented when a sealed bag is destroyed (`crossbeam-epoch/src/internal.rs` in the fork), so thread-local unsealed bags (capacity 512 with `-b small`) are excluded.
- Average-per-operation metrics, as used in the IBR, Hyaline and Crystalline evaluations, hide worst cases. The Crystalline authors note that for HE and WFE "the worst-case (as opposed to average-case) number of unreclaimed objects is much higher than in HP".

### 6. Execution probe: one stalled participant (smr-benchmark)

Configuration: `-d hash-map -t 32 -g 0 -r 100000`, write-only (50% insert, 50% remove), with jemalloc. Script and raw outputs are in `support/`. Basis: execution of the pinned harness. All values come from the harness's own summary line.

| Scheme | Stall flag | Run length | Peak garbage (objects) | Peak allocated |
|---|---|---|---|---|
| EBR | none (`-n 0`) | 10 s ×3 | 699,392 / 1,004,544 / 1,411,072 | 51.3–91.4 MiB |
| EBR | repin 1 ms / 10 ms | 10 s | 605,184 / 1,161,216 | 42.3 / 77.0 MiB |
| EBR | stalled (`-n 3`) | 5 s | 86,872,703 | 5.19 GiB |
| EBR | stalled | 10 s ×3 | 143,244,288 / 169,788,139 / 208,203,264 | 8.55 / 10.14 / 12.43 GiB |
| EBR | stalled | 20 s | 341,233,011 | 20.37 GiB |
| PEBR | none | 10 s ×3 | 243,712 / 264,704 / 287,744 | 18.1–20.3 MiB |
| PEBR | stalled | 5 / 10 (×3) / 20 s | 248,832 / 247,296–280,576 / 229,376 | 17.8–20.2 MiB |
| HP / HP++ / NBR+ (threshold 256) / HP-BRCU | none (stall flag unsupported) | 10 s | 30,313 / 40,032 / 15,454 / 38,413 | 15.9 / 26.3 / 8.0 / 17.2 MiB |
| VBR | none | 10 s | not reported (hard-coded 0) | 10.3 MiB |
| no reclamation | — | 10 s | n/a | 5.74 GiB |

Derived from these runs:

- **Growth rate.** Stalled EBR grows at 86,872,703/5 s = 17.4 M objects/s and 341,233,011/20 s = 17.1 M objects/s, which is linear in time and consistent with "no bound".
- **Cost per object.** Allocated bytes ÷ garbage = 64.1 bytes per deferred object in all five stalled runs (for example, 10,887,362,384 / 169,788,139).
- **Stalled EBR versus no reclamation.** At 10 s, stalled EBR held more memory than the no-reclamation baseline (8.55–12.43 GiB vs 5.74 GiB). This is consistent with each deferred object costing about 64 B (node plus deferral record) at throughput in the same range; the bare node size was not measured separately.

Not established by this probe:

- bounds for HP, NBR, HP-BRCU or VBR *under a stall*, because the harness's stall flag covers only EBR and PEBR;
- scheme throughput rankings, because the host load averaged above its vCPU count.

### 7. Production implementations: limit type

| Implementation (pinned) | Mechanism | Corresponds to a proved bound? |
|---|---|---|
| crossbeam-epoch | 64 deferred functions per bag (`MAX_OBJECTS`); a sealed bag is freed when `global_epoch.wrapping_sub(self.epoch) >= 2`; `collect()` pops at most `COLLECT_STEPS = 8` bags; `pin()` collects every `PINNINGS_BETWEEN_COLLECT = 128` pins; `try_advance` returns without advancing if any pinned participant's epoch differs | no bound. Derived: pin-triggered collection reclaims ≤ 8×64 = 512 objects per 128 pins per thread (4 per pin), so a thread retiring more than 4 objects per pin depends on flushes and other threads |
| Folly `hazptr_domain` | reclaim when `rcount >= max(kThreshold=1000, kMultiplier=2 × hcount)` or every `kSyncTimePeriod` = 2 s; 8 shards; `kListTooLarge = 100000` used by cohort cleanup | heuristic resembling Michael's R = H + Ω(H). Derived: each threshold-triggered pass can free ≥ rcount − hcount ≥ hcount objects when the 2H term dominates |
| urcu `defer_rcu` | per-thread queue of `DEFER_QUEUE_SIZE (1 << 12)`; when `head - tail >= DEFER_QUEUE_SIZE - 2` the caller runs `rcu_defer_barrier_thread()` → `synchronize_rcu()` | bounded memory (≤ 4096 entries ≈ 32 KiB of pointers per thread, derived) bought by blocking the retiring thread |
| urcu `call_rcu` | wait-free queue; `qlen` "maintained for debugging"; helper threads splice whole batches | none |
| Linux RCU | if a grace period exceeds 100 ms, `cond_resched()` reports quiescent states; 109 ms `resched_cpu()` on `nohz_full`; 500 ms priority boost (`CONFIG_RCU_BOOST`); 10 s `resched_cpu()`; at 10,000 callbacks per CPU, force QS checks and lift batch limits; `rcu_barrier()` waits for in-flight callbacks | none: "These mechanisms are not foolproof, nor can they be", since an infinite loop in a read-side critical section "must by definition prevent later grace periods from ever completing" |

Basis: source (crossbeam, folly, urcu) and documentation (Linux `Requirements.rst`). Desnoyers et al. state the liveness premise that grace periods complete "as long as all read-side critical sections are finite in duration", which is a liveness assumption, not a space bound.

### 8. Six-level cost profile

| Level | Finding | Basis |
|---|---|---|
| L1 authoring | Obligations by scheme: EBR, 2 call sites per operation. HP, protect and validate each traversed pointer, plus data-structure redesign for Harris-style lists. NBR, read/write phase split and restart. DEBRA+, recovery code. HP-BRCU/PEBR/VBR, restart paths. LoC, person-months and token budgets: not measured. | papers |
| L2 build | smr-benchmark release build of 8 drivers: 66 s wall, 6 min 16 s user; incremental build of 6 more drivers: 19.6 s wall | execution |
| L3 compile/elaboration latency | not measured | — |
| L4 execution | DEBRA overhead vs. leaky: average 10%, worst 28% on a BST; DEBRA+ fault tolerance adds 2.5% on average. Hyaline up to 2× over Epoch at 81 threads (oversubscribed). NBR+ over HP 2× and over IBR > 50% when oversubscribed. RCEBR (automatic counting over EBR) within 10% of EBR at 144 threads (Anderson–Blelloch–Wei 2022). Probe throughputs: not interpretable (load). | papers; execution |
| L5 proof checking | Bounds are paper proofs; no mechanized proof of any bound examined; checker speed not applicable | — |
| L6 memory | 64.1 B per deferred object under stalled EBR (probe). Header words per object: EBR/HP 1, IBR/HE/Hyaline/Crystalline 3 (Crystalline Table 1). HP/HE/IBR scan snapshots "2.5 MB" for 144 threads × 16 pointers (derived as 144·144·16·8 B = 2,654,208 B, assuming each thread snapshots all slots). urcu defer queue 32 KiB/thread (derived). Energy: not measured. | execution; papers; derived |

### 9. Comprehensibility and a unifying model

- **C1 (human comprehension).** EBR has one concept (critical section), but its failure mode is nonlocal: a sleeping reader anywhere inflates memory everywhere, and nothing in the code at the allocation site signals it. HP keeps reasoning local (only protected pointers are held) but makes each traversal step a protocol with a validation re-read. Rollback-based robust schemes (DEBRA+, NBR, VBR, PEBR, HP-BRCU) introduce nonlocal control transfer (`siglongjmp`, ejection errors). The ERA theorem shows this burden is unavoidable for robust and widely applicable schemes, not an engineering accident. Bugs manifest only under stalls, which ordinary tests rarely produce.
- **C2 (one model).** Every scheme decides reclaimability with a reservation predicate over each retired object's lifetime interval [birth, retire]:
  - EBR reserves every object retired at or after the oldest pinned epoch, an unbounded set;
  - HP reserves explicitly named addresses;
  - HE/IBR reserve objects whose interval intersects a reserved era interval;
  - Hyaline replaces scanning with reference counts on batches;
  - neutralization and ejection shrink a stalled thread's reservation to its explicit shields.

  Under this reading (derived), a bound is |{retired x : reserved(x)}|, and the ERA witness is a reservation that must cover an unbounded chain of retired, still-linked nodes. The model is a synthesis for comparison, not a theorem from the sources.

### 10. Validation of the claims (V1–V4)

- **V1 (specification adequacy).** The two robustness definitions are not equivalent: IBR satisfies its own definition but not ERA's strong one. NBR's Corollary 11 restates Lemma 10's Θ(kp) as Θ(p) by treating k as a constant. Readers should check which statement they rely on. Mutation or non-vacuity testing of these definitions: not examined.
- **V2 (implementation testing).** smr-benchmark documents AddressSanitizer runs with stress parameters. crossbeam-epoch shrinks `MAX_OBJECTS` to 4 under `crossbeam_sanitize`/`miri` "to trigger any potential data races". Differential testing across schemes: not examined.
- **V3 (concurrency and platform).** DEBRA+ requires that a signalled process "will execute its signal handler" at its next step and cites Linux as satisfying this. NBR and HP-BRCU depend on the same OS behaviour. Weak-memory model checking (for example GenMC or Loom) of these schemes: not examined.
- **V4:** not applicable (no plant or operator model). The probe is a real-harness stall test, but only for EBR and PEBR.

## Boundaries

- **Not examined.**
  - The full text of Michael 2004 (only the abstract sentence and third-party restatements). PEBR (abstract plus fork source). VBR's DISC 2021 full paper (ERA's classification and the arXiv abstract only). Hart et al. 2007 (no text obtained).
  - The SPAA 2017 Hazard Eras brief announcement itself: the extended version may differ.
  - The ERA paper's PODC version: the arXiv v1 preprint was read, and Appendix E's proofs that HP, IBR and HE are not widely applicable were not checked line by line.
  - The Folly thread-local retire caches; Linux RCU source code beyond `Requirements.rst`; `rcubarrier.rst` beyond its role as a barrier.
- **Unknown.**
  - A closed-form bound for Crystalline-L/-LW/-W: the text read gives loop-bound lemmas and "bounded memory usage" claims, not a formula.
  - Whether HE's equation (1) is bounded by any function of N and slots alone; the authors say it "may be higher, or lower than the bound for HP".
  - Whether smr-benchmark's PEBR result (≈0.25 M deferred objects, flat in time) would remain flat on an unloaded host or with more threads.
- **Known not to apply.**
  - IBR's and Hyaline-S's bounds do not cover starving threads unless operations restart, by the authors' own footnotes.
  - Plain DEBRA's partial fault tolerance does not cover a crash *inside* an operation.
  - urcu's `defer_rcu` bound does not preserve non-blocking progress.
- **Unsupported.**
  - smr-benchmark's `-n` stall modes for any scheme other than EBR and PEBR.
  - VBR garbage counts in that harness.
- **Stronger conclusions not established:**
  - that stall-free garbage peaks in the probe rank the schemes, since a single host under external load was used;
  - that any production library offers a proved bound;
  - that the ERA theorem forbids practical schemes, since it forbids only the conjunction of three formally defined properties.

## Evidence

- **Literature.** DOIs were verified against Crossref metadata on 2026-11-21: Michael `10.1109/TPDS.2004.8`; Hart et al. `10.1016/j.jpdc.2007.04.010`; Desnoyers et al. `10.1109/TPDS.2011.159`; Brown `10.1145/2767386.2767436`; Ramalhete–Correia `10.1145/3087556.3087588`; Wen et al. `10.1145/3178487.3178488`; Nikolaev–Ravindran `10.1145/3293611.3331575`, `10.1145/3453483.3454090`, `10.1145/3332466.3374540` (WFE), `10.1145/3658851`; Kang–Jung `10.1145/3385412.3385978`; Singh–Brown–Mashtizadeh `10.1145/3437801.3441625`; Sheffi–Herlihy–Petrank `10.1145/3409964.3461817`; Sheffi–Petrank `10.1145/3583668.3594564`; Kim–Jung–Kang `10.1145/3626183.3659941`; Jung et al. HP++ `10.1145/3558481.3591102`; Dice–Herlihy–Kogan `10.1145/2926697.2926699`; Cohen–Petrank `10.1145/2814270.2814298`; Anderson–Blelloch–Wei `10.1145/3519939.3523730`. The following were verified through the doi.org handle API plus DataCite metadata instead, because these registrations are not in Crossref: Fraser, *Practical lock-freedom*, UCAM-CL-TR-579, `10.48456/tr-579`; VBR full paper `10.4230/LIPIcs.DISC.2021.35` (LIPIcs 209, 35:1–35:18). arXiv records read: 2211.04351, 1712.01044, 2012.14542, 1905.07903, 2107.13843, 2108.02763.
- **Key passages.**
  - ERA: Definitions 5.1–5.6, Theorem 6.1 and its proof, Appendix A.
  - DEBRA abstract and §5 (O(mn²); signal requirement). NBR Lemma 3, Lemma 10, Corollary 11, §7 E2.
  - IBR Theorem 2 and §5. Hyaline Theorems 3–5 and §6. HE §3.1 equation (1) and Table 1. HP-BRCU §5 (bound) and §6. Crystalline Table 1 and §§6–7.
  - Fraser §5.2.3. Desnoyers et al., RCU overview (grace-period definition).
- **Source** (repository@revision as pinned in `REPORT.json`):
  - `crossbeam-rs/crossbeam` `crossbeam-epoch/src/internal.rs`: L64–69 `MAX_OBJECTS`; L155–161 `is_expired`; L178 `COLLECT_STEPS`; L208–226 `collect`; L237–293 `try_advance`; L340 `PINNINGS_BETWEEN_COLLECT`; L459–463.
  - `facebook/folly` `folly/synchronization/HazptrDomain.h`: L45–47, L125–128, L369–373, L376–386, L401–428.
  - `urcu/userspace-rcu`: `doc/rcu-api.md` L95–135; `src/urcu-defer-impl.h` L41–45, L244–253, L315–324; `src/urcu-call-rcu-impl.h` L52, L718–727.
  - `torvalds/linux` `Documentation/RCU/Design/Requirements/Requirements.rst` L1411–1487, L1565–1580.
  - `kaist-cp/smr-benchmark`: `README.md` L175–204; `src/config/map.rs` L203–210, L355–364; `src/bin/ebr.rs` L112–116, L127–180; `src/bin/vbr.rs` L127–128.
  - `kaist-cp/crossbeam` EBR fork `crossbeam-epoch/src/internal.rs` L57, L194, L236; PEBR fork `crossbeam-epoch/src/internal.rs` L295–327 (ejection).
  - `urcs-sync/Interval-Based-Reclamation`: `src/RetiredMonitorable.hpp`, `src/trackers/BaseTracker.hpp` L43–51, `src/rideables/SortedUnorderedMap.hpp` L118.
  - `rusnikola/lfsmr`: `benchmark/` tree listing.
  - `pramalhe/ConcurrencyFreaks` `papers/hazarderas-2017.pdf` §3.1.
- **Execution (2026-11-21).**
  - Build: `git clone https://github.com/kaist-cp/smr-benchmark && git checkout 00b4e4d06d9b91f289b4644163f0cac0660d4af7 && RUSTUP_TOOLCHAIN=nightly-2025-03-02 cargo build --release --bin ebr --bin pebr --bin hp --bin nbr --bin hp-brcu --bin vbr --bin nr --bin hp-pp`.
  - `Cargo.lock` resolved the EBR fork to `ee760604650f37e9bef5ebcd55a1c6403c6dfe0c` and the PEBR fork to `8c4b969c866a7d1b1c698f6b374e781615efb8c8` (branches `smr-benchmark` and `pebr` of `kaist-cp/crossbeam`).
  - Runs: `support/run_smr_probe.sh target/release out`. Outputs: `support/smr_stall_probe_log.txt`, `support/smr_stall_probe.csv` (exact byte counts), `support/probe_env.txt` (timestamps, load averages).

## Revalidation

1. **Stall behaviour (about 2 minutes plus the build).** `./target/release/ebr -d hash-map -t 32 -g 0 -r 100000 -n 3 -i 5` and the same with `-i 10`. The finding holds if peak garbage roughly doubles between the two runs, and if `pebr` with the same flags stays within a small constant factor of its `-n 0` value.
2. **Production limits.** Diff the cited line ranges at a new revision: `MAX_OBJECTS`, `COLLECT_STEPS`, `PINNINGS_BETWEEN_COLLECT` and `is_expired` in crossbeam-epoch; `hazptr_domain_rcount_threshold`, `kMultiplier` and `kSyncTimePeriod` in Folly; `DEFER_QUEUE_SIZE` and the full-queue branch in urcu; the "Forward Progress" section of `Requirements.rst`. Any change to these constants invalidates the derived figures in §7.
3. **Harness accounting.** Check that `src/bin/vbr.rs` still hard-codes zero garbage and that the EBR fork still counts only sealed bags before comparing "peak garb" across schemes.
4. **Theory.** Re-read ERA Definition 5.3 Conditions 4–5 and the Theorem 6.1 proof in the published PODC version; a changed definition changes every classification in §3.
