# Deferred, coalesced, lazy, and concurrent-deferred reference counting: which count operations are postponed, the proved space cost of lazy freeing, reclamation delay, and measured memory held by deferral (LXR, CDRC/CIRC, free-threaded CPython)

## Summary

- **Four separate postponement mechanisms.** In Blackburn–McKinley's taxonomy:
  - *deferral* means some pointers (classically stack and register roots) generate no count operations at all, so a retain event (a zero-count table, ZCT, or temporary increments) must protect their referents until the next RC phase;
  - *buffering* changes only when increments and decrements are applied, not whether;
  - *coalescing* (Levanoni–Petrank) applies only the before and after images of each mutated slot per period;
  - *lazy freeing* postpones the recursive deletion that follows a zero count.

  Each mechanism holds memory past the program's last reference, for a different reason and for a different length of time.
- **Proved space results are few and worst-case.** Boehm (POPL 2004) proves that if every reference-count operation must take constant time, lazy deletion can raise space requirements by Ω(R) in the worst case, where R is the ratio of largest to smallest object size. The bound is achievable, and is avoided if allocating an n-byte object may do O(n) counting work. CDRC (PLDI 2021, Theorem 1) proves O(P²) space overhead and O(P²) deferred decrements for P processes. That bound counts *decrements*, not unreclaimed objects, and excludes the cost of the deletes they trigger. Bacon–Cheng–Rajan's cost model notes that a ZCT can contain as many entries as there are live plus dead objects.
- **Reclamation delay is mostly argued or measured, not bounded.**
  - Levanoni–Petrank prove safety and that their collector "eventually reclaims all unreachable objects". Zero-count objects that are locally referenced or "snooped" are passed to the next cycle.
  - The CIRC authors identify the *garbage-chain* problem: with deferred decrements, node i+1 of a dead chain is considered only after node i is reclaimed in a later reclamation batch, so a backlog can grow without bound.
- **Measured on a real harness (`kaist-cp/smr-benchmark` DoubleLink queue, 32 threads).** CDRC over EBR peaked at 2.66 / 5.70 / 11.57 GB after 5 / 10 / 20 s. That is above the never-reclaim baseline (2.18 / 4.85 / 8.08 GB), while plain EBR stayed at 0.01–0.20 GB. CIRC over EBR grew more slowly (0.58 / 1.02 / 1.71 GB). On this heavily loaded host CIRC over hazard pointers also grew (2.56 / 4.36 / 10.19 GB), which conflicts with the CIRC paper's report that its memory does not grow over time; the cause was not isolated.
- **Free-threaded CPython defers counting only for selected objects, which only the cyclic GC can free.** Measured at the pinned CPython revision (3.16.0a2+, built both ways): with automatic GC disabled, all 200,000 dropped top-level function objects stayed alive until `gc.collect()`, about 232 B each. With default GC thresholds, 11,376 were still alive at loop end. A nested-function control and the GIL build retained 0. PEP 779 reports 15–20% higher total memory for the free-threaded build (pyperformance geometric mean) but does not attribute it to deferral.
- **High-performance counting collectors limit deferral by pause-time policy.** LXR processes decrements lazily and concurrently after each brief pause. The paper reports pauses that had to finish leftover lazy decrements in xalan (21% of pauses), lusearch (5%) and avrora (1%), and stuck (saturated) counts of 0–1% in 16 of 17 benchmarks (batik 6.6%). The mmtk-core implementation enables lazy decrements by default and uses 2-bit counts.

## Applicability

The report covers memory held by postponed reference-count work in tracing/counting hybrids for managed languages (Java-family collectors), in concurrent counting libraries for unmanaged languages (C++/Rust), and in a free-threaded CPython design.

Subjects and how they relate:

- **Papers.**
  - Read in full text: Levanoni–Petrank (TOPLAS 2006 version, from the author's site); Blackburn–McKinley 2003 (author PDF); Bacon–Cheng–Rajan 2004 (a course-hosted copy of the OOPSLA paper); Anderson–Blelloch–Wei 2021 (author PDF of the PLDI paper) and 2022 (arXiv 2204.05985); Zhao–Blackburn–McKinley 2022; Jung–Kim–Parkinson–Kang 2024 (author PDF).
  - Abstract only: Boehm 2004, via an index record of the ACM abstract.
  - Not read; described only through the papers above, and marked as such: Deutsch–Bobrow 1976, Bacon et al. 2001, Shahriyar et al. 2012/2013, Lins 1992.
- **Implementations (source).**
  - `cmuparlay/concurrent_deferred_rc`, the header-only C++ CDRC library: `include/` examined in source; its `benchmarks/` and `results/` were not built or run.
  - `kaist-cp/smr-benchmark`, which contains Rust ports of CDRC and CIRC (`smrs/cdrc`, `smrs/circ`): executed.
  - `mmtk/mmtk-core` `src/plan/lxr/`; `python/cpython` (QSBR and deferred counting); `python/peps` (PEP 703, PEP 779).
- **Execution environment.** One shared cloud VM: 96 vCPUs, Intel Xeon @ 2.60 GHz, 236 GiB RAM, Linux. The 1-minute load average was 97–155 from other tenants during the DoubleLink runs. Rust `nightly-2025-03-02` was used; the repository pins `nightly-2025-03-03`. CPython was built from the pinned commit with GCC 15.2.0 twice: `--disable-gil` and default. Results characterize these revisions on this host only.

Upstream revisions are as pinned in `REPORT.json`; evidence was gathered on 2026-11-21.

## Findings

### 1. What each design postpones, and when the work is done

| Design | Deferred (no count ops) | Buffered / coalesced | When processed | Stated delay to reclamation | Status |
|---|---|---|---|---|---|
| Deutsch–Bobrow 1976 (as described by Blackburn–McKinley and Bacon–Cheng–Rajan) | stack and register references | single buffer of count operations | RC phase: scan roots, free ZCT entries not root-referenced | until the next RC phase | relayed |
| Temporary-increment deferral (Bacon et al., relayed) | roots | separate increment and decrement buffers; all increments before any decrement | each RC phase; matching decrement applied at the *next* phase | ≥ one phase for root referents | relayed |
| Levanoni–Petrank 2001/2006 | locals (ZCT, "marked local") | slots logged once per cycle (dirty bit); decrement old image, increment final value | on-the-fly cycle with four soft handshakes | zero-count locally referenced or snooped objects go to the *next* cycle's ZCT; "eventually reclaims all unreachable objects" | proved (safety, liveness) |
| Ulterior RC / BG-RC 2003 | roots, plus all pointers in a bounded copying nursery | coalescing for mature RC space | nursery collection; "integrate" event increments survivors' referents | young garbage reclaimed by copying at nursery collection; mature by RC after it | measured |
| LXR 2022 | roots (increment at tₙ, decrement at tₙ₊₁); young objects never get counts unless they survive | coalescing write barrier; increments in the pause, **decrements lazily and concurrently** after it | brief RC pauses; concurrent SATB trace for cycles | lazy decrements affect "promptness only of mature object reclamation"; leftover decrements are finished before the next epoch | measured |
| CDRC 2021 | none for heap links; *snapshots* act as deferred increments | decrements retired through acquire–retire (a generalization of hazard pointers allowing multiple retires) | when the retire is ejected (no protecting announcement) | each link of a dead chain waits for its own ejection (garbage chain, per CIRC) | proved O(P²) deferred decrements |
| Automatic SMR-backed RC 2022 | as CDRC, over EBR, IBR, Hyaline | deferred decrements | per underlying scheme | "each retired pointer could recursively prevent the collection of many nodes beyond the one it directly points" | measured |
| CIRC 2024 | as CDRC | **decrements immediate**; only reclamation deferred, one deferred task per object, with recursive destruction of chains using epoch timestamps | underlying SMR (EBR or HP) | chain reclaimed in one task in the common case | measured |
| Free-threaded CPython (PEP 703, source) | interpreter-stack references to *deferred* objects (PEP 703 lists top-level functions, code objects, modules, methods, heap types; confirmed in source for functions, `classmethod`/`staticmethod` wrappers and modules) | biased counting merges; QSBR delays frees of shared list and dict storage and mimalloc page reuse | deferred objects: cyclic GC only; QSBR items: when all attached threads pass a quiescent state | unbounded between GC passes for deferred objects | documented + measured here |

Basis: normative statements of each paper, documentation (PEP 703), source (CPython), derived where marked "relayed".

### 2. Space and delay results with their conditions

- **Boehm 2004 (worst case; abstract read).** The model is lazy deletion, "deferring deletions and associated reference count decrements, usually to allocation time".
  - Result: with constant-time count operations, space can grow by a factor Ω(R), where R = size of largest object / size of smallest object. The bound is achievable.
  - Mitigation: allow O(n) counting work per n-byte allocation, which largely removes the cost.
  - The paper also measures classic RC pauses "longer" than tracing.
  - Applies to: any design that frees lazily with a fixed per-allocation work quota. LXR's lazy decrements are instead bounded by pause-to-pause scheduling (the next pause finishes them), so Boehm's constant-time premise does not apply directly (derived).
- **Bacon–Cheng–Rajan 2004 (cost model).**
  - Deferred RC moves root handling "from the application to the collector". Examining roots and removing their referents from the ZCT "is tracing".
  - Costs: κ(CD) = L(R) + L(V_D, E_D) per collection; collection frequency φ = a / V_D (allocation rate over free space); space σ(CD) = (V/ω)(1 + log₂V).
  - The ZCT "can equal the total number of live and dead objects", so "robust implementations use a bit in each object".
  - Reading (derived): the deferral period, and with it the memory that deferral holds, is set by heap headroom V_D. Halving headroom doubles RC-phase frequency.
- **CDRC Theorem 1 (proved; proof "deferred to the full paper").** On P processes: pointers are single words; `load` takes O(1); `store` and `cas` take O(1) expected time "excluding the cost of any call to delete resulting from a decrement"; there are "O(P²) space overhead and O(P²) deferred decrements"; only single-word primitives are used.
  - This does not bound the objects that become reclaimable through those decrements, nor how many batches a dead chain needs (derived from the statement's scope; empirically confirmed in §4).
- **CIRC (argument plus measurement).** "Only after nodeᵢ is reclaimed can nodeᵢ₊₁ be considered for reclamation… the rate of collection may fall behind the rate of dequeuing, resulting in a buildup of garbage backlog." Eager deferred-task processing (the OrcGC style) is reported to cost throughput and still not fix memory.
- **CDRC library source (where the chain cost comes from).** In `include/cdrc/`, the destructor of an `atomic_rc_ptr` (a mutable shared link) calls `mm.delayed_decrement_ref_cnt(ptr)`, which `retire`s a decrement. The destructor of a plain `rc_ptr` calls `mm.decrement_ref_cnt(ptr)` immediately; if that zeroes the count, it destroys the object at once, or retires a `dispose` when weak references exist. Derived: a dead chain linked through plain `rc_ptr` fields is torn down recursively in one step, but one linked through `atomic_rc_ptr` fields (as in queues whose links are CAS-updated) needs one retire-then-eject round per link. This is the source-level form of the garbage-chain problem. Basis: source.
- **Levanoni–Petrank (proved).** Safety: "an object is recycled during cycle k only if it is unreachable". Liveness is qualitative. No cycle-count bound on delay was found in the text read.

### 3. Collector measurements reported by the papers

| Source | Configuration compared | Heap setting | Reported result |
|---|---|---|---|
| Ulterior RC (SPEC JVM98, Jikes RVM) | BG-RC vs BG-MS, MS, pure deferred RC | moderate heap = 1.5× minimum | BG-RC throughput on average 2% better than BG-MS at moderate heaps; maximum pause times "a factor of 4 lower on average" |
| Levanoni–Petrank (JVM 1.2.2, 4-way 550 MHz Pentium III Xeon) | vs. original mark-sweep-compact | — | pauses "drastically reduced (by two orders of magnitude)"; throughput reduced "by at most 8%" |
| LXR (DaCapo and others, OpenJDK) | LXR vs G1, Shenandoah, ZGC | 1.3× and 2× G1 minimum heap | leftover lazy decrements at pauses: xalan 21%, lusearch 5%, avrora 1%; stuck counts 0–1% in 16/17 benchmarks, batik 6.6%; Shenandoah "cannot keep up with lusearch's 9.5 GB/s" allocation |
| Anderson et al. 2022 (C++, 144 threads) | RCEBR, RCIBR, RCHyaline vs manual | — | RCEBR within 10% of EBR and RCHyaline within 15% of Hyaline throughput on BST; similar memory when not oversubscribed, "several times more" in linked list and oversubscribed runs |
| CIRC 2024 (smr-benchmark, AMD EPYC 7543 / Xeon 6248R) | CIRC vs CDRC vs EBR/HP | — | CIRC and CDRC add up to 20% and 30% throughput overhead to the underlying scheme in one figure pair, and CDRC-HP up to 58% in another configuration; CDRC "cannot promptly reclaim long linked structure" (SkipList, DoubleLink) |
| PEP 779 (pyperformance) | free-threaded vs GIL build | — | memory "about 15–20% higher" (geometric mean); proposed acceptance target 20%; not attributed to any mechanism |

Basis: documentation (paper and PEP statements). None of these sources report the smallest heap in which each design completes with and without deferral as a single comparable table. That reproduction was not run here.

### 4. Execution probe A: deferred decrements on a dead chain (DoubleLink queue)

Command: `double-link -m <mgr> -t 32 -i <s>` at `kaist-cp/smr-benchmark` (pinned). Memory is jemalloc `stats.allocated` sampled every 1 ms; values are peak bytes, shown in GB (10⁹ bytes); exact byte counts are in the CSV. Script and raw CSV are in `support/`. Basis: execution of the real harness, which includes Rust ports of CDRC and CIRC (not the C++ CDRC library).

| Manager | 5 s | 10 s (runs) | 20 s |
|---|---|---|---|
| no reclamation (`nr`) | 2.18 GB | 4.85 GB | 8.08 GB |
| EBR | 0.114 GB | 0.107 / 0.014 / 0.161 GB | 0.198 GB |
| CDRC over EBR | 2.66 GB | 5.70 / 5.86 / 5.85 GB | 11.57 GB |
| CDRC over EBR, flush per dequeue | 1.90 GB | 2.52 GB | 4.89 GB |
| CIRC over EBR | 0.58 GB | 1.02 / 0.39 / 0.99 GB | 1.71 GB |
| HP | 0.010 GB | 0.010 GB | 0.010 GB |
| CDRC over HP | 3.13 GB | 6.29 GB | 11.50 GB |
| CIRC over HP | 2.56 GB | 4.36 GB | 10.19 GB |

Derived:

- CDRC over EBR grows roughly linearly: 11.57 / 2.66 = 4.3× for 4× the time. It exceeded the never-reclaim baseline at every length (ratios 1.22, 1.18, 1.43), consistent with per-node count metadata plus deferred-decrement records accumulating faster than chains are drained.
- CIRC over EBR held 4.6–8.8% of CDRC over EBR's peak at matched lengths, but still grew with time on this host.
- Throughput (1.1–1.9 M ops/s) is not interpretable because the host load average exceeded its vCPU count.
- Not established: whether CIRC over HP grows on an unloaded host (the paper reports otherwise); the C++ CDRC library's behaviour.

### 5. Execution probe B: deferred reference counting in free-threaded CPython

Script: `support/deferred_rc_probe.py`. It creates and immediately drops 200,000 function objects with `types.FunctionType(code, {})`, then counts survivors through weak references and traced memory through the builtin `_tracemalloc`. Basis: execution of the real interpreter, built from the pinned commit.

| Build | Code object | Automatic GC | Alive after drop | Traced bytes after drop | Alive after `gc.collect()` |
|---|---|---|---|---|---|
| free-threaded | top-level (`CO_NESTED` clear) | disabled | 200,000 | 65,624,344 | 0 |
| free-threaded | top-level | enabled, thresholds (2000, 10, 10) | 11,376 | 21,871,808 | 0 |
| free-threaded | nested (`CO_NESTED` set) | disabled | 0 | 19,224,408 | 0 |
| GIL | top-level | disabled | 0 | 17,624,336 | 0 |
| GIL | top-level | enabled | 0 | 17,624,392 | 0 |
| GIL | nested | disabled | 0 | 17,624,336 | 0 |

Derived, using the free-threaded nested run as the baseline (it contains the same weak-reference list):

- (65,624,344 − 19,224,408) / 200,000 = 232.0 B retained per dropped top-level function, the function plus its fresh globals dict.
- With GC enabled, (21,871,808 − 19,224,408) / 11,376 = 232.7 B per survivor, which is consistent.
- The amount of memory held by deferral is therefore set by GC scheduling, not by the program's last use. Deferred objects are not freed by refcount at all.

Mechanism in source (CPython, pinned):

- `PyFunction_NewWithQualName` calls `_PyObject_SetDeferredRefcount` when `(co_flags & CO_NESTED) == 0 || (co_flags & CO_METHOD)`. The comment reads: "not nested functions because they are more likely to capture variables, which makes prompt deallocation more important".
- `_PyObject_SetDeferredRefcount` sets `_PyGC_BITS_DEFERRED` and initializes `ob_ref_shared = _Py_REF_SHARED(_Py_REF_DEFERRED, 0)`, with `_Py_REF_DEFERRED` defined as `(PY_SSIZE_T_MAX / 8)` in `Include/internal/pycore_object.h`. This bias keeps ordinary decrements from reaching zero.
- The free-threaded collector calls `disable_deferred_refcounting(op)` on unreachable objects "so that they are collected immediately after finalization". If it has seen a frame without a valid stack pointer (`skip_deferred_objects`), it keeps deferred objects alive (comment "GH-129236").
- **PEP vs. implementation (discrepancy).** PEP 703 says deferred objects "are marked by setting the two most significant bits in the local reference count field to one". The pinned source instead uses a GC bit plus the shared-count bias. Treat the PEP as design rationale, not as a layout specification. Basis: documentation vs. source.

Other deferral in the same interpreter (source):

- QSBR-delayed frees advance the global write sequence after more than `QSBR_DEFERRED_LIMIT = 127` items or `QSBR_FREE_MEM_LIMIT = 1024*1024` bytes per thread. The source comment says this "helps limit memory usage due to QSBR delaying frees too long".
- Deferred mimalloc page reuse advances after `QSBR_PAGE_MEM_LIMIT = 4096*20` bytes.
- Threads report quiescent states on eval-loop back-edges (`pycore_qsbr.h` comment); detached threads are offline (`QSBR_OFFLINE 0`).
- These are triggers for *attempting* reclamation, not bounds: a thread that stays attached without reaching a quiescent point delays all QSBR frees (derived from the polling design; not executed).

### 6. LXR in mmtk-core (source)

- `const LAZY_DECREMENTS: bool = !cfg!(feature = "lxr_no_lazy");`: lazy decrements are on by default.
- Recursive decrements are not performed inline. `ProcessDecs::recursive_dec` pushes children to a buffer, and a full buffer is flushed as a new work packet. Children are decremented only if `rc != MAX_REF_COUNT && rc != 0`.
- `src/util/rc.rs`: `LOG_REF_COUNT_BITS = 1` ⇒ `REF_COUNT_BITS = 2` ⇒ `MAX_REF_COUNT = 3`. Counts saturate ("stick") at 3, and saturated objects are left to the backup trace.
- Policy constants (with their comments): `RC_STOP_PERCENT = 15` ("trigger Full GCs instead if the available heap after a RC pause is still small"), `TRACE_THRESHOLD = 20`, `CYCLE_TRIGGER_THRESHOLD = 1024` (available pages).
- Deferral is therefore bounded operationally: the next RC pause drains the backlog, and low headroom escalates to concurrent marking or a full GC. No proved space bound is stated.

### 7. Six-level cost profile

| Level | Finding | Basis |
|---|---|---|
| L1 authoring | CDRC and automatic RC remove manual `retire` calls (the CDRC paper highlights the code they delete). CIRC needs no user changes over CDRC's interface. CPython deferral is invisible to Python code but changes destruction timing for top-level functions. LoC, person-months and token budgets: not measured. | papers; source |
| L2 build | smr-benchmark: 6 extra drivers in 19.6 s wall (incremental). CPython `configure && make -j24 python`: 52.7 s wall, max RSS 326,568 KiB as reported by GNU `time` (free-threaded); 51.6 s, 317,792 KiB (GIL) | execution |
| L3 compile latency | not measured | — |
| L4 execution | Paper-reported overheads in §3. Probe throughputs not interpretable (host load) | papers |
| L5 proof checking | CDRC's Theorem 1 proof is deferred to a full paper; Levanoni–Petrank's proofs are on paper; no mechanized proof examined | — |
| L6 memory | DoubleLink peaks in §4; 232 B per deferred-retained CPython function (derived); CPython free-threaded build 15–20% more memory overall (PEP 779); LXR 2-bit counts in side metadata (source); ZCT presence bit per object (cost model). Energy: not measured | execution; documentation; source |

### 8. Comprehensibility and a unifying model

- **C1 (human comprehension).** Programmers reason about counting as "freed at last release". Every mechanism here breaks that model in a different, invisible way:
  - deferral: freed at the next RC phase or GC;
  - coalescing: intermediate referents never counted;
  - lazy freeing: freed at a later allocation;
  - concurrent deferral: freed after ejection, per chain link;
  - CPython: top-level functions freed only by GC, nested ones promptly.

  The CPython rule is local and syntactic (`CO_NESTED`) but surprising. A program that drops many dynamically created top-level functions or modules accumulates them until a GC pass, and finalizers run late. Diagnostics: weak references and `gc.collect()` reveal it; nothing at the drop site does.
- **C2 (one model).** All mechanisms fit "count = heap-visible references + an over-approximation term reconciled at a scheduled point":
  - the ZCT and temporary increments over-approximate roots;
  - CPython's `_Py_REF_DEFERRED` bias over-approximates interpreter-stack references;
  - CDRC snapshots and announcements over-approximate in-flight increments;
  - lazy freeing over-approximates liveness of zero-count subgraphs.

  The memory held is the set whose true count is zero but whose over-approximation has not yet been reconciled. The designs differ only in the reconciliation trigger (root scan, GC pass, ejection, allocation quota, pause) and in whether reconciliation of a chain is one step (CIRC, recursive deletion inside a pause) or one step per link (CDRC). This is a synthesis for comparison, not a theorem from the sources.

### 9. Validation (V1–V4)

- **V1 (specification adequacy).** CDRC's theorem quantifies deferred decrements; users who read it as a bound on unreclaimed memory are contradicted by §4 (derived). PEP 703's layout description is contradicted by the pinned source (§5). Spec-mutation testing: not examined.
- **V2 (implementation testing).** smr-benchmark documents AddressSanitizer runs. It notes that sanitizer leak reports for CIRC-EBR are false positives caused by epoch bits in high pointer bits. The CIRC paper reports a bug in CDRC's weak-reference algorithm, later fixed by Parkinson et al. 2023 (not examined), and states that its own CDRC port does not include the fix. Differential testing: not examined.
- **V3 (concurrency).** Weak-memory model checking of CDRC, CIRC or CPython QSBR: not examined.
- **V4:** not applicable.

## Boundaries

- **Not examined.**
  - The full texts of Deutsch–Bobrow 1976, Bacon et al. 2001, Shahriyar et al. 2012 and 2013, Lins 1992, and Boehm 2004 (abstract only). Claims about them are relayed from later papers that describe them.
  - CDRC's full-paper proof.
  - Execution of the C++ `concurrent_deferred_rc` library (`benchmarks/`, `results/`); only `include/` was read.
  - MMTk LXR execution, so the smallest-heap-to-complete comparison with and without deferral was not reproduced.
- **Unknown.**
  - Why CIRC over HP grew with time here when its authors report non-growing memory. Candidate (untested): CPU oversubscription starving reclamation on a host with load above its vCPU count.
  - Whether CPython's QSBR delay produces measurable memory growth when one thread stays attached in a long C call (not executed).
- **Known not to apply.**
  - Boehm's Ω(R) bound assumes a constant per-operation work quota. It does not describe designs that drain deferred work at pauses (LXR) or at GC (CPython deferred objects).
  - CDRC's O(P²) does not bound reclaimable-but-unreclaimed objects.
- **Unsupported.** None of the CPython sources examined provide a way to make a deferred object's last decrement free it immediately, short of a GC pass or interpreter shutdown, during which deferral is disabled for reachable objects.
- **Stronger conclusions not established:**
  - that deferral explains the 15–20% memory difference in PEP 779;
  - that CDRC is unsuitable in general, since its memory matched EBR on hash maps and trees in the CIRC paper;
  - any ranking by throughput.

## Evidence

- **DOIs** were verified against Crossref on 2026-11-21: Deutsch–Bobrow `10.1145/360336.360345`; Lins `10.1016/0020-0190(92)90088-D`; Bacon et al. `10.1145/378795.378819`; Bacon–Rajan `10.1007/3-540-45337-7_12`; Levanoni–Petrank `10.1145/504282.504309` and `10.1145/1111596.1111597`; Blackburn–McKinley `10.1145/949305.949336`; Boehm `10.1145/964001.964019`; Bacon–Cheng–Rajan `10.1145/1028976.1028982`; Paz et al. `10.1145/1255450.1255453`; Shahriyar et al. `10.1145/2258996.2259008`, `10.1145/2509136.2509527`; Anderson–Blelloch–Wei `10.1145/3453483.3454060`, `10.1145/3519939.3523730` (arXiv 2204.05985); Zhao–Blackburn–McKinley `10.1145/3519939.3523440`; Jung et al. `10.1145/3656383`; Choi–Shull–Torrellas (biased counting) `10.1145/3243176.3243195`; Collins `10.1145/367487.367501`.
- **Key passages.**
  - Ulterior RC §2.2 (mechanisms, formal definitions) and §1.
  - Bacon–Cheng–Rajan §4.1 and §7.8 (eqs. 30–33).
  - Levanoni–Petrank §4 (Reclaim-Garbage, next-cycle ZCT), §5 (snooping), abstract and conclusion.
  - CDRC Theorem 1 and §2. CIRC §1.1 and §6. Anderson et al. 2022 §6. LXR §2.1 and the "Lazy Decrements" paragraph.
  - Boehm abstract.
  - PEP 703 "Deferred Reference Counting" and "Integration With Deferred and Biased Reference Counting"; PEP 779 "Memory use" and the Specification section.
- **Source** (repository@revision as pinned in `REPORT.json`):
  - `python/cpython`: `Objects/funcobject.c` L227–236; `Objects/object.c` L2820–2830; `Include/internal/pycore_object.h` L28; `Include/internal/pycore_object_deferred.h`; `Python/gc_free_threading.c` L278–300, L1146–1155, L1209–1236; `Objects/obmalloc.c` L136–155, L1411–1441; `Include/internal/pycore_qsbr.h` L27–29, L75.
  - `mmtk/mmtk-core`: `src/plan/lxr/mod.rs` L26–42; `src/plan/lxr/gc_work/rc.rs` L701–706, L748–750; `src/util/rc.rs` L14–21.
  - `python/peps`: `peps/pep-0703.rst` L599–630, L837–862, L1208–1243; `peps/pep-0779.rst` L109–116, L139–143.
  - `kaist-cp/smr-benchmark`: `README.md` L45–56, L212–239, L260.
  - `cmuparlay/concurrent_deferred_rc`: `include/cdrc/atomic_rc_ptr.h` L54–57 (`~atomic_rc_ptr` delays the decrement); `include/cdrc/rc_ptr.h` L53–58 (`~rc_ptr` decrements immediately); `include/cdrc/internal/memory_manager_base.h` L89–102 (`eject`), L114–123 (`decrement_ref_cnt`), L133–136 (`delayed_decrement_ref_cnt`); `include/cdrc/internal/counted_object.h` L64–98 (`EjectAction`, `release_refs`).
- **Execution (2026-11-21).**
  - smr-benchmark: `git checkout 00b4e4d06d9b91f289b4644163f0cac0660d4af7; RUSTUP_TOOLCHAIN=nightly-2025-03-02 cargo build --release --bin double-link`, then `support/run_doublelink_probe.sh target/release out`. Outputs: `support/doublelink_probe_log.txt`, `support/doublelink_probe.csv`.
  - CPython: `git fetch --depth 1 origin dc222c8d6c366e3d52d4b0d0053ad7bb8a601fff`; out-of-tree `configure --disable-gil` and default `configure`, each followed by `make -j24 python`; then `./python support/deferred_rc_probe.py`. Output: `support/deferred_rc_probe_output.jsonl`. Host, toolchain, build times and load averages: `support/probe_env.txt`.

## Revalidation

1. **CPython deferral (under 2 minutes after building `python`).** Run `support/deferred_rc_probe.py` under a free-threaded build. The finding holds if `alive_after_drop` equals `created` for the top-level, GC-disabled run and is 0 for the nested control. Then diff `PyFunction_NewWithQualName`'s `CO_NESTED` condition and `_Py_REF_DEFERRED` at the new revision.
2. **Chain backlog.** In smr-benchmark, run `double-link -m cdrc-ebr -t 32 -i 5` and `-i 20`. Growth roughly proportional to run length reproduces §4. Run CIRC over HP on an idle machine to resolve the open discrepancy.
3. **LXR policy.** Diff `src/plan/lxr/mod.rs` constants, `ProcessDecs::recursive_dec`, and `src/util/rc.rs` count width.
4. **Theory.** Check CDRC's full-version Theorem 1 wording for whether it adds a bound on unreclaimed objects; check Boehm's paper body for the exact model before applying Ω(R) to a design.
