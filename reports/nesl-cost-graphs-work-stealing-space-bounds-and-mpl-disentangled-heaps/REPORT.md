# Fork-join peak space: cost graphs, scheduler-specific space bounds, barrier rewrites, and what MPL, ParlayLib and calf keep live or prove

## Summary

- **Peak space of a fork-join program is a property of a schedule, not of the program.** The cost-semantics literature models an execution as a computation DAG plus heap dependencies; space at an instant is what is reachable from the roots of the executed prefix, and a schedule's peak is the maximum over its prefixes. Every published space bound fixes either a particular reference schedule (the sequential depth-first one, giving `S1`) or quantifies over a scheduler class.
- **Published bounds by policy:** parallel depth-first `S1 + O(p·D)` (time `O(W/p + D)`); NESL implementation `O(s + d·p·log p)` (time `O(w/p + d·log p)`); randomized work stealing on fully strict computations `S1·P` (expected time `T1/P + O(T∞)`); DFDeques `S1 + O(K·p·D)`; MPL's GC-integrated scheduling `O(R*·P)` memory and `O(W + R*·P)` work for determinacy-race-free (disentangled) programs.
- **Composition per resource:** work composes parallel branches with `+`, span with `max`, and worst-case space over all schedules with `+` (sum of branch peaks). For series-parallel programs with node-local allocation deltas, the recursion `peak(seq a b) = max(peak a, net a + peak b)`, `peak(par a b) = peak a + peak b` equals the maximum over all schedule prefixes exactly (derived; brute-force-checked on a toy model with 0 mismatches).
- **Inserting a join (barrier) moves bounds in opposite directions:** span (and every time bound built from it) weakly rises; the all-schedule space peak weakly falls; the depth-first reference space `S1`, and hence `S1·P`, `S1 + O(p·D)` and `O(R*·P)`, can move either way. Using the barrier form's space bound to budget the barrier-free program is unsound (toy instance: 5 vs 7).
- **Systems (pinned revisions):** MPL keeps a per-task heap per fork level and, at a join, *splices* the child's heap path into the parent's without reclaiming anything (`HM_HH_merge` → `HM_HH_zip`); its space guarantee assumes disentanglement and its GC is disabled at top level (documented). ParlayLib's waiting worker runs *other* stolen jobs on top of its blocked frame; on a synthetic fork tree this exceeded the work-stealing `S1·P` frame budget in 23 of 60 non-conservative runs and never in 60 `conservative` runs, and any per-worker par-nesting depth of 1000 aborts the process ("internal error: scheduler queue overflow"). agda-calf's parallel cost structure covers only work/span-style monoids; it has no parallel space structure, `_∥_` and its cost law are postulates, and the general parallel bound lemma `boundg/par` contains an unsolved hole under `--allow-unsolved-metas`.

## Applicability

- **Literature scope:** binary fork-join (nested parallel) computations, plus the NESL nested-data-parallel model and fully strict multithreaded computations as defined in the cited papers. Futures, synchronization variables, and general DAGs with arbitrary joins are covered only where noted.
- **Subjects examined directly (source):** `MPLLang/mpl` at `254325b5946f609f76458f0d9509a3206e0521cd` (runtime `runtime/gc/hierarchical-heap.{c,h}`, `runtime/gc/decheck.{c,h}`, scheduler `basis-library/schedulers/spork/{Scheduler,DequeABP}.sml`, `README.md`); `cmuparlay/parlaylib` at `51017699dcc421f80479cdb238d3092233ad0d26` (`include/parlay/scheduler.h`, `include/parlay/internal/work_stealing_{deque,job}.h`, `include/parlay/parallel.h`); `calfproject/agda-calf` at `10f1ba616e1ade017e4048324ae894281379ce08` (`src/Calf/Parallel.agda`, `src/Algebra/Cost/{Structures,Bundles,Instances}.agda`, `src/Examples.agda`, `src/Examples/TreeSum.agda`, `src/Examples/Sorting/Parallel/*.agda`, `.github/workflows/agda.yaml`, `README.md`).
- **Executed:** ParlayLib's default native scheduler (no `PARLAY_CILKPLUS`/`PARLAY_OPENCILK`/`PARLAY_OPENMP`/`PARLAY_TBB` plugin) built from the pinned tarball with g++ 15.2.0 `-std=c++17 -O2` on x86_64 Linux 7.1.6, 96 hardware threads. Other ParlayLib scheduler plugins were not run. MPL was not built or run; calf was not type-checked (no Agda run).
- **Toy model:** the series-parallel `(net, peak)` model in §4 is a model written for this report, not any upstream system; it is labelled wherever used.
- **Relationship among subjects:** comparison. The papers supply definitions and bounds; MPL and ParlayLib are two runtimes realizing (or not) the assumptions of those bounds; calf is a mechanized cost logic examined for which resources its parallel composition can express.

## Findings

### 1. What "peak space" means in the cost-semantics literature

Basis: documentation (papers) + derived.

- A program run is a **computation graph** (nodes = evaluation steps, edges = control/data dependencies) together with **heap dependencies** from nodes to the locations they may still use (Spoonhower, Blelloch, Harper, Gibbons, ICFP 2008 / JFP 2010). A **schedule** is any linearization (or `p`-wide step sequence) respecting the computation graph; each executed **prefix** is a down-set of the DAG.
- Space at a prefix is the size of the heap reachable from the **roots** of that prefix (values still needed by unexecuted nodes). Peak space of a schedule is the maximum over its prefixes. Different schedulers pick different prefixes, so peak space is schedule-dependent even for a deterministic program.
- `S1` (or `s`, `R*`) in published bounds is the peak of **one reference schedule** — the sequential depth-first (left-to-right) execution — not the minimum or maximum over schedules.
- Derived consequence used throughout: adding precedence edges (e.g., a barrier) removes down-sets. Any quantity defined as a **maximum over schedules** can only fall; any quantity defined as a **minimum over schedules** can only rise; the longest path (span/depth) can only rise; a quantity tied to one particular reference schedule (such as `S1`) has no fixed direction.

### 2. Published space bounds by scheduling policy

| Source (DOI) | Scheduler / setting | Time bound | Space bound | Assumptions on the computation |
| --- | --- | --- | --- | --- |
| Blelloch & Greiner, ICFP 1996 (`10.1145/232627.232650`) | NESL implementation on the paper's abstract machines | `O(w/p + d·log p)` | `O(s + d·p·log p)` reachable space | nested data-parallel NESL programs; `s` = sequential space |
| Blelloch, Gibbons & Matias, JACM 46(2) 1999 (`10.1145/301970.301974`) | parallel depth-first (PDF) schedules | `O(W/p + D)` | `S1 + O(p·D)` | fine-grained nested parallelism; `S1` = depth-first sequential space |
| Blumofe & Leiserson, JACM 46(5) 1999 (`10.1145/324133.324234`) | randomized work stealing | expected `T1/P + O(T∞)` | `S1·P` | fully strict computations (joins only to the parent); busy-leaves execution |
| Narlikar & Blelloch, TOPLAS 21(1) 1999 (`10.1145/314602.314607`) | DFDeques (depth-first deques with memory threshold `K`) | as reported in the paper | `S1 + O(K·p·D)` | nested parallelism; `K` a runtime memory quota |
| Arora, Westrick & Acar, POPL 2021 (`10.1145/3434299`) | MPL scheduling integrated with hierarchical GC | work `O(W + R*·P)` including GC | `O(R*·P)` | determinacy-race-free programs (disentangled); `R*` = sequential live memory |

Basis: documentation (Crossref-verified bibliographic data for every row; abstract text for the last row; bound forms for rows 1–4 as stated in the papers' published abstracts and secondary summaries — the full texts of rows 1–4 were not re-read for this report).

Observations (derived): the additive bounds (`S1 + O(p·D)`, `O(s + d·p·log p)`, `S1 + O(K·p·D)`) charge parallelism to depth; the multiplicative bounds (`S1·P`, `O(R*·P)`) charge it to processor count. All five are stated relative to the depth-first reference schedule; none bounds the worst case over all schedules, which can exceed `S1` by a factor up to the number of parallel leaves (a `par` of `n` leaves that each allocate `m` and free it before finishing has all-schedule peak `n·m` while `S1 = m`).

### 3. How static analyses and cost logics compose parallel branches

| System | Resource | Sequential `a ; b` | Parallel `a ∥ b` | Notes |
| --- | --- | --- | --- | --- |
| Hoffmann & Shao, ESOP 2015 (`10.1007/978-3-662-46669-8_6`) | work | `M_let + w1 + w2` | `M_Par + w1 + w2` | type-based amortized analysis (multivariate resource polynomials) |
| same | depth | `M_let + d1 + d2` | `M_Par + max(d1, d2)` | potential may not be naively reused across branches; cost-free typings separate size tracking from cost |
| same | heap space | — | — | not treated: the cost metric "assigns a non-negative cost to each evaluation step"; non-additive costs such as stack space are named as future applications |
| agda-calf `ℕ²-ParCostMonoid` | (work, span) | `(w1 + w2, s1 + s2)` | `(w1 + w2, max(s1, s2))` | `pcm-× ℕ-Work-ParCostMonoid ℕ-Span-ParCostMonoid` |
| agda-calf `ResourceMonoid` | (need, leftover) high-water pair | `(p, p') · (q, q') = (p + (q ∸ p'), q' + (p' ∸ q))` | none | sequential `CostMonoid` only; no `ParCostMonoid` instance |
| schedule-oblivious space (derived, §4) | (net, peak) | `(na + nb, max(pa, na + pb))` | `(na + nb, pa + pb)` | exact maximum over all schedule prefixes for series-parallel programs |

Basis: source (calf `Instances.agda` lines 79–116, 337–356, 416–417) + documentation (Hoffmann & Shao text: "MPar` maxpd1,d2q" for depth; "a metric that assigns a non-negative cost to each evaluation step"; "non-additive cost such as stack-space usage") + derived.

Key point (derived): the three resources differ in the *parallel* operator — `+` for work, `max` for span, `+` for worst-case space — and space alone has a non-trivial *sequential* operator (`max(pa, na + pb)`), because memory can be returned. calf's `IsParCostMonoid` requires `⊕` a monoid, `⊗` a commutative monoid with the same unit `𝟘`, a preorder and monotonicity of both operators (`Structures.agda` lines 57–64); it records **no interchange law** between `⊕` and `⊗`, so the direction in which a resource moves under a barrier rewrite is not part of the structure.

### 4. Inserting a join between pipeline steps

Rewrite: `U = (a1 ; a2) ∥ (b1 ; b2)` becomes `B = (a1 ∥ b1) ; (a2 ∥ b2)` (a barrier between the two rounds). `B`'s DAG is `U`'s DAG plus edges.

| Quantity | Direction `U → B` | Reason |
| --- | --- | --- |
| work `W` | unchanged | same nodes |
| span `D` (and `max(d1, d2)` rules, calf span) | weakly up | `max(a1 + a2, b1 + b2) ≤ max(a1, b1) + max(a2, b2)` |
| time bounds `W/p + O(D)`, `w/p + d·log p`, `T1/P + O(T∞)` | weakly up | monotone in `D` |
| all-schedule peak (sum-of-peaks recursion) | weakly down | down-sets of `B` ⊆ down-sets of `U`; equivalently `max(x1 + y1, x2 + y2) ≤ max(x1, x2) + max(y1, y2)` |
| depth-first reference peak `S1` | either | the reference order changes from `a1 a2 b1 b2` to `a1 b1 a2 b2` |
| `S1·P`, `O(R*·P)` | either | follow `S1` (`R*`) |
| `S1 + O(p·D)`, `O(s + d·p·log p)`, `S1 + O(K·p·D)` | either (biased up) | `D` term rises, `S1` either |

Basis: derived + execution (toy model of series-parallel programs, not any upstream system).

Toy-model execution (`/tmp/s3_r12_62b_ws/probes/costgraph_toy.py`, seed 0, Python 3.13.15; full source in Evidence):

```text
check1 compositional_peak_vs_bruteforce mismatches=0
check2 barrier U->B over 4000 random instances (p=4):
  span : up=1134 eq=2866 down=0
  peak : up=0 eq=3090 down=910
  s1   : up=468 eq=3023 down=509
  bound: up=1442 eq=2194 down=364
check3 hand instance a1=[3,-3] a2=[1] b1=[1] b2=[3,-3]:
  U: span=3 all_schedule_peak=7 S1=5
  B: span=4 all_schedule_peak=5 S1=5
```

`bound` is the expression `S1 + p·D` with the hidden constant set to 1 (illustrative only). Reading: span never fell; the all-schedule peak never rose; the depth-first reference peak rose and fell about equally often; the depth-first-scheduler bound expression rose about four times as often as it fell. In the hand instance, the barrier form's worst-case space (5) under-budgets the barrier-free program, whose worst schedule reaches 7. Basis for the generality of these directions: the derived argument in the table; the toy run only confirms it on small random instances.

### 5. MPL (`MPLLang/mpl` @ `254325b5946f609f76458f0d9509a3206e0521cd`)

Basis: source + documentation (README).

- **Heap per fork level, path copying, merge at join.** `hierarchical-heap.h` lines 71–76: each heap record keeps `nextAncestor`, and "all threads have their own leaf-to-root path (essentially, path copying) which is merged only at join points of the program." At a fork the scheduler bumps the depth (`HH.setDepth (thread, depth + 1)`, `Scheduler.sml`) so new allocations go to a fresh leaf heap.
- **At a join nothing is reclaimed; heaps are spliced.** `hierarchical-heap.c` lines 310–342, `HM_HH_merge`:

  ```c
  /* can only merge at join point! */
  assert(childThread->currentDepth == parentThread->currentDepth);
  ...
  // free stack of joining heap
  CC_freeStack(s, HM_HH_getConcurrentPack(childHH));
  /* Merge levels. */
  parentThread->hierarchicalHeap = HM_HH_zip(s, parentHH, childHH);
  ```

  The child's chunk lists become part of the parent's levels; byte counters (`bytesSurvivedLastCollection`, `bytesAllocatedSinceLastCollection`) are summed. Reclamation happens later in local (leaf) and concurrent (internal-heap) collections. So the memory live just after a join is the union of both branches' surviving allocations — the `+` of §3 — until a collection runs.
- **Unstolen fork (fast path).** `Scheduler.sml` lines 807–812: if the spawned right side was never stolen, "the thread hasn't been stolen, so it hasn't yet been converted into a full thread. (The discarded thread is located in the current heap ... so it will be garbage-collected appropriately.)"; `HH.joinIntoParentBeforeFastClone` promotes chunks into the parent.
- **Which forks become stealable.** The spork scheduler promotes a fork to a stealable task only when heartbeat tokens suffice (`Heartbeat.enoughToSpawn ()`, `Scheduler.sml` lines 1035–1040) and `depth < Queue.capacity` and `depthOkayForDECheck depth` hold (lines 678, 785; the same conjunction is asserted in `assertTokenInvariants`, lines 228–243). `Queue.capacity = 2^6 − 1 = 63` (`DequeABP.sml` lines 38–39). Beyond these limits `maybeSpawn` returns `false` and the fork runs sequentially — degradation, not failure (contrast ParlayLib, §6).
- **Disentanglement check uses fork-path task ids.** `decheck.c`: `MAX_FORK_DEPTH 31` (line 9); a tid packs a path bit-string and `(dag_depth << 5) | tree_depth`; fork sets the children's paths to `(path & ~(1<<h)) | (1<<(h+1))` and `(path | (1<<h)) | (1<<(h+1))` (lines 106–112); `decheckIsOrdered` (lines 295–318) decides whether a writer is ordered before the current task by an LCA computed with bit tricks and a per-thread table of sync depths. When entanglement detection is compiled in, the scheduler stops spawning at depth ≥ 31 (`depthOkayForDECheck`). In `ASSERT` builds a global table of `sizeof(uint32_t) * 2^31` bytes is mapped (`decheckInit`, lines 34–46; comment: "8 GB with the default MAX_FORK_DEPTH").
- **What is proved/measured.** The space theorem `O(R*·P)` and work `O(W + R*·P)` (POPL 2021) assume determinacy-race freedom, which implies disentanglement (POPL 2020). The README cites entanglement detection (ICFP 2022) and effects support (PLDI 2023), and its Known Issues state: "The GC is currently disabled at the 'top level' (outside any calls to `ForkJoin.par`) ... it can cause a memory explosion for programs that are mostly (or entirely) sequential" (README lines 303–307). Programs that do most allocation outside `par` are therefore outside the practical scope of the space guarantee.

### 6. ParlayLib (`cmuparlay/parlaylib` @ `51017699dcc421f80479cdb238d3092233ad0d26`)

Basis: source + execution (real library, synthetic workload).

- **Fork/steal/join protocol** (`scheduler.h` lines 337–352): `pardo` builds `right_job` *on the forking frame's stack*, pushes it, runs `left`, then either pops and runs `right` itself or, if stolen, calls `scheduler.wait_until(done, conservative)`. The forking frame (and everything it holds) stays live until the thief finishes.
- **Waiting runs unrelated work on top of the blocked frame.** `scheduler.h` lines 140–159 and 214–229: non-conservative `wait_until` calls `do_work_until(done)`, which repeatedly takes a local job or steals a random one and runs it *on the same call stack*. The header warns this "can deadlock if the stolen work wants a lock held by the code that is waiting". Conservative mode busy-waits (`std::this_thread::yield()`).
- **Fixed-capacity deque.** `work_stealing_deque.h` line 41 `static constexpr int q_size = 1000;` and lines 57–60: on reaching 1000 the push prints `internal error: scheduler queue overflow` and calls `std::abort()`. Each slot is `alignas(64)`, so each deque reserves ≈64 KB.
- **Execution — nesting depth limit.** `deque_depth.cpp` (Evidence) nests `par_do` `d` deep: `d = 998, 999` complete; `d = 1000, 1001` abort with exit status 134 and the message above; identical with `PARLAY_NUM_THREADS = 1, 8, 64`. The limit counts pushes not yet popped on one worker's deque, so it also applies to recursion that a waiting worker stacks on top of a blocked frame.
- **Execution — help-while-waiting versus the `S1·P` frame budget.** `steal_wait.cpp` (Evidence): complete binary fork tree of depth `D = 14`; each internal node holds one unit from entry until after its join; leaves spin 1–20 µs (90%) or 200–2000 µs (10%), deterministically per seed. Sequentially, peak live units `S1 = 14` and at most 14 internal frames are nested on the stack. 20 seeds per row:

  | `P` | mode | max frames nested on one worker's stack (range) | runs with nesting > `D` | peak live units (range) | `S1·P` | runs with peak > `S1·P` | median wall s |
  | --- | --- | --- | --- | --- | --- | --- | --- |
  | 4 | default | 14–22 | 17 | 48–62 | 56 | 5 | 0.555 |
  | 8 | default | 15–33 | 20 | 95–143 | 112 | 9 | 0.258 |
  | 16 | default | 18–32 | 20 | 187–273 | 224 | 9 | 0.125 |
  | 4 | conservative | 14–14 | 0 | 48–51 | 56 | 0 | 0.681 |
  | 8 | conservative | 14–14 | 0 | 84–94 | 112 | 0 | 0.355 |
  | 16 | conservative | 14–14 | 0 | 150–169 | 224 | 0 | 0.173 |

  Derived explanation: Blumofe–Leiserson's `S1·P` argument relies on the busy-leaves property, which a library on a linear stack cannot provide when a blocked frame is buried under stolen work: a frame whose children have all finished cannot resume until the work stacked above it completes, so it holds memory while not being a leaf of the active computation. Conservative mode restores "one active path per worker" (≤ `D` frames per worker, hence ≤ `S1·P`) at the cost of idle waiting (median 23–38% slower here). Scope: this is one synthetic workload; it shows the bound is not implied by the implementation, not a frequency for real applications.
- **What ParlayLib measures or proves about space:** nothing found in the examined files — no space accounting, no documented space bound, no GC. User obligations stated in source: avoid holding a lock across a non-conservative wait; keep per-worker par-nesting below 1000.

### 7. agda-calf (`calfproject/agda-calf` @ `10f1ba616e1ade017e4048324ae894281379ce08`)

Basis: source.

- `src/Calf/Parallel.agda` line 1: `{-# OPTIONS --rewriting --allow-unsolved-metas #-}`. Lines 23–27 **postulate** the parallel operator and its cost law:

  ```agda
  postulate
    _∥_ : {A₁ A₂ : tp⁺} → cmp (F A₁) → cmp (F A₂) → cmp (F (A₁ ×⁺ A₂))
    ∥/join : ∀ {A₁ A₂} {v₁ v₂ c₁ c₂} →
      step (F A₁) c₁ (ret v₁) ∥ step (F A₂) c₂ (ret v₂) ≡ step (F (A₁ ×⁺ A₂)) (c₁ ⊗ c₂) (ret (v₁ , v₂))
  ```

- The general bound rule `boundg/par` (lines 53–67) contains an **unsolved hole** as its first reasoning step, line 61: `≲⟨ {!   !} ⟩` (relating `bind cost (e₁ ∥ e₂) …` to the parallel composition of the two cost projections). `bound/par` (lines 69–74), the rule giving `IsBounded … (e₁ ∥ e₂) (c₁ ⊗ c₂)`, is defined as `boundg/par`. `bound/par` is used by `Examples/Sorting/Parallel/MergeSort.agda` line 244 and `MergeSortPar.agda` line 283.
- `src/Examples.agda` line 14 comments out `-- import Examples.Sorting.Parallel`, so the CI build (`agda --html … src/index.agda` with Agda v2.6.3 and stdlib v2.0, `.github/workflows/agda.yaml`) checks `Examples.TreeSum` and `Examples.Exp2` (which import `Calf.Parallel`) but not the parallel sorting bounds. Whether Agda 2.6.3 accepts the import of a module with an unsolved meta without error was not executed here.
- **Cost structures available for `∥`:** `ℕ-Work-ParCostMonoid` (`⊗ = +`), `ℕ-Span-ParCostMonoid` (`⊗ = ⊔`, line 346), their product `ℕ²-ParCostMonoid` (line 417), and `sequentialParCostMonoid`. The README describes a parallel cost monoid as `(ℂ, ⊕, 𝟘, ⊗, 𝟙, ≤)` (README line 33), but the code's `ParCostMonoid` has a single unit `𝟘` for both operators (`Bundles.agda` lines 34–44) — a documentation/source discrepancy.
- **Space:** the high-water `ResourceMonoid` (lines 79–116) is a sequential `CostMonoid` only. A schedule-oblivious parallel space structure (`⊗ = (p + q, p' + q')` on the same pairs) would satisfy the `IsParCostMonoid` fields (commutative monoid, monotone), but no such instance exists at this revision, and calf's step-counting semantics does not model reclamation timing across interleavings. Derived: calf can state parallel *time* bounds but, as pinned, no parallel *space* bounds.

### 8. Cross-system matrix

| | MPL | ParlayLib (native) | agda-calf |
| --- | --- | --- | --- |
| Live at a steal | parent's heap path (ancestors) + thief's fresh leaf heap; promoted task's continuation | forking frame and its stack-allocated job; thief runs the closure by reference | n/a (no machine model) |
| Live at a join | union of both branches' surviving chunks (spliced, not copied, not freed) | blocked frame plus any stolen work stacked above it | n/a |
| Space guarantee | `O(R*·P)` for disentangled programs (paper); top-level GC disabled (README) | none documented | none for `∥` |
| Fork-depth capacity | 63 (spawning declines), 31 when entanglement detection is on | 1000 pushes per worker (abort) | n/a |
| User-program assumptions | disentanglement / determinacy-race freedom; allocation mostly inside `par` | no lock held across non-conservative waits; nesting < 1000 | cost annotations via `step`; parallel law axiomatized |
| Enforcement | dynamic (entanglement detection/management in runtime) | none (abort on overflow) | static, modulo postulates and one open hole |

### 9. Performance and resource footprint (L1–L6)

| Level | Evidence | Status |
| --- | --- | --- |
| L1 authoring/repair | calf parallel merge sort bounds: `MergeSort.agda` 13,295 bytes, `MergeSortPar.agda` 17,427 bytes + `MergeSortPar/Merge.agda` 36,591 bytes (source sizes from the pinned tree); person-months not reported | source sizes only; effort not examined |
| L2 toolchain build | ParlayLib probe `g++ -O2`: 0.82 s wall, 147 MB max RSS (header-only library) | execution (this host) |
| L3 elaboration | calf CI job budget `timeout-minutes: 60` (workflow file); Agda check time not measured | not examined |
| L4 generated code | ParlayLib probe run `P = 16`, `D = 14`: 0.12 s wall, 3.2 MB max RSS; conservative mode 23–38% slower median on this workload | execution (synthetic) |
| L5 proof checking | calf: not run. MPL `decheckIsOrdered`: O(1) bit operations plus a table lookup per check (source) | source / not examined |
| L6 memory/binary | ParlayLib deque ≈ 64 KB per worker (1000 × 64-byte slots); probe binary 30,256 bytes; MPL `ASSERT`-build sync-depth table 8 GiB virtual (2^31 × 4 B, zero-filled mapping); MPL top-level allocation not collected (README) | source + execution |

### 10. Comprehensibility and conceptual simplicity (C1–C2)

Basis: derived.

- **C1 working-memory load.** A reader must hold four concepts to interpret any space bound: the DAG, the heap dependencies, the reference schedule, and the scheduler class. Bounds that hide the reference schedule inside `S1` invite the error of treating `S1` as the program's space. The `(net, peak)` pair is the smallest local summary that composes for worst-case space; diagnosing a violation needs the witness down-set (which branches advanced how far), which none of the examined systems reports.
- **C1 footguns found:** ParlayLib's waiting strategy silently changes the space and deadlock behaviour of code that holds locks or memory across a join; MPL's top-level GC gap is documented only under Known Issues; calf's README and code disagree on the units of a parallel cost monoid.
- **C2 one abstraction for three resources.** Work, span and worst-case space are each a pair (sequential operator, parallel operator) on an ordered carrier; they differ in the *direction* of the interchange inequality between `(a ; b) ∥ (c ; d)` and `(a ∥ c) ; (b ∥ d)` — equality for work, `≤` for span, `≥` for space. Recording that direction as a field (an interchange law) would make the barrier analysis of §4 an instance of the structure instead of a per-resource argument; calf's `IsParCostMonoid` currently omits it. The separation between the core invariant (down-set structure of the DAG) and realization accidents (linear stacks, fixed deques, heartbeat promotion) is clean in the papers and blurred in ParlayLib, where the stack discipline changes which bound applies.

### 11. Validation of implementations and claims (V1–V4)

| Level | What exists | Gap |
| --- | --- | --- |
| V1 spec adequacy / non-vacuity | toy model: compositional peak checked against exhaustive down-set enumeration (0 mismatches over 394 generated programs and 8000 barrier-rewrite instances); calf bound lemma has an unsolved hole, so its parallel bounds are not fully checked | no mutation testing of calf specs; no machine check that published bounds match their papers' models |
| V2 checker/lowering fuzzing | none examined | — |
| V3 concurrency validation | ParlayLib stress runs with deterministic leaf seeds (this report); MPL entanglement detection is a runtime monitor | no GenMC/Loom-style model checking of either deque; seed sweeps only sample schedules |
| V4 field/human validation | MPL README reports scale to "hundreds of cores" and heaps "as much as 1TB" | not examined for space bounds |

## Boundaries

- **Not examined:** MPL concurrent-collection policy details (`concurrent-collection.c`), local-collection scope selection (`HM_HH_desiredCollectionScope`), entanglement *management* (pinning) costs; ParlayLib under its Cilk Plus, OpenCilk, OpenMP and TBB plugins; any measurement of MPL itself; Agda type-checking of calf; futures, synchronization variables and non-series-parallel DAGs.
- **Unknown:** whether ParlayLib's help-while-waiting exceeds `S1·P` on real applications; the frequency observed (23 of 60 non-conservative runs over `P ∈ {4, 8, 16}`) is specific to the synthetic workload above. Whether Agda accepts `Calf.Parallel` without error under the CI configuration.
- **Known not to apply:** the work-stealing `S1·P` bound to ParlayLib's default waiting mode (the busy-leaves precondition is not met, and the bound was exceeded in execution); the all-schedule peak equality of §4 to programs with frees that depend on interleaving (e.g., reclamation triggered by GC timing) — the toy model uses node-local deltas.
- **Unsupported (by the subject):** parallel space bounds in calf at the pinned revision; par-nesting ≥ 1000 per worker in ParlayLib (aborts); spawning beyond depth 63 (or 31 with entanglement detection) in MPL (forks run sequentially).
- **Stronger conclusions not established:** that barriers always reduce real memory use (they reduce the worst case over schedules, not the memory of a particular scheduler); that MPL's `O(R*·P)` holds for programs allocating mainly outside `par`; that the table rows 1–4 bounds hold with the exact constants shown (constants are hidden in `O(·)`; the papers' full texts were not re-verified here).

## Evidence

All evidence acquired 2026-11-20 (UTC).

**Repositories (pinned):**

- `MPLLang/mpl` `254325b5946f609f76458f0d9509a3206e0521cd`: `runtime/gc/hierarchical-heap.c` 310–342 (`HM_HH_merge`); `runtime/gc/hierarchical-heap.h` 71–76; `runtime/gc/decheck.c` 9–11, 36–40, 98–124, 181–208, 273–318; `basis-library/schedulers/spork/Scheduler.sml` 136–150, 228–239, 670–690, 795–890; `basis-library/schedulers/spork/DequeABP.sml` 33–51; `README.md` 18–26, 41–72, 300–307.
- `cmuparlay/parlaylib` `51017699dcc421f80479cdb238d3092233ad0d26` (tarball sha256 `4f2fc759c1ca474db2f45585ee2300997a128d48fba79bf47aaa579aa8858ee8`): `include/parlay/scheduler.h` 131–275, 330–352; `include/parlay/internal/work_stealing_deque.h` 14–63; `include/parlay/internal/work_stealing_job.h` 17–50; `include/parlay/parallel.h` 158–211.
- `calfproject/agda-calf` `10f1ba616e1ade017e4048324ae894281379ce08`: `src/Calf/Parallel.agda` 1–74; `src/Algebra/Cost/Structures.agda` 57–98; `src/Algebra/Cost/Bundles.agda` 34–59; `src/Algebra/Cost/Instances.agda` 79–120, 319–356, 416–417; `src/Examples.agda` 1–20; `src/Examples/TreeSum.agda` 1–40; `.github/workflows/agda.yaml`; `README.md` 33, 57, 181–210.

**Literature (DOIs resolved through Crossref on 2026-11-20):** Blelloch & Greiner, ICFP 1996, pp. 213–225, `10.1145/232627.232650`; Blelloch, Gibbons & Matias, JACM 46(2):281–321, 1999, `10.1145/301970.301974`; Blumofe & Leiserson, JACM 46(5):720–748, 1999, `10.1145/324133.324234`; Narlikar & Blelloch, TOPLAS 21(1):138–173, 1999, `10.1145/314602.314607`; Spoonhower, Blelloch, Harper & Gibbons, ICFP 2008 pp. 253–264, `10.1145/1411204.1411240`, and JFP 20(5–6):417–461, 2010, `10.1017/S0956796810000146`; Hoffmann & Shao, ESOP 2015, LNCS pp. 132–157, `10.1007/978-3-662-46669-8_6` (full text read from the author's PDF); Raghunathan, Muller, Acar & Blelloch, ICFP 2016 pp. 392–406, `10.1145/2951913.2951935`; Westrick, Yadav, Fluet & Acar, POPL 2020 (PACMPL 4), `10.1145/3371115`; Arora, Westrick & Acar, POPL 2021 (PACMPL 5), `10.1145/3434299`; Niu, Sterling, Grodin & Harper, POPL 2022 (PACMPL 6), `10.1145/3498670`; Westrick, Arora & Acar, ICFP 2022 (PACMPL 6) pp. 679–710, `10.1145/3547646`; Arora, Westrick & Acar, PLDI 2023 (PACMPL 7) pp. 1558–1583, `10.1145/3591284`; Grodin, Niu, Sterling & Harper, POPL 2024 (PACMPL 8) pp. 273–301, `10.1145/3632852`.

**Execution environment:** x86_64, Linux 7.1.6, 96 hardware threads; g++ (Debian 15.2.0-14); Python 3.13.15. ParlayLib from the pinned tarball, include path `parlaylib-51017699dcc421f80479cdb238d3092233ad0d26/include`.

**Probe 1 — `deque_depth.cpp` (verbatim):**

```cpp
// Probe 1: nesting depth of par_do on a single worker vs. the fixed deque capacity.
// Build: g++ -std=c++17 -O2 -pthread -I<parlaylib>/include deque_depth.cpp -o deque_depth
// Run:   PARLAY_NUM_THREADS=1 ./deque_depth <depth>
#include <cstdio>
#include <cstdlib>
#include <parlay/parallel.h>

static long leaves = 0;

void nest(int d) {
  if (d == 0) { leaves++; return; }
  // Each level pushes one right-hand job onto the worker's deque before running the left side.
  parlay::par_do([&] { nest(d - 1); }, [&] { /* trivial right side */ });
}

int main(int argc, char** argv) {
  int depth = std::atoi(argv[1]);
  nest(depth);
  std::printf("depth=%d completed leaves=%ld workers=%zu\n", depth, leaves, parlay::num_workers());
  return 0;
}
```

```text
$ g++ -std=c++17 -O2 -pthread -I$INC deque_depth.cpp -o deque_depth
$ for d in 998 999 1000 1001; do PARLAY_NUM_THREADS=1 ./deque_depth $d; echo "exit=$?"; done
depth=998 completed leaves=1 workers=1
exit=0
depth=999 completed leaves=1 workers=1
exit=0
internal error: scheduler queue overflow
exit=134
internal error: scheduler queue overflow
exit=134
(PARLAY_NUM_THREADS=8 and =64: depth 999 completes, depth 1000 aborts identically.)
```

**Probe 2 — `steal_wait.cpp`** (verbatim; run: `PARLAY_NUM_THREADS=<P> ./steal_wait 14 <conservative> <seed>`, seeds 1–20):

```cpp
// Probe 2: frames that stay live on a worker's stack while it waits at a join.
//
// Workload: complete binary fork tree of depth D. Every internal node holds one unit of
// "frame memory" from entry until after its join (like a merge buffer that must outlive
// both children); leaves hold nothing and spin for a deterministic pseudo-random time.
// A sequential (depth-first) execution therefore has peak live units S1 = D and a maximum
// physical nesting of D internal frames on its stack.
//
// Measured per run:
//   max_stack  = maximum, over workers, of internal frames simultaneously nested on that
//                worker's own call stack (thread_local counter);
//   peak_live  = maximum, over time, of internal frames entered but not yet exited (all workers).
//
// Build: g++ -std=c++17 -O2 -pthread -I<parlaylib>/include steal_wait.cpp -o steal_wait
// Run:   PARLAY_NUM_THREADS=<P> ./steal_wait <D> <conservative 0|1> <seed>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <parlay/parallel.h>

static std::atomic<long> live{0};
static std::atomic<long> peak_live{0};
static std::atomic<long> max_stack{0};
static thread_local long my_stack = 0;
static bool conservative = false;
static uint64_t seed = 1;

static inline uint64_t mix(uint64_t x) {
  x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
  x ^= x >> 27; x *= 0x94d049bb133111ebULL;
  x ^= x >> 31; return x;
}

static void spin_us(double us) {
  auto t0 = std::chrono::steady_clock::now();
  while (std::chrono::duration<double, std::micro>(std::chrono::steady_clock::now() - t0).count() < us) {}
}

static void enter() {
  long l = live.fetch_add(1) + 1;
  long p = peak_live.load();
  while (l > p && !peak_live.compare_exchange_weak(p, l)) {}
  my_stack++;
  long m = max_stack.load();
  while (my_stack > m && !max_stack.compare_exchange_weak(m, my_stack)) {}
}

static void leave() { my_stack--; live.fetch_sub(1); }

static void node(int d, uint64_t id) {
  if (d == 0) {
    // Heavy-tailed leaf durations: 90% short (1-20us), 10% long (200-2000us).
    uint64_t h = mix(id ^ (seed * 0x9e3779b97f4a7c15ULL));
    double u = (h >> 11) * (1.0 / 9007199254740992.0);
    double us = (h % 10 == 0) ? 200.0 + 1800.0 * u : 1.0 + 19.0 * u;
    spin_us(us);
    return;
  }
  enter();
  parlay::par_do([&] { node(d - 1, 2 * id); }, [&] { node(d - 1, 2 * id + 1); }, conservative);
  leave();
}

int main(int argc, char** argv) {
  int D = std::atoi(argv[1]);
  conservative = std::atoi(argv[2]) != 0;
  seed = std::strtoull(argv[3], nullptr, 10);
  auto t0 = std::chrono::steady_clock::now();
  node(D, 1);
  double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  long P = (long)parlay::num_workers();
  std::printf("P=%ld D=%d conservative=%d seed=%llu S1=%d max_stack=%ld peak_live=%ld S1*P=%ld time_s=%.3f\n",
              P, D, (int)conservative, (unsigned long long)seed, D, max_stack.load(), peak_live.load(),
              (long)D * P, secs);
  return 0;
}
```

Sample raw lines: `P=8 D=14 conservative=0 seed=2 S1=14 max_stack=21 peak_live=125 S1*P=112 time_s=0.249`; `P=8 D=14 conservative=1 seed=2 S1=14 max_stack=14 peak_live=84 S1*P=112 time_s=1.182` (first sampling pass; the §6 table aggregates a separate pass of 20 seeds per row, whose `P=8` default-mode rows include `max_stack=33` and `peak_live=143`). The aggregated table in §6 summarizes 120 runs. Build: `g++ -std=c++17 -O2 -pthread -I$INC steal_wait.cpp -o steal_wait` (0.82 s, 147,184 KB max RSS; binary 30,256 bytes).

**Probe 3 — `costgraph_toy.py`** (toy model, verbatim; run `python3 costgraph_toy.py 0`; output reproduced in §4; check1 compared 394 generated programs with at most 18 steps, 256 of them containing `seq`/`par` nodes):

```python
import random, sys
def net(t): return sum(t[1]) if t[0] == 'leaf' else net(t[1]) + net(t[2])
def peak(t):
    if t[0] == 'leaf':
        s = m = 0
        for d in t[1]: s += d; m = max(m, s)
        return m
    a, b = t[1], t[2]
    return max(peak(a), net(a) + peak(b)) if t[0] == 'seq' else peak(a) + peak(b)
def span(t):
    if t[0] == 'leaf': return len(t[1])
    return span(t[1]) + span(t[2]) if t[0] == 'seq' else max(span(t[1]), span(t[2]))
def steps(t, out):            # step DAG: list of [delta, preds]; returns (sources, sinks)
    if t[0] == 'leaf':
        first = last = None
        for d in t[1]:
            out.append([d, [last] if last is not None else []]); i = len(out) - 1
            first = i if first is None else first; last = i
        return ([first] if first is not None else []), ([last] if last is not None else [])
    sa, ka = steps(t[1], out); sb, kb = steps(t[2], out)
    if t[0] == 'seq':
        for s in sb: out[s][1] = list(set(out[s][1]) | set(ka))
        return (sa or sb), (kb or ka)
    return sa + sb, ka + kb
def brute_peak(t):            # max over all down-sets (= all schedule prefixes)
    dag = []; steps(t, dag); best = 0
    def rec(i, chosen, mem):
        nonlocal best
        if i == len(dag): best = max(best, mem); return
        rec(i + 1, chosen, mem)
        if all(p in chosen for p in dag[i][1]):
            chosen.add(i); rec(i + 1, chosen, mem + dag[i][0]); chosen.discard(i)
    rec(0, set(), 0); return best
def df_peak(t):               # sequential left-to-right depth-first schedule
    s = m = 0
    def go(t):
        nonlocal s, m
        if t[0] == 'leaf':
            for d in t[1]: s += d; m = max(m, s)
        else: go(t[1]); go(t[2])
    go(t); return m
def leaf(r, n=3): return ('leaf', [r.randint(-2, 3) for _ in range(r.randint(1, n))])
def tree(r, d):
    if d == 0 or r.random() < 0.3: return leaf(r)
    return (r.choice(['seq', 'par']), tree(r, d - 1), tree(r, d - 1))
r = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
mism = 0
for _ in range(400):
    t = tree(r, 3); dag = []; steps(t, dag)
    if len(dag) <= 18 and peak(t) != brute_peak(t): mism += 1
print('check1 compositional_peak_vs_bruteforce mismatches=%d' % mism)
cnt = {}; p = 4
for _ in range(4000):
    a1, a2, b1, b2 = (leaf(r, 4) for _ in range(4))
    U = ('par', ('seq', a1, a2), ('seq', b1, b2)); B = ('seq', ('par', a1, b1), ('par', a2, b2))
    assert brute_peak(U) == peak(U) and brute_peak(B) == peak(B)
    for k, fu, fb in [('span', span(U), span(B)), ('peak', peak(U), peak(B)), ('s1', df_peak(U), df_peak(B)),
                      ('bound', df_peak(U) + p * span(U), df_peak(B) + p * span(B))]:
        d = 'up' if fb > fu else 'eq' if fb == fu else 'down'; cnt[(k, d)] = cnt.get((k, d), 0) + 1
print('check2 barrier U->B over 4000 random instances (p=%d):' % p)
for k in ['span', 'peak', 's1', 'bound']:
    print('  %-5s: up=%d eq=%d down=%d' % (k, cnt.get((k, 'up'), 0), cnt.get((k, 'eq'), 0), cnt.get((k, 'down'), 0)))
a1, a2, b1, b2 = ('leaf', [3, -3]), ('leaf', [1]), ('leaf', [1]), ('leaf', [3, -3])
U = ('par', ('seq', a1, a2), ('seq', b1, b2)); B = ('seq', ('par', a1, b1), ('par', a2, b2))
print('check3 hand instance a1=[3,-3] a2=[1] b1=[1] b2=[3,-3]:')
for n, t in [('U', U), ('B', B)]:
    print('  %s: span=%d all_schedule_peak=%d S1=%d' % (n, span(t), peak(t), df_peak(t)))
```

## Revalidation

- **ParlayLib capacity:** `grep -n 'q_size' include/parlay/internal/work_stealing_deque.h` at the new revision; rerun Probe 1 at depths `q_size − 1` and `q_size`.
- **ParlayLib waiting strategy:** inspect `wait_until` / `do_work_until` in `include/parlay/scheduler.h`; if waiting still runs arbitrary stolen jobs on the same stack, rerun Probe 2 for `P ∈ {4, 8, 16}`, seeds 1–20, and compare `peak_live` with `14·P`. A run with `peak_live > 14·P` reconfirms the boundary; none in 60 runs weakens (does not refute) it.
- **MPL join semantics:** diff `HM_HH_merge` and `HM_HH_zip` in `runtime/gc/hierarchical-heap.c`; check `MAX_FORK_DEPTH` in `decheck.c`, `capacityPow` in `DequeABP.sml`, and the README Known Issues text on top-level GC.
- **calf:** `grep -n 'allow-unsolved-metas\|{!' src/Calf/Parallel.agda`; `grep -n 'Sorting.Parallel' src/Examples.agda`; `grep -n 'ParCostMonoid' src/Algebra/Cost/Instances.agda` to see whether a space instance or an interchange field has been added. Type-check with the CI Agda/stdlib versions to settle the open import question.
- **Toy-model directions:** rerun Probe 3 with other seeds; any `span down` or `peak up` count above zero would indicate a bug in the model, since both directions follow from the down-set argument.
