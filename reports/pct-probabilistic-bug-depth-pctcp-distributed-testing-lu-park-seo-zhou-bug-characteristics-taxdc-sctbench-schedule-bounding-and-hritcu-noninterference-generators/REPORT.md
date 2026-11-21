# Probabilistic Concurrency Testing, bug depth, and empirical evidence on how deep real concurrency bugs are

## Summary

- **Bug depth** (Burckhardt et al., ASPLOS 2010) is the minimum number of ordering constraints in a *directive* that guarantees a bug. For a program with at most `n` threads and `k` steps, one run of the PCT scheduler finds a depth-`d` bug with probability at least `1/(n·k^(d−1))`. The algorithm draws a random permutation of initial thread priorities and `d−1` independent, uniform priority-change points in `{1..k}`, then always runs the enabled thread with the highest priority. The bound needs `n` and `k` up front. In practice both the paper's prototype and the two open implementations examined here estimate `k` from earlier runs. Basis: documentation (paper) + source.
- **PCTCP** (Ozkan et al., OOPSLA 2018) extends the guarantee to partial orders revealed online, such as message-passing executions. It covers the order with chains using online chain partitioning and proves a bound of `1/(w²·n^(d−1))`, where `w` is the poset width and `n` the number of events. Both are unknown in advance. **Notation swap:** PCTCP writes the PCT bound as `1/(k·n^(d−1))`, with `k` as the number of chains and `n` as the number of events. The PCTCP authors state that P#'s "prioritized strategy", which is the predecessor of Coyote's strategy, has no chains and does not carry PCTCP's guarantee.
- **Two open implementations deviate from the published algorithm in ways that matter for the bound:**
  - **Shuttle's `PctScheduler`** follows the paper closely. Its deviations are that it learns `k` dynamically, draws change points without replacement, and counts only multi-runnable steps. Separately, its new-task priority insertion never selects TaskId 0 as a swap target. As a result, a newly spawned task ranks above task 0 with probability `(N−1)/(2N)` rather than `1/2` (exact enumeration). This only matters for tasks with id ≥ 16.
  - **Coyote's `PrioritizationStrategy`** draws a *random number* of change points in `[1, bound]` and schedules operation groups rather than threads. It also selects change points with a loop that its own remark calls Fisher–Yates, but which draws every swap index from `[0, Count)`. Under that loop, change point 0 is selected with probability ≥ `(1−1/L)^(L−1)` ≈ 0.37, against a uniform `c/L` (exact enumeration plus Monte Carlo of a transliteration).
- **Empirical depth studies:**
  - **Lu–Park–Seo–Zhou (2008), 105 real bugs:**
    - 101/105 involve ≤ 2 threads.
    - 97/105 (92%) manifest once the order among ≤ 4 memory accesses is enforced.
    - 49/74 non-deadlock bugs involve one variable.
    - 30/31 deadlocks involve ≤ 2 resources.
  - **TaxDC (2016), 104 distributed-concurrency bugs in Cassandra, HBase, Hadoop MapReduce and ZooKeeper:** a third-party summary reports that more than 60% are triggered by a single untimely message and 63% need a fault. The primary text was **not examined**.
- **Schedule bounding vs randomization:** on SCTBench's 49 bugs, PCT with `d = 3` was the most effective technique (Thomson–Donaldson–Betts, TOPC 2016). It found every bug any other technique found, plus three more, and missed one. A naive random scheduler beat preemption bounding.
- **The worst-case bound is far looser than observed hit rates:**
  - **Derived from SCTBench's recorded `(n, k)`:** for `d = 3`, only 30 of 49 benchmarks would reach 99% detection within a 100,000-schedule budget.
  - **PCT paper's own measurements:** pbzip2 had a measured hit rate of 0.701 against a guaranteed 0.0001, and Dryad 0.164 against 2×10⁻⁵.
- **Partial-order sampling (POS):** POS beats PCT where many events do not race, and Morpheus (ASPLOS 2020) applies it to Erlang distributed systems. In POS's micro-benchmarks, PCT never covered all partial orders.
- **Noninterference testing (Hriţcu et al.):** the decisive lever against counterexamples that need long instruction sequences was not more search. It was generation by execution plus **strengthening the property**. Moving from end-to-end to single-step noninterference cut the geometric-mean time to failure from 135.76 ms to 0.47 ms on their control-flow machine.
- **Toy experiment** (planted ordering chains of depth 1–5; a toy model, not any upstream tool):
  - PCT with a matched `d` tracks its bound closely on precisely timed chains.
  - PCT with too small a `d` *never* hits deeper chains.
  - Uniform random walk and uniform interleaving sampling beat PCT on average when `k` is small, but fail on behaviours that need a long uninterrupted run.
  - Lexicographic enumeration finds such behaviours last.

## Applicability

- **Subjects and how they relate.** Two published randomized schedulers (PCT and PCTCP) are compared against two open implementations that cite PCT:
  - Shuttle `PctScheduler`, a Rust concurrency-testing library, at `awslabs/shuttle@72bdbdb612c2311905c84bbc73d59f12a5b17e43`.
  - Coyote `PrioritizationStrategy`, a .NET systematic-testing framework, at `microsoft/coyote@0c51dc58cc34cdefa24dcfabf3439e5e0ec77309`.

  The empirical background comes from two bug-characteristic studies and SCTBench (`mc-imperial/sctbench@d59ab26ddaedcd575ffb6a1f5e9711f7d6d2d9f2`, its benchmark list and harness). Delay bounding, partial-order sampling, uniform random walk and noninterference generator design are covered as alternative ways to reach deep behaviours.
- **Exact observation vs extension.**
  - The implementation findings apply only to the pinned revisions. Both pins were each repository's `HEAD` on the observation date.
  - Probabilistic claims about the implementations come from **Python transliterations** of the quoted loops. Neither upstream binary was built or run.
  - Claims about the papers come from author-hosted PDFs or open-access versions (Evidence lists them). TaxDC percentages come only from a third-party review.
- **Program model.**
  - PCT's guarantee assumes a terminating, deterministic-given-schedule program with known upper bounds on threads and steps. "Step" means a scheduling point; the paper's prototype counted synchronization operations.
  - PCTCP assumes events are revealed in "upgrowing" order: each new element is maximal so far.
  - Neither guarantee covers data nondeterminism, weak-memory reorderings below the scheduling granularity, or liveness. PCT and PCTCP are unfair schedulers.
- **Toy experiment.** The toy model has `n` threads, each with `m` always-enabled unit steps, and no synchronization. Its numbers are properties of that model only.

## Findings

### 1. PCT: depth, algorithm, guarantee (Burckhardt, Kothari, Musuvathi, Nagarakatte 2010)

Basis: documentation (paper, Sections 2–3 and 5)

- **Definitions.**
  - A *directive* `D = (E, A1, b1, …, Ad, bd)` consists of an event labelling plus `d` label sets `Ai` and distinct labels `bi` (Def. 5).
  - A schedule *violates* `D` in either of two cases (Def. 6). Either some `bi` occurs while a member of `Ai` has not occurred, or some `bj` occurs before `bi` for `i < j`.
  - `D` *guarantees* bug `B` when two conditions hold (Def. 7). Every non-violating partial schedule can be extended without violating `D`, and every complete non-violating schedule satisfies `D` and lies in `B`.
  - `depth(B) = min{size(D) | D guarantees B}` (Def. 8). The paper's ordering violation (Fig. 1a) has depth 1. Its atomicity violation and deadlock examples have depth 2.
- **Algorithm `RandS(n, k, d)` (Fig. 7).**
  1. Set `p[t] ← d + π(t) − 1` for a uniform random permutation `π`. Initial priorities are therefore `d … d+n−1`.
  2. Draw `k1 … kd−1` uniformly in `{1..k}`.
  3. Repeatedly run the enabled thread with the *maximal* `p`.
  4. After the schedule length reaches `ki`, set the running thread's priority to `d − i`. These values sit below all initial priorities, and later change points give lower values.
- **Theorem 9.** If `n ≥ maxthreads(P)` and `k ≥ maxsteps(P)`, then `Pr[RandS(n,k,d) ∈ B] ≥ 1/(n·k^(d−1))`.
  - The proof builds a directed scheduler `DirS` that shares the random variables. `DirS` succeeds when `π` gives `b1`'s thread the lowest initial priority (probability `1/n`) and each `ki` hits the step that precedes `bi+1` (probability `1/k` each).
  - The sample space has `n!·k^(d−1)` equally likely valuations.
- **Engineering deviations stated in the paper.**
  - `d` is chosen from a random distribution in practice (footnote 1).
  - `k` for run `i+1` is the step count of run `i`, which may under- or over-estimate `k`.
  - No change points are inserted while only one thread is enabled.
  - Phases are detected at join points.
  - An extra change point is added for the main thread before exit ("final wait").
- **Measured vs guaranteed (paper Tables 2–3).** Hosts were a quad-core Xeon L5420 at 2.50 GHz with 16 GB RAM.

| Program | d | n | k | k_eff | Stress | Random sleep | PCT measured | PCT guaranteed |
|---|---|---|---|---|---|---|---|---|
| Splash-FFT | 1 | 2 | 791 | 139 | 0.06 | 0.27 | 0.50 | 0.5 |
| Splash-LU | 1 | 2 | 1517 | 996 | 0.07 | 0.39 | 0.50 | 0.5 |
| Splash-Barnes | 1 | 2 | 7917 | 318 | 0.0074 | 0.0101 | 0.4916 | 0.5 |
| Pbzip2 | 2 | 4 | 1981 | 1207 | 0 | 0 | 0.701 | 0.0001 |
| Work Steal Queue | 2 | 2 | 1488 | 75 | 0 | 0.001 | 0.002 | 0.0003 |
| Dryad | 2 | 5 | 9631 | 1990 | 0 | 0 | 0.164 | 2×10⁻⁵ |

The previously unknown Firefox and Internet Explorer bugs were found with `d = 1`. The Firefox run had `n = 12` and `k = 38.4M` operations; the Internet Explorer run had `n = 25` and `k = 1.4M`.

### 2. PCTCP: distributed extension (Ozkan, Majumdar, Niksic, Tabaei Befrouei, Weissenbacher 2018)

Basis: documentation (paper)

- **Model.**
  - Events (sends/receives, crashes, reboots) form a happens-before partial order revealed online. A schedule is a linearization of that order.
  - A schedule *hits* a `d`-tuple if it orders those events as listed. A family of schedules is *d-hitting* if it contains a hitting schedule for every `d`-tuple the order allows.
  - PCT samples a *strong* d-hitting family by treating each thread as one chain.
- **Algorithm.**
  1. Maintain an online chain partition with `O(w²)` chains (Agarwal–Garg), assign random chain priorities, and always schedule the highest-priority enabled chain.
  2. Lower chain priorities at `d−1` random points.
  3. Guarantee: `≥ 1/(w²·n^(d−1))` for partial orders of width ≤ `w` and size ≤ `n`.

  PCT is recovered as a special case. PCTCP's introduction writes the PCT bound as `1/(k·n^(d−1))`, with `k` as the number of chains (threads) and `n` as the number of instructions. That reverses the letters used in the PCT paper.
- **Implementations evaluated.** These were a modified P# runtime that schedules only receive events, a Cassandra harness on SAMC, and the HitMC scheduler for ZooKeeper.
- **Reported results.**
  - **P# benchmarks.** `d` was raised from 1 only when 10,000 runs found nothing; ChainReplication needed `d = 5`. Percentage of buggy runs:

    | Benchmark | Runs | PCTCP | Random walk in PCTCP runtime | P# prioritized | P# random walk |
    |---|---|---|---|---|---|
    | BoundedAsync | 10,000 | 98.97% | 99.04% | 0 | 0 |
    | ChainReplication | 1,000 | 12.6% | 17.5% | 0 | 0 |
    | Raft | 1,000 | 0.2% | 1.1% | 0 | 1.3% |
    | FailureDetector | 5,000 | 0.36% | 0.08% | 0 | 0 |

  - **Cassandra CASSANDRA-6023.** There were 54 events. Random walk found 0 of 1,000 runs, and PCTCP with `d = 4` also found 0. PCTCP found 1 of 1,000 runs with `d = 5` and again with `d = 6`.
  - **ZooKeeper leader election.** With 1 crash and 1 reboot over 1,000 runs, random walk produced 12 inconsistent elections. PCTCP produced 26–42, with 42 for `d = 5` and `n = 50`.
  - **Overhead.** Runs took 2–7 s each.
- **Stated limitations.**
  - The scheduler is unfair. Raft livelocks unless a heuristic cycle detector temporarily disables a chain.
  - HitMC applies the guarantee only to the first `n` events.
  - Bugs found at parameter `d` need not have depth `d`.
  - The authors note that P#'s "prioritized strategy" is called PCT in P#'s source "but without the notion of chains it does not provide the same probabilistic guarantee".

### 3. Two open implementations at pinned revisions

Basis: source + execution (exact enumeration of transliterations; not the upstream binaries)

| Aspect | Paper (RandS) | Shuttle `shuttle-schedulers/src/pct.rs` | Coyote `Source/Core/Testing/Interleaving/PrioritizationStrategy.cs` |
|---|---|---|---|
| Unit prioritized | thread | task | *operation group*; random choice inside the group (l.110) |
| Number of change points | exactly `d−1` | `min(max_depth−1, max_steps−1)` (l.99) | uniform in `[1, bound]`: `Next(MaxPriorityChangesPerIteration) + 1` (l.70); default bound 10 |
| Change-point domain | i.i.d. uniform `{1..k}` | distinct, `[1, max_steps−1]` (l.102–105) | `Take(c)` of a shuffled `[0, MaxPriorityChangePoints)` (l.71–75) |
| Step counter | every step | only decisions with >1 runnable task (l.141–154) | only steps with ≥2 enabled groups (l.99–103) |
| `k` | given | learned: first iteration runs oldest-task-first, then grows (l.75–79, 151–153) | max multi-group step count over earlier iterations (l.67); no change points in iteration 0 |
| Yield | not modelled | yielding task deprioritized like a change point (l.142) | not special-cased in this strategy |
| New threads | random priority | swap with random target (l.116–132) | insert at uniform index in `[0, Count]` (l.132) |
| Fairness | unfair | unfair | fair variant falls back to random after `MaxUnfairSchedulingSteps` (l.89–92; default 10,000, `Configuration.cs` l.369) |

**Shuttle new-task insertion.** At `pct.rs` line 121:

```rust
let target_task_id = TaskId::from(self.rng.gen_range(0..self.priorities.len()) + 1);
```

The target is drawn from `[1, len]`. Drawing the new task's own id gives it the lowest priority; otherwise the target is moved to the lowest priority and the new task takes the target's old one. TaskId 0 is never a target.

Exact enumeration over all prior priority permutations, `N = 2..6`, gives `P(new task ranks above task 0) = (N−1)/(2N)`: 0.25, 0.333, 0.375, 0.400 and 0.417. Uniform insertion would give 0.5.

Priorities for TaskIds `0..15` are pre-populated and reshuffled each iteration (l.56, 88–93; `DEFAULT_INLINE_TASKS = 16` in `shuttle-engine/src/runtime/task/mod.rs` l.52). The insertion path, and hence this deviation, only affects tasks with id ≥ 16. Whether it lowers the depth bound for any concrete program is **unknown**.

**Minor Shuttle items.**
- The comment at l.100–101 says change points are offset into `[1, max_steps]`, but the code yields `[1, max_steps−1]`. This still covers every decision after the first.
- The doc comment points to a Coyote path, `.../Strategies/Probabilistic/PCTStrategy.cs`, that does not exist in the pinned Coyote tree.
- In `shuttle/tests/basic/pct.rs` l.193 the comment reads "n=50, k=110" while computing `1/(20*110)` for 20 threads.

**Coyote change-point shuffle.** At `PrioritizationStrategy.cs` lines 195–201:

```csharp
for (int idx = result.Count - 1; idx >= 1; idx--)
{
    int point = this.RandomValueGenerator.Next(result.Count);
    int temp = result[idx];
    result[idx] = result[point];
    result[point] = temp;
}
```

- **What the code does.** The remark at l.187–191 says "Shuffles the specified range using the Fisher-Yates algorithm". `Next(n)` is `System.Random.Next(n)`, which is uniform on `[0, n)` (`Source/Core/Random/RandomValueGenerator.cs` l.55). Textbook Fisher–Yates instead draws `point` from `[0, idx]`.
- **Why index 0 is over-selected.** Position 0 is never an `idx` and changes only when `point == 0`. Element 0 therefore stays first with probability ≥ `(1−1/L)^(L−1)` → `1/e`.
- **Exact enumeration of all `L^(L−1)` draw sequences.**

| L | c kept | P(index 0 selected), Coyote loop | uniform | min P(specific set) / uniform | max / uniform |
|---|---|---|---|---|---|
| 5 | 1 | 0.4096 | 0.200 | 0.512 | 2.048 |
| 7 | 1 | 0.3966 | 0.143 | 0.463 | 2.776 |
| 7 | 2 | — | 0.0476 | 0.343 | 2.048 |

  - The textbook loop gives ratio exactly 1.000 in every row.
  - **Monte Carlo** (seed 7): `P(index 0 selected)` is 0.368 for `L = 100, c = 1`, 0.454 for `L = 100, c = 10`, and 0.374–0.384 for `L = 1000, c = 1..10`. The textbook loop gives 0.0097, 0.1011 and 0.0005–0.012.
- **Consequence (derived).** Change point 0 coincides with the first decision at which a second group is enabled. At that decision, the uniformly random insertion of new groups (l.132) already randomizes which group runs first. Shuttle skips this index for exactly that reason (`pct.rs` l.96–98). Combined with the random count in `[1, 10]` under the default bound, the probability of drawing a specific set of `d−1` later points falls below the paper's `1/k^(d−1)` factor. For `L = 7` and one point, it can be as low as 0.46× uniform.
- **Where this strategy runs.** Coyote's default portfolio is fair mode (`Configuration.cs` l.352). Under the interleaving policy it rotates Random, ProbabilisticRandom(3), Prioritization(10) and DelayBounding(10) round-robin per iteration (`OperationScheduler.cs` l.125–133, 219–222). This strategy therefore drives one default iteration in four.
- **Delay bounding in Coyote.** `DelayBoundingStrategy` draws its delay points *with replacement* in `[0, MaxDelayPoints]` (l.70–76).

**Derived consequence for distributed code.** Neither implementation maintains chains. By PCTCP's own argument about P#, neither implementation carries PCTCP's `1/(w²n^(d−1))` guarantee for message-passing programs.

### 4. How deep are real concurrency bugs?

Basis: documentation

**Lu, Park, Seo, Zhou (2008).** The study covered 105 randomly selected bugs from MySQL, Apache, Mozilla and OpenOffice: 74 non-deadlock and 31 deadlock. "Manifestation condition" means a partial order among a set of accesses which, once enforced, guarantees the bug.

| Quantity | Non-deadlock (74) | Deadlock (31) |
|---|---|---|
| Threads: 1 / 2 / >2 / env. | 0 / 71 / 1 / 2 | 7 / 23 / 1 / 0 |
| Variables or resources: 1 / >1 | 49 / 25 | 7 / 23 (2 res.) + 1 (>2) |
| Accesses: 1 / 2 / 3 / 4 / >4 | 0 / 22 / 33 / 12 / 7 | 7 / 3 / 20 / 0 / 1 |
| Pattern | 72 atomicity or order violation; 24 order violations | — |

- **Derived:** 101/105 involve ≤ 2 threads, and 97/105 = 92.4% involve ≤ 4 accesses (67 non-deadlock + 30 deadlock).
- **The authors' caveat:** "we do not intend to draw any general conclusions about all concurrent applications". The four applications are C/C++.
- **The authors' own caveat on testing:** "enforcing a specific partial order among a set of accesses is not trivial", because inputs and many accesses must also be controlled.

**TaxDC (Leesatapornwongsa, Lukman, Lu, Gunawi 2016).**
- From the abstract: 104 distributed-concurrency bugs from Cassandra, Hadoop MapReduce, HBase and ZooKeeper, classified by triggering timing condition, input preconditions, symptoms and fixes, and stored as 2,083 labels.
- A third-party review (Evidence) reports the following; the primary PDF was not reachable:
  - more than 60% are triggered by a single untimely message delivery (order or atomicity violation);
  - 63% need faults such as crashes, reboots, timeouts or disk errors;
  - 47% fail silently.
- **Reading for depth (derived, hedged).** The "single message" ordering is shallow in PCTCP's sense, but the fault preconditions widen the search space beyond message orderings. PCTCP's Cassandra case needed `d ≥ 5`.

### 5. Schedule bounding vs randomized search; delay bounding

Basis: documentation + source + derived

- **SCTBench (Thomson, Donaldson, Betts; TOPC 2016 abstract).** The suite has 49 buggy benchmarks and compared DFS, preemption bounding, delay bounding, a controlled random scheduler and PCT.
  - PCT with `d = 3` was best: it found every bug the others found plus three more, and missed one.
  - The random scheduler found more bugs than preemption bounding and two fewer than delay bounding.
  - Delay bounding beat preemption bounding, and bounded search beat unbounded DFS.
  - Most bugs need a bound of 1–2; one needs 5 preemptions.
  - In 18 benchmarks the bug appeared in 50% of random runs. These "trivial" benchmarks should serve only as a minimum baseline.
- **Harness.** `README.md` lists `run_many.py --mode {dfs,pb,db,random,pct} --limit 100 --timelimit 300`, recommends a schedule limit of at least 10,000, and names 100,000-schedule result logs. Preemption and delay bounding iterate bounds 0, 1, …. `benchmarks/buggy.txt` columns are `suite test maxThreads maxSteps` (`scripts/run_many.py` l.141–145). It has 49 active lines, with `k` ranging from 8 to 24,453 (median 43) and `n` from 2 to 101 (median 4).
- **Derived from `buggy.txt`.** With `N99 = ⌈ln 0.01 / ln(1−p)⌉` and `p = 1/(n·k^(d−1))`:
  - **d = 2:** 45/49 benchmarks reach 99% within 100,000 runs.
  - **d = 3:** only 30/49 do. Examples are ferret (`n=11, k=24453`: `p = 1.5×10⁻¹⁰`, N99 ≈ 3.0×10¹⁰), radbench bug1 (8.8×10⁹), and splash2 barnes (1.8×10⁸).

  Because PCT with `d = 3` still found all but one bug, the worst-case bound evidently understates real hit rates by orders of magnitude. The bugs' true depths are **unknown**, so this observation cannot rank the bound's slack per benchmark.
- **Delay bounding (Emmi, Qadeer, Rakamarić; POPL 2011, MSR technical report text).** A deterministic scheduler is allowed `K` delays (skip the next-scheduled task).

| Bounding scheme | Exploration cost |
|---|---|
| Unbounded | `O(C^I)` |
| Context bounding | `O((IC)^c)` |
| Preemption bounding | `O((IC)^(p+C))` |
| Delay bounding | `O(I^K)`, independent of the number of dynamically created tasks |

  Here `I` is the number of scheduler invocations and `C` the number of choices per invocation. Deciding delay-bounded depth-first reachability is NP-hard, and in NP for simple asynchronous programs.

  | Benchmark | Preemption bounding | Delay bounding |
  |---|---|---|
  | Remaining CCR bug | 8,895 schedules (2 preemptions) | 2,728 schedules (2 delays) |
  | Futures livelock (1,075 steps) | 259 schedules | 45 schedules |

  The paper also compared PB and DB schedule counts across 41 CCR tests in its Fig. 5.
- **Guarantee contrast (derived).** Delay or preemption bounds give a *coverage* guarantee only once the bounded space is exhausted, and the bound counts deviations from a chosen deterministic scheduler. PCT's depth is a property of the bug and gives a per-run probability that does not depend on exhausting anything.

### 6. Partial-order sampling, uniformity, and distributed systems

Basis: documentation

- **POS (Yuan, Yang, Gu; CAV 2018).** The algorithm:
  1. Give each event a fresh uniform priority.
  2. Always run the highest-priority enabled event.
  3. After executing an event, re-draw the priorities of enabled events that race with it.

  **Theorem 1.** The probability of sampling partial order `E` is at least `(1/P^{|V_E|})·R^U`, where `P` is the number of processes, `|V_E|` the number of events, `D_E` the number of races, `R = P·|V_E|/(|V_E|+D_E)`, and `U = (|V_E| − D_E/(P−1))/2`. With at least an `αN` share of non-racing events, the bounds compare as follows:

  | Strategy | Worst-case probability |
  |---|---|
  | Random walk | `1/P^N` |
  | PCT | `1/N^((1−α)N)` |
  | POS | advantage over random walk whenever `α > 0` |
- **POS micro-benchmarks.** These had 4 threads × 4 events × 4 objects. Across all ten programs, PCT showed "0(x)" (incomplete coverage of all partial orders). The geometric mean of minimum hit ratios was 2.14e−8 for random walk and 2.87e−6 for POS.
- **POS on SCTBench** (10⁴ tries per case; 32 non-trivial cases):

  | | POS | PCT variants | Random walk |
  |---|---|---|---|
  | Geometric-mean hit ratio vs POS | 1× | ≈2.6× lower | ≈4.7× lower |
  | Best in (cases) | 20 | 10 | 3 |
  | Bugs missed | 0 | 1 | 3 |
- **Morpheus (Yuan, Yang; ASPLOS 2020).** Morpheus applies POS plus conflict analysis to Erlang and found 11 previously unknown errors in four systems, including RabbitMQ and Mnesia. Hit ratios over 10,000 trials per configuration (PCT with `d = 5`):

  | Algorithm | Geometric-mean hit ratio |
  |---|---|
  | POS+ | 0.0249 |
  | POS | 0.0151 |
  | PCT+ | 0.0106 |
  | PCT | 0.0089 |
  | Random walk | undefined: missed 2 of 11 errors even with conflict analysis |

  Message sends conflict when they share a recipient, which differs from shared-memory location conflicts.
- **Selectively uniform random walk (Zhao, Wolff, Mathur, Roychoudhury; ASPLOS 2025).** It argues that random walk is far from uniform over interleavings and samples interleavings uniformly given per-task event-count estimates. Shuttle ships it as `UrwRandomScheduler` (`shuttle-schedulers/src/urw.rs`), which uses one trial run to estimate the counts.

### 7. Generator design for noninterference testing (Hriţcu et al., JFP 2016 / ICFP 2013)

Basis: documentation (arXiv 1409.0393v2, which carries the JFP 26 e4 reference)

- **Setup.** QuickCheck tests information-flow abstract machines against injected bugs. Pairs of indistinguishable states are generated by generating one state and *varying its high parts*. MTTF was measured on 4×2.4 GHz machines with 11.7 GB RAM, GHC 7.4.1 and QuickCheck 2.7.6, with 5-minute caps.
- **Generators for the basic stack machine (Fig. 5).** MTTF in ms.

| Bug | Naive | Weighted | Sequence | Sequence + smart ints | By execution |
|---|---|---|---|---|---|
| ADD* | 83247 | 5344 | 561.6 | 30.05 | 0.87 |
| LOAD* | not found | not found | 73116 | 2259 | 4.03 |
| STORE*A | not found | not found | 38036 | 32227 | 1233.5 |
| Geometric mean | — | — | 69.73 | 13.33 | 0.77 |
| Tests/s | 24129 | 11466 | 8541 | 7915 | 3284 |
| Discard rate | 79% | 62% | 65% | 59% | 4% |

  Naive programs execute an average of 0.47 steps, and 74% of runs stop on stack underflow. Any counterexample needs at least a `Store` and a `Halt`. Generation *by execution* builds each next instruction from the current machine state.
- **Property strengthening (Fig. 18, control-flow machine).** The variants, in order of strength, were end-to-end NI from initial states (EENI, `≈mem`), EENI with `≈low`, quasi-initial starting states, LLNI, and single-step SSNI over all states with "tiny" generation.
  - The STORE*A MTTF fell from 20,018.67 ms to 16.32 ms.
  - The geometric mean fell from 135.76 ms to 0.47 ms.
  - SSNI with naive generation reached a geometric mean of 12.87 ms.
  - **Derived lesson:** shrinking the *required depth of a counterexample*, by making invariants explicit, beats searching harder for long counterexamples. The cost is that the invariant must be discovered, and the authors show testing guiding that discovery.

### 8. Toy experiment: planted ordering chains of increasing depth

Basis: execution (toy model written for this report; not Shuttle, Coyote, or any upstream tool)

- **Model.**
  - `n` threads each run `m` always-enabled steps, giving `k = n·m`.
  - A planted behaviour of depth `d` is a chain of `d+1` events alternating between threads 0 and 1, which must occur in order. Threads 2…n−1 are bystanders.
  - **Loose** chains place events at random admissible steps. **Tight** chains use consecutive steps of the same thread, so every switch must occur at an exact point.
  - Every chain is guaranteed by a directive of size `d`, so its PCT depth is ≤ `d` (minimality not proved).
  - **r2c** means thread 1 finishes all `m` steps before thread 0 starts.
- **Strategies.** Lexicographic DFS (lowest thread first), uniform random walk (`rw`), uniform interleaving sampling (`uni`), and `RandS(n, k, D)` for `D = 1..5`. There were 8 chains per (looseness, depth) group.
- **Statistics.** "min" is the smallest per-chain hit-rate estimate in the group. "0" means fewer than 1/N.

| Config | Group | rw min / mean | uni min / mean | PCT(D=d) min / mean | Bound `1/(n k^(d−1))` | DFS hit ≤ 1000 schedules |
|---|---|---|---|---|---|---|
| n=2, m=8 (k=16; exhaustive 12,870), N=20,000 | tight d=2 | .0300 / .0967 | .0256 / .1348 | .0299 / .0308 | .03125 | 7/8 |
| | tight d=3 | .0347 / .0628 | .0263 / .0742 | .0016 / .0020 | .00195 | 3/8 |
| | tight d=4 | .0106 / .0250 | .0019 / .0260 | .0001 / .0001 | 1.2e−4 | 3/8 |
| | loose d=3 | .0019 / .109 | .0001 / .177 | .0019 / .0064 | .00195 | 6/8 |
| | r2c | .0037 | .0001 (exact 1/12870) | .4997 | .5 | first hit = schedule 12,870 (last) |
| n=2, m=40 (k=80), N=20,000 | tight d=2 | 0 / .0189 | 0 / .0239 | .0060 / .0067 | .00625 | 0/8 |
| | loose d=2 | .0017 / .141 | 0 / .192 | .0232 / .0488 | .00625 | 0/8 |
| | r2c | 0 | 0 | .5056 | .5 | 0 |
| n=4, m=12 (k=48), N=10,000 | tight d=2 | .0108 / .0679 | .0016 / .0611 | .0094 / .0107 | .0052 | 0/8 |
| | r2c | .0004 | 0 | .5083 | .25 | 0 |

- **Per-run rates vs the bound.** In every resolvable group (`N·bound ≥ 5`), no chain's PCT estimate fell significantly below the bound (one-sided `z > 3.29`). For tight 2-thread chains the bound is nearly attained: 0.0299–0.0308 against 0.03125, and 0.0016–0.0020 against 0.00195. For `d ≥ 4` at `k = 16`, and `d ≥ 3` at `k ≥ 48`, `N` cannot resolve the bound.
- **Under-provisioned depth is fatal.** PCT with `D < d` had **zero hits on every chain** of depth `d` in all three configurations, for example `pct1` on every `d ≥ 2` chain. Over-provisioning costs a factor: on r2c at `k = 16`, the hit rate falls from 0.4997 at `D = 1` to 0.2814, 0.1590, 0.0869 and 0.0489 for `D = 2…5`.
- **Random walk and uniform sampling.** At small `k` they beat matched-`D` PCT on mean hit rate for `d ≥ 3`, because the whole interleaving space is small (12,870). They lose on worst-case chains that need a long uninterrupted run, where random walk hits r2c at `2^(−m)`: measured 0.0037 for `m = 8`, which equals 1/256 within sampling error.
- **Lexicographic DFS.** It reaches behaviours that start with a high-id thread last.

### 9. Performance and resource footprint (L1–L6)

| Level | What is known | Basis |
|---|---|---|
| L1 authoring/maintenance | **not measured** for either implementation. PCTCP's chain tracking required a custom P# runtime and a custom SAMC/HitMC scheduler. | documentation |
| L2 toolchain build | **not measured**: Shuttle and Coyote were not built. | — |
| L3 per-decision scheduling cost | Shuttle: `min_by_key` over runnable tasks plus `Vec::contains` over `d−1` change points per decision, so `O(runnable + d)`. Coyote: `List` scans, `Remove`/`Add`, and `HashSet` lookup per decision, so `O(groups)`. Wall-clock per decision: **not measured**. | source (derived) |
| L4 end-to-end testing throughput | PCTCP P#: BoundedAsync 10,000 runs in 71.48 s; Cassandra 1,000 runs in about 504–512 min; ZooKeeper 1,000 runs in 2,059–7,111 s. Hriţcu: 24,129 tests/s (naive) vs 3,284 tests/s (by execution). SCTBench harness defaults: 300 s time limit, 100,000-schedule logs. Toy probe: 140,000 schedules plus 12,870 enumerated in 4.9 s, single thread, on a 2.60 GHz Xeon (`n=2, m=8`). | documentation + execution |
| L5 certificate checking | not applicable: no certificates are produced. | — |
| L6 memory | Toy probes: peak RSS 11.9–24.2 MB (`/usr/bin/time -v`). Upstream schedulers' RSS: **not measured**. | execution |

### 10. Comprehensibility, simplicity, and validation (C1–C2, V1–V4)

- **C1 (comprehensibility).**
  - PCT's mental model is small: random priorities plus `d−1` demotions. Failures replay deterministically (Shuttle `ReplayScheduler`).
  - The guarantee's preconditions, known `n` and `k` and exactly `d−1` changes, are silently replaced by estimates and random counts in both implementations. A user cannot read a bound off the configuration.
  - PCTCP's algorithm is short, but its proof rests on online-dimension theory.
  - Hriţcu et al.'s shrinking yields minimal counterexamples, and the SSNI ones are single steps.
- **C2 (simplicity).** PCT, PCTCP and POS are one mechanism, priority scheduling over a cover of the partial order, differing only in the cover:

  | Scheme | Cover |
  |---|---|
  | PCT | threads |
  | PCTCP | online chains |
  | POS | per-event priorities re-drawn on races |

  Delay bounding and preemption bounding are the exhaustive counterparts, parameterized by deviations from a deterministic scheduler. Coyote's "operation group" is an extra unit whose relation to chains is undocumented.
- **V1 (property validation).**
  - Hriţcu et al. measured injected-bug MTTF, a mutation-style kill metric.
  - SCTBench uses 49 known bugs.
  - The upstream test `shuttle/tests/basic/pct.rs` asserts hits with margins derived from the bound.
  - The toy probe is non-vacuous: under-provisioned `D` gives zero hits.
- **V2 (implementation vs specification).** There is no differential test against RandS. The §3 deviations come from source reading and are confirmed only on transliterations.
- **V3 (concurrency validation).** This whole report is V3 evidence.
- **V4 (operational validation).** PCTCP's ZooKeeper and Cassandra studies replay crash/reboot fault budgets through model-checker harnesses.

## Boundaries

- **Not examined:**
  - The primary text of TaxDC; its percentages above are secondary.
  - The full text of Thomson–Donaldson–Betts beyond the abstract: per-benchmark bounds, the never-found bug's identity, and PCT parameters other than `d = 3`.
  - The ICB paper (Musuvathi–Qadeer 2007) beyond its DOI.
  - Trace-aware PCT (Ozkan et al., OOPSLA 2019).
  - Coyote's `Fuzzing/PrioritizationStrategy.cs`, which uses random delays rather than change points.
- **Unknown:**
  - Whether Shuttle's TaskId-0 exclusion or Coyote's biased change-point selection changes measured bug-finding rates on any real benchmark. Only exact probabilities of the transliterated selection steps were computed.
  - The real depths of SCTBench bugs.
  - Whether PCT run with parameter `D > depth` retains `1/(n k^(D−1))`. The toy shows positive but reduced hit rates; this is not proved.
  - The minimal PCT depth of the toy chains.
- **Known not to apply:**
  - PCTCP's guarantee does not apply to Shuttle or Coyote PCT on message-passing code (no chains).
  - The PCT guarantee does not apply to iterations where the learned `k` underestimates the true step count, or where Coyote draws fewer than `d−1` change points.
  - The toy model has no blocking, so priority inversion, which PCT's directive handles, is absent.
- **Unsupported:** fairness or liveness under PCT. Shuttle and Coyote use explicit fair fallbacks or yield demotion, and PCTCP uses a livelock heuristic.
- **Not established by this evidence:**
  - That bounded or random search exposes deep, precisely timed behaviours at rates the worst-case bound predicts. Observed rates exceed the bound when many tuples trigger the bug, and the bound itself becomes unusable once `d ≥ 3` and `k` is in the thousands.
  - That the absence of a counterexample after N schedules certifies anything beyond what the bound gives for known `n`, `k` and `d`.
- **Scale limits of this investigation:** the probes were limited to ≤ 60 s, a single thread and ≤ 4 GiB. Neither upstream framework was built.

## Evidence

All observations were made on 2026-11-21 (UTC).

- **Shuttle** (`awslabs/shuttle@72bdbdb612c2311905c84bbc73d59f12a5b17e43`):
  - `shuttle-schedulers/src/pct.rs` l.12–19 (doc), 56, 75–105, 113–163, with l.121 quoted.
  - `shuttle-engine/src/runtime/task/mod.rs` l.52.
  - `shuttle/tests/basic/pct.rs` l.176–200.
  - `shuttle-schedulers/src/urw.rs` l.29–38.
  - `shuttle-schedulers/README.md`.
- **Coyote** (`microsoft/coyote@0c51dc58cc34cdefa24dcfabf3439e5e0ec77309`):
  - `Source/Core/Testing/Interleaving/PrioritizationStrategy.cs` l.60–83, 86–113, 118–161, 186–204, with l.195–201 quoted.
  - `Source/Core/Testing/Interleaving/DelayBoundingStrategy.cs` l.60–84.
  - `Source/Core/Random/RandomValueGenerator.cs` l.55.
  - `Source/Core/Configuration.cs` l.352, 369, 503–507.
  - `Source/Core/Runtime/Scheduling/OperationScheduler.cs` l.125–133, 212–222.
- **SCTBench** (`mc-imperial/sctbench@d59ab26ddaedcd575ffb6a1f5e9711f7d6d2d9f2`): `README.md`; `benchmarks/buggy.txt`; `scripts/run_many.py` l.135–181.
- **Papers.** All DOIs were verified against Crossref metadata on 2026-11-21.
  - Burckhardt et al., ASPLOS 2010, doi:10.1145/1736020.1736040. Author PDF at microsoft.com: Figs. 7–8, Defs. 5–8, Thm. 9, Tables 2–3.
  - Ozkan et al., PACMPL 2(OOPSLA) 160, doi:10.1145/3276530. Author PDF at fniksic.github.io: §1, §4, Tables 1–5.
  - Lu et al., ASPLOS 2008, doi:10.1145/1346281.1346323. Author PDF: Tables 5–7, Findings 1–8.
  - Leesatapornwongsa et al., ASPLOS 2016, doi:10.1145/2872362.2872374. Abstract via an index of ACM metadata; percentages from a third-party review blog post of 2016-11-09.
  - Thomson et al., TOPC 2(4), doi:10.1145/2858651 (abstract), and PPoPP 2014, doi:10.1145/2555243.2555260.
  - Emmi et al., POPL 2011, doi:10.1145/1926385.1926432; the SIGPLAN Notices version doi:10.1145/1925844.1926432 is the one cited by Coyote. Text from MSR-TR-2010-123: §1, Fig. 5, Thms. 1–2.
  - Hriţcu et al., JFP 26 e4, doi:10.1017/S0956796816000058 = arXiv:1409.0393v2 (Figs. 5–8, 18); ICFP 2013, doi:10.1145/2500365.2500574.
  - Yuan, Yang, Gu, CAV 2018, doi:10.1007/978-3-319-96142-2_20. Author PDF: Thm. 1, §4.3, Tables 1, 3.
  - Yuan and Yang, ASPLOS 2020, doi:10.1145/3373376.3378484. Author PDF: Tables 2–3.
  - Zhao et al., ASPLOS 2025, doi:10.1145/3669940.3707214 (abstract, §5).
  - Musuvathi and Qadeer, PLDI 2007, doi:10.1145/1250734.1250785 (identity only).
- **Execution.** The host was an x86-64 Intel Xeon at 2.60 GHz running Python 3.13. Each probe ran single-threaded under `ulimit -v 4194304` and `timeout 60`. Scripts and raw outputs are in `support/`:
  - `python3 pct_depth_probe.py 2 8 20000 12870 1`; `… 2 40 20000 20000 2`; `… 4 12 10000 20000 3`. Outputs: `out/pct_depth_*.txt`.
  - `python3 pct_changepoint_probe.py 7` (exact; `out/pct_changepoint.txt`).
  - `python3 pct_changepoint_mc.py 7` (`out/pct_changepoint_mc.txt`).
  - `python3 sctbench_bounds.py buggy.txt` (`out/sctbench_bounds.txt`).

## Revalidation

- **Coyote shuffle.** Diff `PrioritizationStrategy.cs` l.186–204 and l.68–76 at a new revision. If `Next(result.Count)` has become `Next(idx + 1)`, the bias is gone. Otherwise rerun `pct_changepoint_probe.py` and expect `P(index 0)` ≥ `(1−1/L)^(L−1)`.
- **Shuttle insertion.** Check `pct.rs` for the `gen_range(0..len) + 1` target draw and for `DEFAULT_INLINE_TASKS`. The `(N−1)/(2N)` result follows directly.
- **Count and domain of change points.** Re-read `pct.rs` l.99–105 and Coyote l.70–75.
- **SCTBench bounds.** Rerun `sctbench_bounds.py` on any updated `buggy.txt`.
- **Paper numbers.** The paper numbers are fixed. Re-verify the DOIs with Crossref.
- **Toy experiment.** Rerun with the same seeds for identical numbers. To test a real implementation, port the chain family into a Shuttle test (`check_pct`, `check_random`, `check_urw`) and compare hit rates with `support/out/pct_depth_*.txt`. That comparison has not been done.
