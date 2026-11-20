# Measured multicore interference bounds: resource-stressing and auto-tuned enemy programs, space and avionics measurement campaigns, and validity critiques of EVT-based probabilistic timing analysis

## Summary

A measured interference bound is the largest execution time observed for a task while co-running programs ("enemies", "resource-stressing benchmarks", "RapiDaemons") load shared hardware. It is an upper bound only under assumptions that measurements cannot themselves establish:

- the enemy set dominates every co-runner behaviour the deployment admits, on every interference channel and combination of channels;
- the task's own paths and hardware states are covered;
- no timing anomaly or thermal/frequency effect makes a less aggressive co-runner, or an unmeasured state, slower.

The primary sources examined do not claim more than this.

- **Radojković et al. (2012)** call the resource-stressing slowdown an "upper estimate" that is "unlikely to be exceeded" and state that "the design of worst-interference benchmarks [is] infeasible in practice". In the same study, mixed stressing workloads exceeded the worst homogeneous workload for 2 of 3 real benchmarks.
- **Iorga et al. (2020)** found that auto-tuned enemies produced a statistically larger slowdown than an enemy from prior work in 35 of 105 benchmark/chip combinations (maximum difference 3.8×). They position empirical tuning as a "first pass" evaluation.
- **Their released harness** (`mc-imperial/multicore-test-harness`) optimizes a confidence-bounded **0.9 quantile after removing samples more than 3 scaled MADs from the median**, and discards runs above a temperature limit. By construction it measures a robust high percentile, not a worst case (`Basis: source`).
- **Industrial methodology** (VanderLeest–Thompson 2020) asserts that execution under RapiDaemons "is an upper bound on WCET … because the RapiDaemons cause equivalent or higher interference than any real application could cause", without proof. The same paper concedes that it is "not clear how combinations of interference channels might produce unique impact".
- **Hardware findings repeatedly overturned earlier worst cases.**
  - MSHR contention defeated cache partitioning (up to 21× reported; Valsan et al. 2016).
  - Write-back-buffer denial of service reached 346× on a Cortex-A53 board (Bechtel & Yun 2019).
  - On the NGMP FPGA prototype, store-heavy kernels reached >19× because the L1 data cache is write-through (Fernández et al. 2012).

Extreme-value MBPTA adds a statistical layer whose validity rests on i.i.d. samples, representativity of the measurement campaign, and (for its original soundness argument) time-randomized hardware. The surveys read concur on four points:

- the results "are only valid for future scenarios of operation for which the sample of observations is representative" (Davis & Cucu-Grosjean 2019);
- EVT "has nothing to say on unobserved events" (Cazorla et al. 2019);
- time-randomized hardware is "neither sufficient nor necessary" for applying MBPTA (Davis & Cucu-Grosjean);
- i.i.d. tests can pass on samples that are "unfit for pWCET computation, owing to fundamental deficiencies in representativeness" (Cazorla et al.).

Running the `chronovise` MBPTA framework (pinned revision) on synthetic data (`Basis: execution`, synthetic inputs, not hardware measurements):

- **A campaign that never exercised a rare mode passes every test.** Ljung-Box, KPSS, R/S, and the KS/CvM/AD tests on held-out block maxima all pass. The per-block-of-50 pWCET at `1e-9` exceedance is `1134.43`, which the deployed mixture exceeds with per-run probability `9.9e-4`.
- **An AR(1) series is caught by Ljung-Box and R/S but not by KPSS or the KS post-EVT test.**
- **`chronovise`'s BDS independence test has two upstream defects.** `embedding_dimension_1` divides an all-pairs count by the normaliser of a smaller pair set, and `indicator_function` dereferences an iterator before the start of the sample.
  - On truly i.i.d. data at nominal α = 0.05, the upstream test rejected 88.2% (n = 100), 57.5% (n = 250) and 33.3% (n = 500) of replicates for samples located far from zero.
  - It is not translation-invariant: the same normal draws were rejected 39.5% unshifted and 88.7% when shifted by 1000.
  - Fixing both defects restored translation invariance and gave 7.5–11.7%.

## Applicability

**Subjects** (see `REPORT.json`), examined by source reading:

- `CSL-KU/IsolBench` at `682680ebf7cdadaee7443ca9246dc424a05e60fa` (`bench/bandwidth.c`, `bench/latency.c`, `bench/pll.cpp`).
- `mc-imperial/multicore-test-harness` at `38d7eddff9444cd114f4fb391f19f4bc4414bcb1` (`README.md`, `scripts/common.py`, `scripts/run_sut_stress.py`, `scripts/run_tuning.py`, example configurations).
- `federeghe/chronovise` at `4b332f10669af73f33e00f8749040eed9601bfb2`, also built and executed on synthetic inputs (only the part not requiring `ceres-solver`).
- `statsmodels/statsmodels` at `32bd3137bd45e763d22802ecfa99be3f02ad03f2` (`statsmodels/tsa/_bds.py`), used only as a reference implementation of the BDS statistic.
- Published measurement campaigns and critiques, listed under Evidence with an indication of what was read.

**Relationship among subjects.**

- IsolBench and the harness are interference generators.
- `chronovise` is an MBPTA tool whose statistical tests are compared with the critiques; `statsmodels` serves as a second implementation of one of those tests.
- The literature supplies the measured platforms, which this report did not measure.

**Hardware.** No avionics or space processor was available. No interference measurement on real hardware was performed: the only machine available was a shared x86-64 cloud VM (2 sockets × 24 cores × 2 threads, `Intel(R) Xeon(R) CPU @ 2.60GHz` per `lscpu`) whose load average was 100–134 on 96 vCPUs during the work, which would dominate any co-run slowdown measurement. Every hardware slowdown number in this report is quoted from a cited paper with its platform. Synthetic-data results characterize `chronovise`'s statistics, not any processor.

**Toolchain.** `chronovise` was compiled with GCC 15.2.0, `-std=c++14 -O2 -include cstdint`, without `ceres-solver`, so the MLE/GMLE estimators were not built and only PWM was used. `-include cstdint` was needed because `include/statistical/test_bds.hpp` uses `uint_fast8_t` without including `<cstdint>`. GCC 15.2.0 rejects it with "‘uint_fast8_t’ does not name a type". This is toolchain drift, not a logic change.

## Findings

### 1. What a measured interference bound can and cannot mean

Basis: derived from the sources in §2–§4.

Let `C_iso` be the task's longest observed execution time in isolation and `C_E` the longest observed time while co-running enemy set `E`. Measurement campaigns report `C_E` or a slowdown `C_E/C_iso`. For `C_E` to bound the deployed execution time `C_dep` one needs, at minimum:

| Premise | Content | Who discharges it |
| --- | --- | --- |
| P1 Channel completeness | Every shared resource through which co-runners interact has been identified | Platform documentation plus measurement. VanderLeest–Thompson: "processors can contain undocumented resources", and "documentation sometimes contains errors" |
| P2 Enemy dominance | For each channel and each *combination* of channels, the enemies generate interference at least as harmful to this task as any deployable co-runner | No source provides a proof. Radojković et al.: "infeasible in practice". VanderLeest–Thompson assert it for RapiDaemons and concede uncertainty about channel combinations |
| P3 Monotonicity / no timing anomalies | More interference never shortens the task in a way that hides a slower path; the task's worst path is exercised under worst interference | Requires timing-compositional hardware (§5.1) |
| P4 State and path coverage | Input-dependent paths, cache and DRAM-bank states, and OS activity are covered | Test design |
| P5 Environmental control | Frequency scaling, thermal throttling and other platform governors behave in deployment as in the campaign | The harness discards runs above `max_temperature` (§2.3), which removes exactly the throttled cases from the statistic |

If any premise fails, `C_E` is an observation, not a bound. The literature summarized below repeatedly found a later, more aggressive or differently targeted enemy that exceeded an earlier "worst case".

### 2. Resource-stressing programs and auto-tuned interference generators

#### 2.1 Resource-stressing benchmarks (Radojković et al. 2012)

Basis: literature (author preprint read).

- **Kernels.** Per-resource x86 assembly kernels: `nop` (fetch/decode); integer and floating add/multiply/divide (execution units); `L1 dcache`, `L1 icache`, `L2`; `mem bw` (pointer chasing sized to L1, L2 and 4×LLC).
- **Platforms.** Intel Atom Z530 (two hardware threads), Pentium D, Core2Quad Q9550.
- **Method.** "Each experiment was repeated 50 times … we reported and analyzed the Longest Observed Execution Time (LOET) in 50 repetitions" (§3.3).
- **Reported slowdowns:**

  | Platform | Resource or setting | Slowdown |
  | --- | --- | --- |
  | Atom | Pipeline sharing | < 2× |
  | Atom | L1 data cache | 6.2× |
  | Atom | Instruction cache | 2.7× |
  | Atom | L2 | 14.1× |
  | Atom | Memory bandwidth | 15.3× |
  | Pentium D | All | "fairly low (around 30%)" |
  | Core2Quad | L2 benchmark sharing an L2 partition | 14.4× |
  | Atom | Real applications vs stressing kernels | up to 22% (STAP radar), 47% (H264 encode), 18% (CoreMark) |

- **Their claim:** "the slowdown detected when using resource-stressing benchmarks may serve as an upper estimate of the effect of inter-task interference" because it "is unlikely to be exceeded for any workload composed of real applications".
- **Counter-evidence within the paper:**
  - The classical approach (measuring with real co-runners) "can lead to an underestimation of WCET". On Atom, the stressing kernels exceeded the classical maximum by up to 14% (CoreMark).
  - "For two out of three real benchmarks under study, H264 encode and CoreMark, the slowdown caused by mixed stressing workload exceeds the highest slowdown of homogeneous workloads" (§4.4). A per-resource maximum is therefore not a combination maximum.

#### 2.2 IsolBench

Basis: source + literature.

At the pinned revision:

- **`bench/latency.c`** builds a singly linked list over a working set of `g_mem_size / CACHE_LINE_SIZE` 64-byte items. The order is a pseudo-random permutation (`srand(0)`; swap with `rand() % workingset_size`). The kernel chases it (`pos = pos->next`) and reports average latency per access. Because each load depends on the previous one, it has one outstanding miss.
- **`bench/bandwidth.c`** touches one `int` per 64-byte line across a buffer (`bench_read`: `sum += g_mem_ptr[i]`; `bench_write`: `g_mem_ptr[i] = i`; stride `CACHE_LINE_SIZE/4`). Defaults: 16384 KB, 5 s, read.
  - The counter is named `g_nread` ("number of bytes read") but is also incremented by `bench_write`, so the printed bandwidth in write mode counts written lines.
- **`bench/pll.cpp`** runs `mlp` independent pointer chases interleaved (`next[j] = list[j][next[j]]` for `j < mlp`; `-l` option, `MAX_MLP 64`). This controls memory-level parallelism, with a write variant that stores to each visited line.
- **Valsan, Yun & Farshchi (2016)** used Latency and Bandwidth combinations ("IsolBench") on an Intel Nehalem, Cortex-A15, Cortex-A9 and Cortex-A7 with the LLC partitioned by PALLOC. Partitioning isolated Cortex-A7 and Nehalem in the Latency-vs-BwRead experiment, "For Cortex-A15 and A9, however, the response time is still increased by up to 3.7X and 2.0X". With BwRead(LLC) victims, "Cortex-A9, A15, and Nehalem now suffer up to 2.1X, 10.6X, and 7.9X slowdowns"; "using BwWrite generally results in even worse interference". The abstract reports "up to 21X WCET increase in a real COTS multicore platform due to MSHR contention". The platform for the 21× figure was not recovered from the text read.
- **Bechtel & Yun (2019)** found that "the cache writeback buffer" is a denial-of-service target. They report "up to 346X (times, not percent)" on a Raspberry Pi 3 (in-order Cortex-A53), "regardless of whether we partition its shared cache or not". Real benchmarks reached 81× (SD-VBS) on the same board. Cache partitioning "was actually detrimental when attacker BwWrite tasks were present as 7 of the 8 benchmarks suffered worse slowdowns with partitioning enabled".

These are the cases in which a previously accepted mitigation or worst case was exceeded by a new enemy design:

| Earlier worst case | What exceeded it | Source |
| --- | --- | --- |
| Partitioned LLC with read enemies | Write enemies (MSHR, write-back buffer) | Valsan 2016; Bechtel 2019 |
| Partitioning as a mitigation | Partitioning made 7 of 8 benchmarks worse under write enemies | Bechtel 2019 |
| Homogeneous stressing workloads | Mixed workloads | Radojković 2012 |
| Hand-written enemies | Tuned enemies, in 35 of 105 benchmark/chip pairs | Iorga 2020 |

#### 2.3 Auto-tuned enemies: `multicore-test-harness` (Iorga et al. 2020)

Basis: source + literature (abstract, author blog, artifact; full paper not read).

The paper's abstract reports three findings:

- "different methods of measurement yield significantly different magnitudes of, and variation in, observed interference effects";
- they "propose a method of measurement based on percentiles and confidence intervals";
- they compare random search, simulated annealing and Bayesian optimisation on five multicore chips (x86 and ARM). "Our method achieves a statistically larger slowdown compared to prior work in 35 out of 105 benchmark/chip combinations, with a maximum difference of 3.8×", and they "envision that empirical approaches, such as ours, will be valuable for 'first pass' evaluations".

The released harness at the pinned revision makes the statistic precise:

- **Objective = high quantile of outlier-trimmed times.**
  - `MappingResult.log_result` sets `self.no_outliers_measurements = remove_outliers(total_times)` and `self.q_value = mquantiles(self.no_outliers_measurements, quantile)[0]` (`scripts/common.py` lines 255 and 258).
  - The tuner keeps the configuration with the largest `result.q_value` (`scripts/run_tuning.py` lines 451–482, comparison at line 474).
  - The default `quantile` is `0.9` (`common.py` line 54). The example configurations also use `0.9` with `"confidence_interval": 0.95`.
- **Outlier removal discards the tail.** `remove_outliers(times, scale=3)` keeps only `median_value - scale * scaled_mad <= x <= median_value + scale * scaled_mad`, with `c = -1 / (sqrt(2) * erfcinv(3 / 2))` (`common.py` lines 316–333; the filter is line 331). The extreme observations that a worst-case claim depends on are excluded before the quantile is taken. The raw times are still kept in the result object (`self.measurements = total_times`, line 254), so a maximum can be recomputed offline; the tuning objective does not use it.
- **Confidence interval on the quantile.** `confidence_variation` sorts the outlier-free times and widens order-statistic ranks until `binom.cdf(ui-1, n, quantile) - binom.cdf(li-1, n, quantile)` reaches the requested confidence (`scripts/run_sut_stress.py` lines 34–87). Under `"stopping": "no_decrease"` measurement stops once the interval width is below `max_confidence_variation` percent of the quantile. Under `"pessimistic"` it scans `candidate_quantiles = [x / 100.0 for x in range(95, 49, -1)]` and accepts the *first* quantile, from 0.95 down to 0.50, whose interval is narrow enough (lines 247, 323–340).
- **Thermal filter.** A run is recorded only `if final_temp < experiment_info.max_temperature` (default 80). Otherwise it is redone after cooling (`run_sut_stress.py` lines 287–297). The author's blog explains the motivation: "if the processor gets very hot, its frequency will automatically be decreased".
- **Victim placement.** "Run the program on core 0" (`run_program_single(experiment_info.sut, 0)`, line 277). Before each run, `sync; echo 1 > /proc/sys/vm/drop_caches` clears the OS page cache, not the CPU caches (line 270).

Consequence (derived): the harness is engineered for reproducible, discriminating comparisons of enemy strength, which is the purpose stated in the abstract. By construction it does not estimate the maximum. A tuned enemy that maximizes the trimmed 0.9-quantile need not maximize the rare worst case, and runs whose slowdown comes from thermal throttling are excluded.

### 3. Space and avionics measurement campaigns

Basis: literature.

| Campaign | Platform | Channels stressed | How co-runners were chosen | Reported worst observations | Caveats stated by the authors |
| --- | --- | --- | --- | --- | --- |
| Fernández et al., EMSOFT 2012 | NGMP: quad-core LEON4 (SPARC V8), 16 KB private write-through L1 D-cache, 256 KB shared L2, 128-bit AMBA AHB with round-robin arbitration, one memory channel. **FPGA prototype on an ML510 (Virtex-5) at 70 MHz**; Linux 2.6.36 and RTEMS 4.10 | Bus (`L2_40`), L2 + bus + memory (`L2_200`), memory controller (`L2miss`, 1 MB), stores (`L2st`) | Hand-designed micro-benchmarks; EEMBC AutoBench with all combinations of the 4 kernels on the other 3 cores (20 experiments) | Bus: 1.83× (Linux), 1.95× (RTEMS). Bus + memory controller: 2.6× / 3.4×. Bus + L2 + memory: 4.3× / "more than 9×". Store-heavy: "higher than 19×". EEMBC: max 5.5× | "the effect of memory controller interferences on the execution time of programs will be higher in the final implementation of NGMP than in our FPGA implementation". The kernels are said to generate "the worst possible delay any application might suffer" for the stressed resource, without proof |
| VanderLeest & Thompson, DASC 2020 | Methodology. Examples: NXP T2080 histogram; Zynq UltraScale+ (4× Cortex-A53) | Per-channel "RapiDaemons" | Commercial generators | No numeric slowdowns in the text read | Asserts an upper bound under RapiDaemons; concedes channel-combination uncertainty and undocumented resources |
| Nowotsch & Paulitsch, EDCC 2012 | not read | not read | not read | not read | Full text not available; nothing from this paper is used |

The NGMP numbers come from a 70 MHz FPGA prototype whose memory subsystem the authors expect to be *less* interference-prone than the final silicon. They must not be transferred to the GR740 silicon without re-measurement. The silicon differs materially (Frontgrade Gaisler documentation; user manual read only to p. 67):

- a "2 MiB Level-2 cache" with "4-ways … supports locking of 1-4 ways", partitionable "based on bus master indexes", versus the prototype's 256 KB L2;
- a "Non-blocking L2 cache using SPLIT protocol";
- 250 MHz system frequency.

The vendor's validation note reports that "split transactions reduce the impact of interference, up to 3.35x times less interference in the worst-case" (GR740-VALT-0010, p. 12; per-configuration values are graphical and were not extracted).

### 4. MBPTA and EVT: assumptions, critiques, and validity tests

#### 4.1 The procedure and its assumptions

Basis: literature.

- **Original procedure (Cucu-Grosjean et al., ECRTS 2012).** Only the abstract and the authors' slides were read; the paper body was not. The abstract claims "a sound measurement-based probabilistic timing analysis technique based on Extreme Value Theory", with bounds "less than 15% pessimistic" relative to the tightest probabilistic bounds and "less than 650 runs" for the benchmarks used. The slides list the steps "I.i.d tests", "Gumbel Fitting (ET)", "CRPS", "Convergence criteria", "More runs". For identical distribution: "Hypothesis testing with Kolmogorov-Smirnov test / Two subsets of data randomly obtained from the trace … Threshold (0.05) is chosen based on experience/common practice". For Gumbel fitting: "Hypothesis testing with exponential tail test". The experiments ran "on a modified version of the SoCLib processor simulator". The conclusion slide adds "But value of pWCET bound is limited to the path coverage achieved in the observations". Davis & Cucu-Grosjean (§4.1) identify the independence test as the Runs test.
- **Generic procedure (Cazorla et al. 2019, §3.4).**
  - (1) "Statistical verification: where the set of collected observations are checked against the prerequisites for the application of EVT (i.e., i.i.d. and stationarity)";
  - (2) data filtering with block maxima or peak-over-threshold;
  - (3) parameter selection;
  - (4) distribution fitting;
  - all "while always paying attention to representativeness".
- **Relaxed independence.** "Early work in this area required execution time observations to be independent and identically distributed (i.i.d.). Later work relaxed this assumption, but still required that the sequence of execution time observations exhibit stationarity and weak dependences. Further, the results are only valid for future scenarios of operation for which the sample of observations is representative" (Davis & Cucu-Grosjean, §4).
- **Hardware randomization.** "time-randomised architectures (e.g. with random replacement caches) are neither sufficient nor necessary for the application of MBPTA methods" (Davis & Cucu-Grosjean, §4.4). "The architecture alone cannot ensure that the execution times will be i.i.d. for all real-time programs" (§6.1).
- **`chronovise`'s own statement of requirements** (JOSS 2018): measurements must be "(1) independent and identically distributed, (2) representative of all worst-case latencies … Both requirements are necessary to obtain a safe, i.e. non-underestimated, pWCET".
- **MBPTA-CV** (Abella et al. 2017; author manuscript read).
  - Tests: "the Ljung-Box independence test … for 20 different lags simultaneously" and "the Kolmogorov-Smirnov two-sample i.d. test", at α = 0.05.
  - Tail model: it enforces an exponential tail (ξ = 0), arguing "since the maximum value is generally unknown, we cannot discriminate between exponential and light tails. Therefore … we must use exponential distributions to model the tail".
  - Footnote 5: "Statistical tests provide information about the data sample at hand rather than about the distribution being observed. Therefore, those tests may be passed either by chance or by introducing some form of randomisation in the data collection process."

#### 4.2 Published soundness critiques

Basis: literature. Where only an abstract, slides or a survey's summary was read, the item says so.

| Critique | Assumption attacked | Statement (source actually read) | Proposed check or remedy |
| --- | --- | --- | --- |
| Griffin & Burns 2010 (abstract + slides) | Continuity; i.i.d. | Abstract: "The Gumbel distribution is assessed in terms of its assumption of continuous behaviour and its need for independent and identically distributed data". Slides: "Runtimes are not independent / Processor caches in particular violate this"; "separate paths through the program have different distributions of runtimes"; earlier work "does not guarantee that the results are safe" | Resets, per-path analysis, code coverage, shifting the continuous bound (slides 13, 15). The surveys disagree on the direction of the continuity effect: Cazorla et al. say "pessimistic"; Davis & Cucu-Grosjean frame it as soundness |
| Reineke 2014 (abstract; arguments via Davis & Cucu-Grosjean §7.1) | Randomized caches enable MBPTA | Abstract: "We refute these claims and conclude that with prevailing static and measurement-based analysis techniques caches with deterministic placement and least-recently-used replacement are preferable over randomized ones." Davis summary: with random placement "MBPTA cannot necessarily detect that there may be rare layouts (e.g. with a probability of 10−6) that result in a large number of cache misses" | — (a rebuttal by Mezzetti et al. 2015 is noted by Davis; not read) |
| Davis & Cucu-Grosjean 2019 (read, pp. 03:1–03:45) | Representativity; reproducibility | "If potential sources of significant execution time variability do not exhibit this variability during analysis … they will not be accounted for in the estimated pWCET distribution produced, which may as a result be optimistic (i.e. unsound)." "There has also been little work on the reproducibility of the method … on how far the pWCET distributions can realistically be extrapolated to very low probabilities e.g. 10−9, 10−12, 10−15" | Coverage of input states, hardware states and worst-case paths; "cannot be left to the user" |
| Cazorla et al. 2019 (read in full) | Representativity vs i.i.d. tests | "EVT has nothing to say on unobserved events." An approach "may indeed produce data samples capable of passing i.i.d. tests … and thus lead to mechanically successful applications of EVT but that are unfit for pWCET computation" | Representativeness arguments external to EVT |
| Hansen et al. 2009, via Davis §4.1 | Gumbel adequacy | "there were some tasks where the rate at which execution times … exceeded some large value was greater than the exceedance probability predicted by the Gumbel distribution, i.e. the pWCET distribution was optimistic" | Validation against >2 million additional measurements |
| Santinelli et al. 2014 (abstract + slides; Cazorla summary) | Independence | Dependencies "may cause pWCET underestimation" (Cazorla summary). Slides: block size and threshold "selected arbitrarily" affect "accuracy and safety" | Extremal-independence / stationarity conditions |
| Lima, Dias & Barros 2016 (via Davis §4.3; not read) | Gumbel / light tail | Davis: fitted models "belong to all three classes of EV distribution … There were also cases where the models belonged to none of them and EVT could not be used to provide sound results" | Fit full GEV; extreme-value-condition tests |
| Reghenzani et al. 2019, ESL (abstract only) | Exponential-tail upper bounding (as in MBPTA-CV) | "we show that this assumption is valid only under certain conditions and that it is often misinterpreted. This leads to unsafe estimations of the worst-case execution time" | Force ξ after estimation, or estimate the error (author's thesis, secondary) |
| Reghenzani et al. 2020, Micpro (abstract only; test list from the first author's PhD thesis, secondary) | Test choice and power | Thesis: Ljung-Box "checks for the presence of a particular form of independence, i.e., the serial correlation". The two-sample KS split-half test is "ineffective and improperly used". Running three tests at α = 0.05 gives "αglobal ≈ 0.14" | KPSS (stationarity) + BDS (short-range dependence) + R/S (long-range dependence), merged into a "Probabilistic Predictability Index"; GoF by KS, CvM, AD, MAD. KS "has, in general, less statistical power"; "at least 1000 time measurements" in the tail |
| Abella et al. 2015, SIES (abstract only) | User-supplied assumptions | "trustworthiness rests a great deal also on the viability of the assumptions that the method makes on the system and on the user's ability" | The specific pitfall list was not read |

**Empirical validation reported for MBPTA-CV.** "We collected 10^7 runs for each benchmark, each taking around 20 seconds per run. In a powerful cluster with 500 jobs running in parallel it took around 10 days." The estimates "upper-bound the observed distributions with a difference at 10−7 of 1.1% and 25.8%" for the two benchmarks. On average, MBPTA-CV used 1,063 runs per benchmark versus 1,644 for the original procedure. The platform was a cycle-accurate simulator "that models a 4-core processor architecture resembling that of the Cobham Gaisler NGMP". This is the only quantitative large-sample validation found among the items read; it validates against more measurements of the same setup, not against unobserved conditions.

#### 4.3 What `chronovise` tests, and how

Basis: source.

At the pinned revision:

- **Hooks.** `AbstractExecutionContext` runs user-registered sample tests on the raw measurements, then block-maxima or peak-over-threshold extraction, then estimation (PWM, or MLE/GMLE when built with `ceres-solver`), then post-EVT goodness-of-fit tests on a held-out portion (`src/aec.cpp` 216–276).
- **Implemented tests:**
  - Ljung-Box (`TestLjungBox(significance_level, n_lags)`);
  - KPSS (`TestKPSS(significance_level, n_lags, trend_class = LEVEL)`);
  - R/S (`TestRS`);
  - BDS (`TestBDS`, only `significance_level == 0.05`; `run` throws "Not implemented" otherwise, `test_bds.cpp` 184–186);
  - Kolmogorov–Smirnov, Cramér–von Mises and Anderson–Darling (optionally "modified") on the fitted distribution.
- **No test-until-pass loop.** When a sample test or post-EVT test rejects, `run()` stops collecting samples (`keep_going = false`) and marks input representativity as not established (`aec.cpp` 179–212). Sample size grows by 20% (`COEFF_INCREASE_SAMPLE_SIZE 0.2`) only when there are too few samples for the estimator or tests (lines 236–253). This avoids the inflated acceptance of repeatedly re-testing until a test passes.
- **"Rejection" semantics.** The base class warns: "@note A false value does not mean that the hypothesis has been accepted" (`include/statistical/test.hpp`, `is_reject`). Ljung-Box, R/S, KPSS and BDS report `has_power() == false`; R/S, KPSS and BDS throw on power requests. The reliability that `Safety` derives from test power is therefore unavailable when those tests are used.
- **pWCET probability is per block.** `pWCET::get_wcet(p)` returns `ref_dist->quantile(p)` of the fitted distribution (`src/evt/pwcet.cpp`). With block maxima the fitted GEV describes the maximum of `block_size` runs, so the returned exceedance probability is per block. For i.i.d. runs the per-run exceedance at that value is smaller (≈ `p/block_size`), which is the conservative direction (derived). The sample program prints "pWCET(p=1-10^(-9))" without stating the block size.
- **Toolchain observation.** Building at the pinned revision with GCC 15.2.0 fails in `test_bds.hpp` unless `<cstdint>` is force-included (Applicability).

#### 4.4 Upstream defects: `chronovise`'s BDS test is mis-normalized and reads before the beginning of the sample

Basis: source + execution.

At `federeghe/chronovise@4b332f10669af73f33e00f8749040eed9601bfb2`, `src/statistical/test_bds.cpp` contains two independent defects in the BDS statistic `W = √(n−m+1)·(C_m − C_1^m)/σ_m`, which `run` evaluates for embedding dimension `m = 2` at line 199:

```cpp
this->statistic = std::abs(std::sqrt(size-m+1) * (this->embedding_dimension(m, epsilon) - std::pow(this->embedding_dimension_1(m, epsilon),m)) / sigma);
```

**Defect 1: inconsistent normalization of `C_1`.**

```cpp
70  template <typename T_INPUT, typename T_TIME>
71  double TestBDS<T_INPUT, T_TIME>::embedding_dimension_1(unsigned long m, double epsilon) const noexcept {
73      const size_t size = measures_save->size();
75      double coeff = 2./((size-m+1.)*(size - m));
79      for (unsigned long s = 1; s <= size; s++) {
81          for (unsigned long t = s+1; t <= size; t++) {
...             (counts pairs with |x_t - x_s| < epsilon)
94      return coeff * sum;
```

The loops sum over all `n(n−1)/2` pairs of the full sample, but `coeff` is the reciprocal of the `(n−m+1)(n−m)/2` pairs of an `m`-embedded sample. `C_1` is therefore inflated by `n(n−1)/((n−m+1)(n−m))`, which is `n/(n−2)` for `m = 2`.

The variance term uses `embedding_dimension(1, epsilon)` (`sigma()`, line 153), which is correctly normalized for `m = 1`, so the two uses of `C_1` inside the same test disagree. The reference implementation in `statsmodels` (`statsmodels/tsa/_bds.py`) takes `C_1` as the mean over the pairs actually used, on the sample truncated to the same `n−m+1` points (`correlation_sum(indicators[ninitial:, ninitial:], 1)`, line 242).

**Defect 2: out-of-range iterator.**

```cpp
19  uint_fast8_t TestBDS<T_INPUT, T_TIME>::indicator_function(unsigned long s, unsigned long t, unsigned long m, double epsilon) const noexcept {
23      assert(t >= m-1);
24      assert(s >= m-1);
28      auto iterator_a = std::next(measures_save->cbegin(), t - 1);
29      auto iterator_b = std::next(measures_save->cbegin(), s - 1);
31      for (unsigned long i=0; i<=m-1; i++) {
...         (compare *iterator_a, *iterator_b against epsilon)
42          iterator_a = std::prev(iterator_a);
43          iterator_b = std::prev(iterator_b);
```

`embedding_dimension(m, ·)` calls this for every `s` from 1 (`for (unsigned long s = 1; s <= size; s++)`, line 59). For `s < m` the loop decrements `iterator_b` past `cbegin()` of the underlying `std::multimap` and dereferences the result. That is undefined behaviour. The assertion at line 24 admits `s = m−1 = 1` for `m = 2`, which is exactly the out-of-range case.

**Observable consequence: a statistic that depends on where the data sit.** BDS is defined through absolute differences, so adding a constant to every observation must not change it. Probe `support/bds_size.cpp` runs the library's `TestBDS` on synthetic i.i.d. data (`std::mt19937_64`, fixed seeds; α = 0.05, the only level the test accepts) and counts rejections. Results (`support/bds_size.out`):

| Data (i.i.d.) | n | Replicates | Upstream | Defect 1 fixed only (`bds_patch_coefficient_only.diff`) | Both fixed (`bds_patch.diff`) |
| --- | --- | --- | --- | --- | --- |
| `1000 + Gamma(4, 5)` | 100 | 400 | **0.882** (353), mean `|W|` 3.48 | 0.117 (47) | 0.117 (47), mean `|W|` 1.00 |
| `N(0, 1)` | 100 | 400 | **0.395** (158), mean `|W|` 1.68 | 0.460 (184) | 0.105 (42), mean `|W|` 0.99 |
| `1000 + N(0, 1)` (same draws shifted) | 100 | 400 | **0.887** (355), mean `|W|` 3.64 | 0.105 (42) | 0.105 (42), mean `|W|` 0.99 |
| `1000 + Gamma(4, 5)` | 250 | 200 | **0.575** (115) | 0.075 (15) | 0.075 (15) |
| `N(0, 1)` | 250 | 200 | 0.140 (28) | not run | 0.100 (20) |
| `1000 + Gamma(4, 5)` | 500 | 60 | **0.333** (20) | 0.117 (7) | 0.117 (7) |

Readings:

- **Upstream is not translation-invariant.** The same `N(0,1)` draws are rejected 39.5% of the time unshifted and 88.7% of the time when shifted by 1000.
- **Fixing only the coefficient removes the excess for data far from zero but not for data near zero.** That residue is consistent with defect 2: the out-of-range read yields a value that compares "within ε" only when the data lie near zero. This is an inference about undefined behaviour under GCC 15.2.0 `-O2`, not a guaranteed behaviour.
- **With both changes, translation invariance returns** (identical counts for shifted and unshifted draws), and rejection rates fall to 0.075–0.117. For reference, `E|W| = 0.80` for a standard normal statistic. The remaining excess over 0.05 was not investigated; a small-sample size distortion of the asymptotic BDS test is one candidate.
- **The upstream unit test does not detect the defects.** `tests/test_test_bds.cpp` checks a single fixed 100-value normal sample (`DistributionACCEPT`), which upstream accepts with `W = 0.41`. With both fixes it is also accepted (`W = 1.42`). A single-sample unit test cannot measure a test's size.

**Consequence.** With the upstream test, an MBPTA run that includes BDS will reject most genuinely i.i.d. campaigns of a few hundred samples whose values lie far from zero, as execution times do. That blocks a valid analysis; it is a conservative failure, not an unsafe acceptance. Because the outcome depends on undefined behaviour, results may also differ between compilers or library versions.

**Cost.** `TestBDS::k` is a triple loop over the sample (lines 125–141), O(n³). Measured driver times (single-threaded, loaded host): n = 250, 0.11 s; n = 500, 0.91 s; n = 1000, 9.68 s. An n = 5000 run was stopped after more than 150 s.

#### 4.5 Synthetic-data probes of the tests' blind spots

`support/mbpta_driver.cpp`, `support/gen_samples.py`. Basis: execution (chronovise on synthetic data).

**Setup.**

- Samples: n = 20000.
- Sample tests at α = 0.05: Ljung-Box (20 lags), KPSS (level, 20 lags), R/S.
- Split: 50/50 training/test.
- Block maxima of size 50 (200 maxima per half); GEV by PWM.
- Post-EVT tests: KS, CvM, AD on the 200 held-out maxima.

| Dataset | Ljung-Box | KPSS | R/S | GEV (loc, scale, ξ) | KS / CvM / AD | pWCET, per-block 1e-9 |
| --- | --- | --- | --- | --- | --- | --- |
| i.i.d. `1000 + Gamma(4, 5)` | pass (15.0 < 31.4) | pass | pass | 1045.81, 7.96, −0.035 | pass / pass / pass | 1162.68 |
| AR(1), φ = 0.8, Gamma innovations | **reject** (35960) | pass (0.109 < 0.461) | **reject** (3.73 > 1.75) | 1048.19, 12.30, −0.078 | pass / **reject** / **reject** | 1174.25 |
| "Campaign": i.i.d. base only; deployment adds a +200 mode with probability `1e-3` | pass | pass | pass | 1045.62, 7.43, −0.059 | pass / pass / pass | 1134.43 |

For the third row the true per-run exceedance of `1134.43` under the deployed mixture is `9.86e-4` (Monte Carlo, `10⁷` draws, `support/exceed.out`). In the campaign distribution no draw exceeded it.

Readings:

- **KPSS tests stationarity, not independence**, and accepted a strongly autocorrelated but stationary series.
- **KS on 200 maxima did not detect the misfit** that CvM and AD detected.
- **No test can see an unexercised mode or co-runner.** The representativity premise (P4/P2 of §1) is outside what the statistics test. The probe's numbers are properties of the synthetic distributions only.

### 5. Multicore timing analyses and the hardware assumptions their soundness needs

#### 5.1 Classification

Basis: literature (quotes from the papers read).

**Survey verdict.** Maiza et al. (2019) review four categories: "full integration, temporal isolation, integrating interference effects into schedulability analysis, and mapping and allocation". They exclude "measurement-based and measurement-based probabilistic timing analysis methods" from scope (§1.2). Their verdict on hardware assumptions (§6.1.5): "The papers reviewed in this survey … typically assume, either explicitly or implicitly, a timing compositional architecture, free of any timing anomalies or domino effects. This is a strong hypothesis, since as far as we know, there is currently no proof that any existing COTS multi-core hardware platform has this property."

| Analysis family (representative work) | Soundness needs (quoted or paraphrased from the source read) | What breaks it on COTS multicore |
| --- | --- | --- |
| Static RTA with interference terms (Davis et al. 2018) | "timing-compositional cores"; "atomic bus transactions, i.e., no split transactions, which furthermore are not re-ordered"; "write-through caches only"; no coherence delays | "recent results by (Hahn et al. 2015) indicate that even simple commercial multicores are non-compositional, rendering most existing analyses unsound for these architectures" (same paper, §2.6) |
| DRAM interference bounds (Kim et al. 2014) | "each core is in-order with one outstanding cache miss and any delays from shared resources are additive"; FR-FCFS controller, open-row policy, single channel; prefetchers, SMT and DVFS disabled | Out-of-order cores and MSHR-level parallelism (Valsan 2016) |
| Memory-interference delay (Pellizzoni et al. 2010) | "a CPU architecture where execution time and communication time are decoupled", or timing anomalies captured by static bounds; RR/FCFS/FP arbitration | Timing anomalies (Lundqvist & Stenström 1999) |
| Bandwidth regulation (MemGuard, Yun et al. 2016) | Guaranteed bandwidth = worst case "all memory requests target a single memory bank"; per-core LLC-miss counters with "all hardware prefetchers" disabled | "LLC miss counts do not capture LLC write-back traffic which may underestimate actual memory traffic", the channel exploited by Bechtel & Yun |
| Upper-bound delay per request (Fernández et al. 2017) | Round-robin or FIFO arbitration, "each core can have only up to one pending request in flight"; `ubd = (Nc − 1) × lmax`; measured `ubd_m` when latencies are undocumented | FR-FCFS and some priority arbiters give "more pessimistic – or simply not computable – ubd" |
| Measurement with enemies (§2–§3) | Premises P1–P5 of §1 | Undocumented channels, combination effects, tuned enemies, thermal effects |
| MBPTA / EVT (§4) | i.i.d. or stationarity with weak dependence; representativity; for the original argument, time-randomized hardware (neither necessary nor sufficient per Davis & Cucu-Grosjean) | Unobserved modes (§4.5), mis-sized tests (§4.4) |
| Timing anomalies (Lundqvist & Stenström 1999) | "A timing anomaly is a situation where, in the first case, C > i or C < 0, or in the second case, C < −d or C > 0"; "Condition 1 If a processor only contains in-order resources no timing anomalies can occur" | Any out-of-order resource voids the sufficient condition |

**COTS reality** (Fernández et al. 2014, WCET workshop): "For many resources the manuals of the processor under analysis rarely provide all the required information to analytically derive those bounds", so bounds are derived "based on experimentation". Their examples include "the FreeScale P4080 and some FPGA versions of the Aeroflex Gaisler LEON4". Such approaches "all require building confidence arguments that accord with the requirements and practices of the application domain".

#### 5.2 What the certification guidance asks, and what a measured bound must add

Basis: normative (texts read).

- **CAST-32A** (November 2016; "does not constitute official policy or guidance from any of the authorities").
  - Definition: "A platform property that may cause interference between independent applications is called an interference channel."
  - **MCP_Resource_Usage_3**: "The applicant has identified the interference channels that could permit interference to affect the software applications hosted on the MCP cores, and has verified the applicant's chosen means of mitigation of the interference." Note a) covers "shared memory, shared cache, an interconnect, or the use of any other shared resources, including shared I/O".
  - **MCP_Resource_Usage_4**: "NOTE: The need to use Worst Case scenarios is implicit in this objective."
  - **MCP_Software_1**: "The WCET of a software component may be determined separately on the MCP if the applicant shows that time interference is mitigated for that software component, otherwise, the WCET should be determined by analysis and confirmed by test on the target MCP with all software components executing in the intended final configuration."
- **EASA AMC 20-193** (Annex I to ED Decision 2022/001/R) and **FAA AC 20-193** (dated 1/8/24) carry the same objectives in substance. Note a) says "shared peripherals" instead of "shared I/O". AMC 20-193 describes itself as "an acceptable means, but not the only means". AC 20-193 adds that to "determine the WCET separately" means "without all the software executing at the same time on other cores".
- **Method neutrality.** None of the three documents read prescribes a statistical or probabilistic method for bounding interference. All three ask for WCET "determined by analysis and confirmed by test" when interference is not mitigated, so a measured bound alone fills only the "confirmed by test" half.

Derived checklist. To connect a measured interference bound to the guidance's interference-channel identification and mitigation objectives, an argument needs at least the following:

1. **A channel inventory with evidence of completeness.** The evidence should be documentation plus per-channel saturation tests, in the VanderLeest–Thompson style of "if no effect is seen … the interference channel is not present". Record the known limit: undocumented resources (P1).
2. **Per-channel and combined enemies with an argued dominance relation to the deployable co-runner set**, or enforced budgets that make the deployed co-runners provably weaker. Examples: bandwidth regulation of LLC misses and write-backs, as in the MemGuard extension used by Bechtel & Yun, with reported thresholds "1000R/100W, 500R/100W, and 500R/50W". Without such enforcement, P2 rests on search, and tuned search has beaten hand-written enemies (Iorga et al.).
3. **A hardware-model argument for monotonicity** (P3), or explicit margins where the platform is known not to be timing-compositional.
4. **Statistic definitions that do not trim the tail.** Report maxima and the number of runs, not only outlier-trimmed quantiles (§2.3). State the run count; Radojković et al. used 50 runs per configuration.
5. **If EVT is used:** i.i.d. evidence with tests of known size and power (§4.4 shows a test whose size was wrong), a representativity argument for inputs and co-runners, and a stated per-run versus per-block exceedance (§4.3).
6. **Environmental control of frequency, thermal and power governors**, matched between campaign and deployment (P5).

### 6. Performance and resource footprint (L1–L6)

| Level | Interference measurement | EVT / MBPTA tooling | Source |
| --- | --- | --- | --- |
| L1 authoring | not measured. Harness configs are short JSON (e.g. 17 keys in `tune_cache_large.json`). Radojković kernels are hand-written assembly | not measured | source |
| L2 build | IsolBench `latency` + `bandwidth`: 0.39 s wall, 40.5 MB peak RSS (`make latency bandwidth`, GCC 15.2.0 `-O3`) | `chronovise` library (23 sources, no ceres, one `g++` at a time, `-O2`): 60.1 s wall, 54.6 s user, 485 MB peak RSS, `libchronovise.a` 4.88 MB; driver link 0.93 s, binary 1.37 MB | execution (loaded host) |
| L3 campaign / tuning latency | Radojković: 50 runs per configuration plus 10,000 isolation runs for OS noise. Harness examples: `tuning_max_time` 120–600 (minutes per README), `measurement_iterations_step` 20, `measurement_iterations_max` 200. Fernández: 20 EEMBC combination experiments (repetitions not stated) | n/a | literature, source |
| L4 victim execution | Slowdowns per §2–§3 (all quoted, platform-specific) | n/a | literature |
| L5 analysis cost | n/a | `chronovise` driver on n = 20000 (Ljung-Box, KPSS, R/S, PWM GEV, KS/CvM/AD): 3.6–4.8 s wall. BDS O(n³): 0.11 s (n = 250), 0.91 s (500), 9.68 s (1000). BDS size study: 24.3 s for 200 × n = 250 | execution (loaded host) |
| L6 memory / footprint | IsolBench default buffers 16 MB (bandwidth) and 16 MB (latency; 4 MB when built for `__arm__`); binaries 38 KB (`bandwidth`) and 33 KB (`latency`) | Driver peak RSS 3.9–7.1 MB | source, execution |

### 7. Comprehensibility and conceptual simplicity (C1, C2)

- **C1: legibility of the claim.** "Slowdown 4.3×" is easy to read, but its meaning depends on the statistic (maximum, trimmed quantile, or mean), the run count, the enemy set, the OS, and the platform revision (FPGA prototype versus silicon). None of these travels with the number unless the report states them. The harness's tuned-quantile semantics (§2.3) and `chronovise`'s per-block exceedance (§4.3) are two places where a reader is likely to over-read the number.
- **C1: diagnosis.** When a test rejects, `chronovise` reports which hook failed and stops. When interference is unexpectedly high, the platform documentation needed to explain it is often unavailable: "we are not aware of the exact mechanism … since low-level details are generally not available for most commercial systems" (Iorga, blog).
- **C2: one invariant.** The invariant every method in §5 tries to establish is a per-task budget `C_dep ≤ B` under every admissible co-runner behaviour. The approaches differ only in where they place the burden:
  - static analyses put it in a hardware model;
  - regulation (budgets, partitioning, arbitration bounds) puts it in enforcement;
  - measurement puts it in enemy dominance;
  - MBPTA puts it in a statistical model.

  A minimal unifying abstraction is an *interference contract* per shared resource: the access rate and pattern a co-runner may present, enforced or assumed. Each method then becomes "bound `C` given the contract" plus "establish the contract". The contract makes the hidden premise P2 explicit rather than adding a mechanism. Where it cannot be enforced (undocumented resources, write-back buffers), the exception remains and must be stated rather than absorbed.

### 8. How the bounds and the tools are validated (V1–V4)

- **V1: specification adequacy.** The BDS defects show that a statistical test can be mis-implemented and still pass its unit tests. `tests/test_test_bds.cpp` has one fixed accept sample and two deterministic reject sequences. The non-vacuity check that exposes the defects is an empirical size study under H₀ plus a translation-invariance check (§4.4); neither is in the upstream suite. The synthetic-mixture probe (§4.5) is a specification mutant for "passed all tests ⇒ representative". `chronovise`'s README already notes that tests "based on random samples" can fail "with a probability of 5%", which is a size statement the BDS test does not meet.
- **V2: differential validation.**
  - Comparing `chronovise`'s BDS with `statsmodels`' localized the defect.
  - Iorga et al.'s comparison of tuned against prior enemies is a differential test of enemy strength.
  - No differential comparison of two MBPTA tools on the same hardware traces was performed (not examined).
- **V3: silicon and physical validation.** All interference evidence is post-silicon measurement on the cited platforms (or FPGA prototype). Thermal effects are treated as noise in the harness and as a channel in the Iorga blog's motivation. No measurement was performed here (Applicability).
- **V4: field and operational evidence.** VanderLeest–Thompson report an 8-core platform where "when an L2 cache RapiDaemon interference generator was instantiated on a particular core, the entire RTOS stalled until the RapiDaemon was killed". A channel effect of that kind is not a bounded slowdown at all. No incident data were collected beyond this anecdote (not examined).

## Boundaries

- **Not measured.** No interference measurement on any processor was performed here: the only available host was an oversubscribed shared cloud VM. Every hardware slowdown is quoted. Whether IsolBench or the harness reproduces the cited slowdowns on any given platform is **unknown** from this report.
- **Not read.**
  - The full text of Iorga et al. 2020. Only the abstract, an author blog post and the artifact were read; the five chips and per-chip maxima are not reported here.
  - Nowotsch & Paulitsch 2012 (no open copy; nothing is attributed to it).
  - The full texts of Griffin & Burns 2010, Cucu-Grosjean et al. 2012 and Santinelli et al. 2014 (abstracts and slides only).
  - Reineke 2014, Reghenzani et al. 2019 and 2020, Reghenzani–Santinelli–Fornaciari 2020 (abstracts only).
  - Abella et al. 2015 (abstract only; its pitfall list is not reported).
  - Lima et al. 2016 (not read; survey summaries only).
  - Paolieri et al. 2009 (not read).
  - Davis & Cucu-Grosjean 2019 pp. 03:46–03:60.
  - The GR740 user manual beyond p. 67 (L2 replacement and bus arbitration chapters).
- **Not examined.**
  - `chronovise` MLE/GMLE estimators (need `ceres-solver`), the PoT and CV approaches, and the `apps/` tools.
  - Whether the BDS defect exists on other `chronovise` branches (`master-next`).
  - The harness's Bayesian-optimisation and simulated-annealing internals beyond the measurement statistic.
  - Commercial RapiDaemons.
- **Toy and synthetic scope.** The `chronovise` probes use synthetic distributions. They show what the tests can and cannot detect for those distributions and do not estimate any real task's pWCET.
- **Unsupported stronger conclusions.**
  - This report does not show that any published interference bound was exceeded in deployment.
  - It does not show that MBPTA is unsound for time-randomized platforms satisfying its premises.
  - It does not show that the BDS defect affected any published result.
  - The patched BDS rates (0.075–0.117) are closer to nominal but were not shown to equal 0.05; the residual excess is **unknown**.
- **Known not to apply.** The NGMP figures were measured on a 70 MHz FPGA prototype and are not GR740 silicon measurements.

## Evidence

Observation date: 2026-11-20 (UTC) for all source reads, builds, executions and DOI resolutions.

**Source.**

- `CSL-KU/IsolBench` @ `682680ebf7cdadaee7443ca9246dc424a05e60fa`: `bench/bandwidth.c` (187–205 kernels, 208–220 usage, 241–296 options), `bench/latency.c` (37–41 defaults, 106–145 options, 150–202 list construction and chase), `bench/pll.cpp` (47–50, 389–413, 438–520), `bench/Makefile`, `README.md`.
- `mc-imperial/multicore-test-harness` @ `38d7eddff9444cd114f4fb391f19f4bc4414bcb1`: `README.md` (framework steps, tuning methods, JSON parameters), `scripts/common.py` (43–160 defaults, 214–262 `MappingResult`, 316–333 `remove_outliers`), `scripts/run_sut_stress.py` (34–87 `confidence_variation`, 223–345 `run_mapping`), `scripts/run_tuning.py` (451–482 objective), `scripts/exp_configs/enemy_tune/tune_cache_large.json`, `scripts/exp_configs/sut_train/tune_sut_pi.json`.
- `federeghe/chronovise` @ `4b332f10669af73f33e00f8749040eed9601bfb2`: `CMakeLists.txt`, `README.md`, `docs/MBPTA.md`, `docs/FRAMEWORK.md`, `src/aec.cpp` (10, 125–276), `src/evt/evtapproach_bm.cpp`, `src/evt/pwcet.cpp`, `include/statistical/test.hpp`, `include/statistical/test_*.hpp`, `src/statistical/test_bds.cpp` (12, 19–47, 50–95, 113–145, 148–171, 174–210), `include/sec.hpp`, `samples/simple_hello_world.cpp`.
- `statsmodels/statsmodels` @ `32bd3137bd45e763d22802ecfa99be3f02ad03f2`: `statsmodels/tsa/_bds.py` 73–106, 228–256.

**Literature.** DOIs were resolved through the DOI handle API (`responseCode` 1) on 2026-11-20. Content was read as stated.

- P. Radojković, S. Girbal, A. Grasset, E. Quiñones, S. Yehia, F. J. Cazorla, *ACM TACO* 8(4), Art. 34, 2012, DOI `10.1145/2086696.2086713`. Author preprint read in full (table cells not extracted).
- M. Fernández, R. Gioiosa, E. Quiñones, L. Fossati, M. Zulianello, F. J. Cazorla, EMSOFT 2012, DOI `10.1145/2380356.2380389`. Author preprint read in full (figure values not extracted).
- S. H. VanderLeest, S. R. Thompson, DASC 2020, DOI `10.1109/DASC50938.2020.9256647`; arXiv:2101.02204 read.
- P. K. Valsan, H. Yun, F. Farshchi, RTAS 2016, DOI `10.1109/RTAS.2016.7461361`. Author camera-ready read.
- M. G. Bechtel, H. Yun, RTAS 2019, DOI `10.1109/RTAS.2019.00037`; arXiv:1903.01314 v1 HTML read.
- D. Iorga, T. Sorensen, J. Wickerson, A. F. Donaldson, RTAS 2020, DOI `10.1109/RTAS48715.2020.000-6`. Abstract (Semantic Scholar record), first author's blog post "Uncovering multicore interference" (17 Apr 2020) and the artifact README read; full text not read.
- J. Nowotsch, M. Paulitsch, EDCC 2012, DOI `10.1109/EDCC.2012.27`. Not read.
- D. Griffin, A. Burns, WCET 2010, OASIcs 15:44–53, DOI `10.4230/OASIcs.WCET.2010.44`. DROPS abstract and authors' slides read.
- L. Cucu-Grosjean et al., ECRTS 2012, DOI `10.1109/ECRTS.2012.31`. Abstract (Semantic Scholar record; co-author homepage) and ECRTS 2012 slides read.
- J. Reineke, *LITES* 1(1):03, 2014, DOI `10.4230/LITES-v001-i001-a003`. DROPS abstract read.
- J. Abella et al., SIES 2015, DOI `10.1109/SIES.2015.7185039`. Abstract read.
- F. Reghenzani, G. Massari, W. Fornaciari:
  - "chronovise", *JOSS* 3(28):711, 2018, DOI `10.21105/joss.00711` (read);
  - *IEEE ESL* 2019, DOI `10.1109/LES.2018.2889114` (abstract);
  - *Microprocessors and Microsystems* 77:103135, 2020, DOI `10.1016/j.micpro.2020.103135` (abstract);
  - the first author's PhD thesis (Politecnico di Milano, 2020), §3.2–3.3, read as a secondary source for the test list;
  - F. Reghenzani, L. Santinelli, W. Fornaciari, *ACM TECS* 2020, DOI `10.1145/3396234` (abstract).
- R. I. Davis, L. Cucu-Grosjean, *LITES* 6(1):03, 2019, DOI `10.4230/LITES-v006-i001-a003`. White Rose deposit read, pp. 03:1–03:45.
- F. J. Cazorla, L. Kosmidis, E. Mezzetti, C. Hernandez, J. Abella, T. Vardanega, *ACM CSUR* 52(1):14, 2019, DOI `10.1145/3301283`. Read in full.
- L. Santinelli, J. Morio, G. Dufour, D. Jacquemart, WCET 2014, DOI `10.4230/OASIcs.WCET.2014.21`. Abstract and slides read.
- G. Lima, D. Dias, E. Barros, ECRTS 2016, DOI `10.1109/ECRTS.2016.20`. Not read.
- J. Abella, M. Padilla, J. del Castillo, F. J. Cazorla, *ACM TODAES* 22(4), 2017, DOI `10.1145/3065924`. Author manuscript read.
- C. Maiza, H. Rihani, J. M. Rivas, J. Goossens, S. Altmeyer, R. I. Davis, *ACM CSUR* 52(3), 2019, DOI `10.1145/3323212`. Accepted manuscript read.
- G. Fernández, J. Abella, E. Quiñones, C. Rochange, T. Vardanega, F. J. Cazorla, WCET 2014, DOI `10.4230/OASIcs.WCET.2014.31`. Read.
- G. Fernández, J. Jalle, J. Abella, E. Quiñones, T. Vardanega, F. J. Cazorla, *IEEE TC* 66, 2017, DOI `10.1109/TC.2016.2616307`. Accepted manuscript read.
- R. I. Davis, S. Altmeyer, L. S. Indrusiak, C. Maiza, V. Nélis, J. Reineke, *Real-Time Systems* 54:607–661, 2018, DOI `10.1007/s11241-017-9285-4`. Open-access HTML read.
- H. Kim et al., RTAS 2014, DOI `10.1109/RTAS.2014.6925998`. Author copy read.
- H. Yun et al., *IEEE TC* 65, 2016, DOI `10.1109/TC.2015.2425889`. Author copy read.
- R. Pellizzoni et al., DATE 2010, DOI `10.1109/DATE.2010.5456952`. Proceedings copy read.
- M. Paolieri et al., ISCA 2009, DOI `10.1145/1555754.1555764`. Not read.
- T. Lundqvist, P. Stenström, RTSS 1999, DOI `10.1109/REAL.1999.818824`. Author preprint read.
- Certification Authorities Software Team, *CAST-32A Multi-core Processors*, November 2016 (FAA-hosted PDF read).
- EASA, *AMC 20-193 Use of multi-core processors*, Annex I to ED Decision 2022/001/R (read).
- FAA, *AC 20-193 Use of Multi-Core Processors*, 1/8/24 (read).
- Frontgrade Gaisler:
  - *GR740 Data Sheet and User's Manual* v2.8 (Dec 2024), pp. 1–67 read;
  - *GR740 Overview* presentation (11 Oct 2023);
  - *GR740 Technical Note on Benchmarking and Validation* GR740-VALT-0010 issue 3.4 (2019).

**Execution.** Host: x86-64 cloud VM, 2 sockets × 24 cores × 2 threads, `Intel(R) Xeon(R) CPU @ 2.60GHz`, Linux, GCC 15.2.0, Python 3.13.15, NumPy 2.3.5. Load average was 100–134 during runs, so wall times are upper-biased. Build and run sequence (`$CHRONOVISE` is a checkout of the pinned revision):

```text
for f in <the 23 non-ceres sources listed in CMakeLists.txt>; do
  g++ -std=c++14 -O2 -include cstdint -I$CHRONOVISE/include -DGIT_VERSION='"4b332f1"' -c $CHRONOVISE/$f; done
ar rcs libchronovise.a *.o
g++ -std=c++14 -O2 -include cstdint -I$CHRONOVISE/include support/mbpta_driver.cpp libchronovise.a -o mbpta_driver
python3 support/gen_samples.py gen
./mbpta_driver s_iid.txt 50 1e-9; ./mbpta_driver s_ar1.txt 50 1e-9; ./mbpta_driver s_campaign.txt 50 1e-9
python3 support/gen_samples.py exceed 1134.43
g++ -std=c++14 -O2 -include cstdint -I$CHRONOVISE/include support/bds_size.cpp libchronovise.a -o bds_size_upstream
# patched variants: apply support/bds_patch_coefficient_only.diff or support/bds_patch.diff to a copy of
# src/statistical/test_bds.cpp, compile it, replace src_statistical_test_bds object in a copy of
# libchronovise.a (ar d / ar rcs), and link bds_size_patched / bds_size_patched2
./bds_size_upstream unit
./bds_size_upstream 100 400 gamma; ./bds_size_upstream 100 400 normal; ./bds_size_upstream 100 400 normal1000
./bds_size_upstream 250 200 gamma; ./bds_size_upstream 250 200 normal; ./bds_size_upstream 500 60 gamma
(same for the patched binaries)
```

Outputs are preserved in `support/mbpta_driver.out`, `support/mbpta_driver_bds_small.out`, `support/exceed.out` and `support/bds_size.out`.

## Revalidation

- **BDS defects.**
  - Inspect `src/statistical/test_bds.cpp` for two things: whether `embedding_dimension_1` still uses `2./((size-m+1.)*(size - m))` with `s, t` looping over `1..size`, and whether `embedding_dimension` still starts at `s = 1` while `indicator_function` walks back `m−1` steps.
  - Then run `support/bds_size.cpp` against the library:
    - `./bds_size 100 400 normal` and `./bds_size 100 400 normal1000` (about 4 s each). Rates near 0.40 and 0.89 reproduce both defects; equal rates near 0.05–0.12 indicate both are fixed.
    - `./bds_size unit` re-evaluates the upstream unit-test sample.
- **Harness statistic.** Check `remove_outliers` and `log_result` in `scripts/common.py` and the default `quantile`. If outliers are no longer trimmed or the objective becomes a maximum, §2.3 changes.
- **`chronovise` flow.** Check `execute_analysis` and the `keep_going` handling in `src/aec.cpp` (no retry on rejection) and `pWCET::get_wcet` (per-block semantics).
- **Literature figures.** They do not change with time. Re-verify by locating the quoted sentences in the cited author preprints, using the section numbers given.
- **Hardware conclusions.** Validating any slowdown on a platform requires an isolated, frequency-pinned, thermally controlled machine and repeating the campaign. No cheap probe substitutes for this.
