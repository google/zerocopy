# CovidSim and Covasim reproducibility contracts, the CODECHECK Report 9 certificate, EpiEstim renewal windows, and forecast-hub weighted interval scoring

## Summary

- **CovidSim reproduces only per thread count.** At revision `b719de9df5909f8fc47753dd1d2baf89fc415943` a result is defined by the binary, the parameter and population files, the four integer seeds, and the effective OpenMP thread count. Each thread draws from its own L'Ecuyer–Côté stream, and every parallel loop uses a `static` schedule, so a fixed thread count gives byte-identical output. Changing the thread count produces a different realisation. The regression suite therefore keeps separate SHA-512 golden files for 1 and 2 threads. In the UK test all 50 files common to both golden sets differ. The suite applies no numerical tolerance.
  - **`/c:N` is only an upper bound.** The effective count is min(N, OpenMP's available threads, 96). With `OMP_NUM_THREADS=1`, a `/c:2` run reproduced the 1-thread goldens.
  - **Measured on this subject:** a GCC 15.2.0 build on x86-64 Linux reproduced the committed US-test goldens at 1 and 2 threads under `-O0`, `-O2`, `-O3` and `-O2 -ffp-contract=off`. It also reproduced the UK-test goldens at `-O2`.
  - **Measured break:** `-O2 -march=native -ffp-contract=fast` and `-O2 -ffast-math` both failed. With FMA at 1 thread, the only change was one cell at the 12th significant digit. With FMA at 2 threads, and with fast-math at both thread counts, the result was a different epidemic realisation, roughly as different as a change of thread count.
- **The CODECHECK certificate 2020-010 confirms two different reproduction relations, so cite them separately.**
  - *Rerun identity:* independent reruns of the public code (revision `b125307e13d0a5226bff78b472b61a51516064e7`, 8 threads, NR=10, fixed seeds) produced summary statistics identical to the authors' own reruns.
  - *Approximate agreement with the published report:* the reruns differed from the original Report 9 tables by mostly under 5%, with three larger differences (one of 25%, two of 10%). The original tables came from private code, a different population dataset and single realisations.
  - The certificate states explicitly that it does not check whether the computation is correct.
- **Covasim 4.0.2 (rebuilt on Starsim) uses a two-tier criterion.**
  - *Exact baseline:* the end-of-run summary of one seeded scenario must match a stored baseline under `np.isclose(atol=1e-9, rtol=0)`.
  - *Statistical parity with v3.1.8:* the cross-version gate uses multi-seed z-scores, with |z|<3 by default and |z|<5 for natural history. It does not require bit identity, because the random-number architecture changed between versions.
  - Arithmetic is 32-bit by default.
- **EpiEstim's estimator matches its closed form.**
  - *Formula:* with prior Gamma(shape (5/5)², scale 5²/5) and total infectivity Λ_t = Σ_s w_s I_{t−s}, the posterior for R over the window [t−τ+1, t] is Gamma(a_prior + Σ local cases, 1/(1/b_prior + Σ Λ)). The estimate is reported at the window end, and only when the window end exceeds the serial-interval mean.
  - *Differential check:* a standard-library Python transcription reproduces the package's own snapshot output to 4.6×10⁻⁸ (the precision at which the snapshot is printed).
  - *Bias directions:* the following agree with Gostic et al. and reappear in a toy renewal model.
    - An assumed generation-interval mean that is too short pulls estimates toward 1; one that is too long pushes them away from 1.
    - End-of-window reporting delays detection of a step change. In the toy, after a drop from R=2.0 to 0.8, the first estimate below 1 came 5, 11 and 16 days late for 7-, 14- and 21-day windows. The window estimate is the ratio Σ I / Σ Λ, so it is weighted toward the larger pre-drop values, and the lag exceeds the half-window midpoint offset.
    - Using report-date counts shifts the curve by roughly the reporting delay.
    - Right truncation biases the most recent estimates strongly downward.
  - *Corrections in EpiEstim 3.0.0:* serial-interval uncertainty resampling, serial-interval estimation from pair data, back-imputation of early unobserved generations, and coarsely aggregated input. It implements no delay deconvolution and no right-truncation nowcast.
- **Forecast-hub scoring and ensembling conventions determine rankings.**
  - *Score:* scoringutils' default weighted interval score uses the Bracher et al. normaliser 1/(K+½). It equals the mean of the per-quantile scores, which are twice the pinball loss (identity checked to 1.4×10⁻¹⁴). It is proper for quantile forecasts but cannot distinguish predictive laws that agree at the scored levels.
  - *Ensemble:* since 2020-07-28 the hub ensemble has been a per-quantile median of eligible models. A model missing any required quantile or target at a location is dropped for that location.
  - *Published comparisons:* these use pairwise mean-score ratios on overlapping forecasts and geometric means. Plain mean WIS over each model's own submissions can be improved by omitting hard targets.
  - *Quantile set:* changing the quantile set (23 versus 7 levels) can reverse a pairwise ranking. This is shown in a constructed example.

## Applicability

**Subjects and relationships.**

| Subject | Revision examined | Relationship |
|---|---|---|
| CovidSim | `mrc-ide/covid-sim@b719de9df5909f8fc47753dd1d2baf89fc415943` (repository HEAD, last commit 2023-02-21) | Primary source and execution subject. All execution results are for this revision. |
| CovidSim, CODECHECK-era | `mrc-ide/covid-sim@b125307e13d0a5226bff78b472b61a51516064e7` (2020-05-27) | Revision named by the certificate. Only its test layout and CMake flags were inspected; it was not built. |
| CODECHECK reproduction | `codecheckers/covid-report9@7e3d7b0559659699ea90be612ad0479db62fb1fa` + certificate DOI `10.5281/zenodo.3865491` | Defines what the certificate reproduced and how. |
| Covasim | `InstituteforDiseaseModeling/covasim@9454c841cda45d431d7c0eb9ec1edfa28240b11a` (version 4.0.2, 2026-11-01) | Source only. Not executed. Kerr et al. 2021 describe the pre-Starsim code line, so implementation statements in that paper do not automatically carry over. |
| EpiEstim | `mrc-ide/EpiEstim@402982637562690073884b58100c80d98b6a8538` (version 3.0.0) | Source and snapshot. The R package was not executed (no R runtime on the observing host); a Python transcription was checked against its snapshot. |
| Forecast Hub | `reichlab/covid19-forecast-hub@3a6997b6abdcfabe321dd059ebe32334095d49b5` | Hub conventions, model metadata and ensemble eligibility/weight CSVs. The hub stopped accepting submissions on 2024-05-01. |
| covidEnsembles | `reichlab/covidEnsembles@9b46312a6fd3635ac4e7e9c03ac29ccb0ad69b5f` | Code that built the hub ensembles (combination method, eligibility). |
| scoringutils | `epiforecasts/scoringutils@779d7d68fa34d80146fdfd4b46f5919c5d61d982` (2.3.0.9000) | Reference WIS implementation. |

**Scope limits.**
- The execution results come from one host class: an x86-64 Linux workstation (Intel Xeon @ 2.60 GHz with FMA, 96 logical CPUs) running Debian GCC 15.2.0, libgomp, and Python 3.13.15.
- The build used direct `g++` invocation with the source list from `src/CMakeLists.txt`, because CMake was not installed on the host. This reproduces the UNIX branch of the CMake flags, which adds no floating-point option for GCC, but not CMake's `RelWithDebInfo` defaults verbatim. The base build used `-O2 -g`.
- Statements about other compilers, operating systems and ISAs come from upstream documentation, unless the text labels them as derived.
- The EpiEstim and WIS probes are labelled per finding. The EpiEstim snapshot comparison checks the transcription against upstream output. All other probe results are toy-model results. They illustrate the formulas and are not properties of any real outbreak, hub submission or model.

## Findings

### 1. CovidSim: stochastic architecture and what "reproducible" means

**Seeds.**
Basis: source.
The command line ends with four integers `SetupSeed1 SetupSeed2 RunSeed1 RunSeed2` (`src/CLI.cpp:164-174`).

| Stage | Code | Effect |
|---|---|---|
| Allocate per-thread generator state | `src/SetupModel.cpp:39-40`: `Xcg1 = (int32_t*)Memory::xcalloc(MAX_NUM_THREADS * CACHE_LINE_SIZE, sizeof(int32_t));` | Each thread's state occupies its own padded slot. `MAX_NUM_THREADS = 96` and `CACHE_LINE_SIZE = 64` (`src/Constants.h:88-89`). |
| Seed setup streams | `src/SetupModel.cpp:41-43` `setall(&P.nextSetupSeed1, &P.nextSetupSeed2)` | Population and household–place network generation. |
| Reseed after network | `src/SetupModel.cpp:294-297`. The source comments that it wants "the same random numbers regardless of whether we used the RNG to make the network, or loaded the network from a file. Therefore we need to reseed the RNG." | Makes "build network" and "load saved network" runs share all later random draws. |
| Seed run streams | `src/CovidSim.cpp:341-345, 354-370` | Realisation 0 of the first fit iteration starts from `RunSeed1/2`. Later realisations continue the advanced state, unless `ResetSeeds && KeepSameSeeds` is set. Calibration loops restore `thisRunSeed1/2` to "generate same run again after calibration". |
| Optional mid-run reseed | `src/CovidSim.cpp:1431-1435` (`ResetSeedsPostIntervention`, `TimeToResetSeeds`) | Supports common-random-number comparison of interventions after a given day. |

**Generator.**
Basis: source.
`ranf_mt(int tn)` (`src/Rand.cpp:28-47`) is the L'Ecuyer–Côté combined multiplicative congruential generator (moduli `Xm1`, `Xm2`; Schrage decomposition with constants 53668/12211 and 52774/3791). It reads and writes `Xcg1[CACHE_LINE_SIZE * tn]`. `setall` (`src/Rand.cpp:49-81`) is the "Set_Initial_Seed" routine of L'Ecuyer and Côté (ACM TOMS 17:98-111, 1991, DOI `10.1145/103147.103158`). It seeds all 96 thread streams by repeatedly jumping the seed with `mltmod(Xa1vw, iseed1, Xm1)`. A thread's stream is therefore fixed by its thread index, not by the agent or place it is processing.

**Threading.**
Basis: source.
- The source contains 75 `#pragma omp` directives (12 in `CovidSim.cpp`, 16 in `SetupModel.cpp`, 21 in `Sweep.cpp`, 26 in `Update.cpp`). 39 of them open parallel regions: 38 are `parallel for` loops, every one with a static schedule, and 1 is a thread-initialisation print (`CovidSim.cpp:255`). The 38 schedule clauses are `schedule(static,1)` ×26 and `static` ×1, with chunk sizes 500 ×6, 1000 ×2 and 10000 ×3. Many loops iterate `for (int Thread = 0; Thread < P.NumThreads; Thread++)`. Under a static schedule the mapping from work to thread, and hence to random stream, is a deterministic function of the thread count.
- **`/c:` is a cap, not a setting.** `src/CovidSim.cpp:245-253` sets `P.NumThreads = omp_get_max_threads()`. Then `if ((P.MaxNumThreads > 0) && (P.MaxNumThreads < P.NumThreads)) P.NumThreads = P.MaxNumThreads;`. Finally it clamps to `MAX_NUM_THREADS`. `/c:` populates `P.MaxNumThreads` (`:176`). The effective thread count, and with it the realisation, is therefore min(`/c`, OpenMP's available threads, 96). It depends on the host CPU count and on `OMP_NUM_THREADS`. The only record is the stderr line `Using %d threads`. An execution check of this behaviour is in the next table.
- Shared updates use `#pragma omp critical` (for example `Sweep.cpp:124-266`, `Update.cpp:216 (inf_event)`) and `#pragma omp atomic` (for example `Update.cpp:93, 177, 940-1087`).
- Floating-point OpenMP reductions exist, for example `double HH_SAR_Denom` and `double HH_Infections` reduced at `src/SetupModel.cpp:646-666`, and `double recovery_time_days` at `:818-820`. OpenMP leaves the combination order of reduction partials to the implementation.
- Whether these doubles feed any checked output was not traced; see Boundaries.

**Consequence.**
Basis: source + documentation.
The README states: "The model code behaves deterministically if run with the same number of threads enabled and run with the same random number seeds" (`README.md:25-26`). `report9/README.md:6` extends this: "Covidsim is now deterministic across platforms (linux, Mac and Windows) and across compilers (gcc, clang, intel and msvc) for a specified number of threads and fixed random number seeds". `report9/README.md:49-52` adds two conditions:
- results match the published spreadsheets only with `/NR:10`, 8 threads and the current seeds;
- changing `/c:` requires regenerating the network file.

**Regression-test contract.**
Basis: source.
`tests/CMakeLists.txt:6-35` registers each integration test twice (`foreach(j RANGE 1 2)`), passing `-j ${j}` and `--checksums .../results-j${j}.cksum`. The UK test uses `wpop_eur.txt.gz` and R=1.1; the US test uses `wpop_usacan.txt.gz` and R=1.5 (`:37-38`). `tests/integration-test.py` runs three simulations per test, all with seeds `98798150 729101 17389101 4797132`:
1. no intervention, building and saving the network (`/S:`);
2. no intervention, loading that network (`/L:`);
3. intervention, loading the network.

It then:
- requires run 1 and run 2 `.xls` outputs to be byte-identical, with at least 3 files over 10 bytes (`:307-323`);
- hashes every `.xls` and every 100th bitmap frame with SHA-512 (`:333-353`);
- compares the sorted list with the golden file (`:375-399`).

The script's explanation (`:60-73`) says the test has no tolerance, so a change such as `0.0308373797` to `0.0308373798` fails it, and that "Floating point computations are deterministic, so only a change to the code can cause the test to fail". The script still names an older golden file, `regressiontest_UK_100th.checksums.txt` (`:78`), although the CMake wiring passes `results-j{1,2}.cksum`. At the CODECHECK-era revision `b125307e13d0a5226bff78b472b61a51516064e7`, the test instead ran 1 and 2 threads inside one invocation, with prefixes `st-` and `mt-`, against a single `results.checksums.txt` per input.

**Golden-file comparison.**
Basis: source. The committed golden files were compared with a short script; the simulator was not run.

| Golden set | Files | Common to j1 and j2 | Identical hashes |
|---|---|---|---|
| `tests/uk-input/results-j1.cksum` vs `results-j2.cksum` | 60 vs 50 | 50 | **0**. Every common file differs, including the step-0 bitmap `results-int.00000.bmp`. j1 also has 10 more bitmap frames (simulation ran to frame 1600 vs 1200). |

**Execution of the real subject.**
Basis: execution. Host: x86-64 Linux workstation, GCC 15.2.0, libgomp. Command: `integration-test.py --input tests/us-input --checksums tests/us-input/results-j$j.cksum --covidsim <binary> --popfile data/populations/wpop_usacan.txt.gz --r 1.5 -j $j`.

| Build flags (all `-std=c++14 -fopenmp -DUNIX`) | US j1 | US j2 | Notes |
|---|---|---|---|
| `-O2 -g` | pass | pass | 57.11 s and 50.40 s wall per test (3 runs each); peak RSS 3,245,216 kB and 3,244,680 kB (`/usr/bin/time -v`). |
| `-O2 -ffp-contract=off` | pass | pass | |
| `-O3` | pass | pass | |
| `-O2 -march=native -ffp-contract=fast` | **fail** | **fail** | In every failing case, run 1 and run 2 were still mutually identical. **j1:** 2 of 12 hashed files changed (`results-noint{,-repeat}.avNE.severity.age.xls`). Across the 722-row table exactly one cell differed: column `CriticalP_9`, row 68, `17.7831255931` vs `17.7831255930` (relative 5.6×10⁻¹²). All cumulative counts were identical. **j2:** 8 of 12 files changed, and the no-intervention realisation diverged (final `cumDeath` 5995 vs 6014, `cumCritical` 4009 vs 4043). The intervention run was unchanged. |
| `-O2 -ffast-math` | **fail** | **fail** | 12 of 12 files changed at both thread counts. Every realisation diverged: j1 no-intervention `cumDeath` 5972 vs 5969, intervention 133 vs 140; j2 6016 vs 6014 and 163 vs 152. |
| `-O0` | pass | pass | |
| `-O2 -g`, **UK** test (`tests/uk-input`, `wpop_eur.txt.gz`, `--r 1.1`; 3,100,000-person population) | pass | pass | 16:35.76 (j1) and 5:51.63 (j2) wall. The j1 run overlapped other jobs on the same host, so its time is contended. Peak RSS 3,522,936 kB and 3,519,396 kB. |
| `-O2 -g`, environment `OMP_NUM_THREADS=1`, test invoked with `-j 2` (so `/c:2`), checked against `results-j1.cksum` | n/a | **passes the 1-thread goldens** | All three runs printed `Using 1 threads`. A 2-thread request silently produced the 1-thread realisation, confirming the `/c:` cap above. |

For scale, the default build's own j1 vs j2 difference is: no-intervention `cumDeath` 5969 vs 6014, intervention 140 vs 152.

**Interpretation.**
Basis: derived from the table above.
- A one-ulp-scale change in a single floating-point expression can stay cosmetic or can produce a different stochastic realisation, depending on the run. In the FMA build at 1 thread it stayed cosmetic: one printed digit changed. At 2 threads the same build gave a whole new no-intervention trajectory.
- The likely mechanism is a probability that is compared against a uniform draw. Once a draw lands on the other side of the threshold, every later draw is consumed by different events. This mechanism is inferred and was not traced in the source.
- The divergence is of the same order as the change caused by switching the thread count. A run can therefore be "reproduced" only as an exact (binary semantics, thread count, seeds, inputs) tuple. A tolerance-based golden comparison would not rescue it.
- Fused multiply–add rounds once where separate operations round twice. GCC contracts by default in its GNU dialects whenever the target ISA has FMA, which includes AArch64 and `-march=native` on modern x86-64. `-ffast-math` additionally permits reassociation.
- The upstream "deterministic across compilers" claim therefore holds only for builds that neither contract nor reassociate. Baseline x86-64 builds without FMA meet that condition.

Regarding the documented compiler set, the 2020 claim covered gcc, clang, intel and msvc. This host adds GCC 15.2.0 at `-O2`/`-O3` as a passing case.

**Build-flag handling.**
Basis: source + derived.
`src/CMakeLists.txt:24-32` gives each platform a different floating-point flag:
- Intel compilers on UNIX get `target_compile_options(CovidSim PUBLIC "SHELL:-fp-model precise")`;
- GCC and Clang get nothing;
- WIN32 executes `add_compile_options("fp:strict")`.

That last command runs after `add_executable(CovidSim ...)` at line 14. CMake's `add_compile_options` populates the directory property `COMPILE_OPTIONS`, which initialises only targets created afterwards in that directory. In addition, the string lacks MSVC's `/` prefix. The command therefore appears to have no effect on the `CovidSim` target. The same line is present at the CODECHECK-era revision (`src/CMakeLists.txt:17`).

This is a static-reading conclusion; no Windows build was performed.

### 2. CODECHECK certificate 2020-010: what was certified

Basis: documentation (certificate source `codecheck/codecheck.Rmd` and `codecheck.yml` at `codecheckers/covid-report9@7e3d7b0559659699ea90be612ad0479db62fb1fa`; Zenodo record).

| Aspect | Certificate content |
|---|---|
| Paper | Ferguson et al., Report 9, 16 March 2020 (DOI `10.25561/77482`). Manifest: Tables 3, 4, 5, A1 (`codecheck.yml`). |
| Code | Public `mrc-ide/covid-sim` master at commit `b125307e13d0a5226bff78b472b61a51516064e7` (2020-05-27). The certificate says this "version is deterministic across all platforms" (`codecheck.Rmd:113-117`). |
| Inputs | Parameter files and R scripts from the original authors, later published in `report9/` (`codecheck.Rmd:120-125`). Network built once with 8 threads (`GB_suppress_release/runonce.sh`: `CovidSim /c:8 ... /S:NetworkGB_8T.bin /R:${rs} 98798150 729101 17389101 4797132`). |
| Compute | "About 3 days on a 64-core workstation, and about 1 day on a departmental HPC cluster" for the batch job lists (`codecheck.Rmd:161-162`). The summary quotes "about 24 hours on a departmental HPC server" (`:77-79`). |
| Criterion A: rerun identity | The summary CSVs "were compared against the values generated by Prof Ferguson … The results were found to be identical". Inserting them into the authors' spreadsheet "generated the same pivot tables" (`codecheck.Rmd:182-188`). |
| Criterion B: agreement with the published report | "Small variations (mostly under 5%)". There were three significant differences: Table A1 peak beds 40 vs 30 thousand (25%); Table 5 total deaths 39,000 vs 43,000 (10%); and 100,000 vs 110,000 (10%) (`:82-93`). These are attributed to determinism changes, different population input files, and averaging NR=10 runs instead of one simulation (`:96-102`). |
| Scope disclaimer | "A CODECHECK does not check whether the original computation analysis is correct" (`:213-216`). |

**Two separate claims.**
Basis: derived.
The certificate establishes rerun identity, which is a property of a frozen tuple (code, inputs, threads, seeds, NR). For the published numbers it establishes only qualitative trend agreement ("the overall trends are consistent", `:104-105`). It says nothing about whether the model is correct.

Edeling et al. (Nature Computational Science 1:128-135, 2021, DOI `10.1038/s43588-021-00028-9`) addressed a third, distinct question: parametric uncertainty. Their abstract reports that 19 of 940 inputs dominate output sensitivity, that input uncertainty is "magnified in the outputs by up to 300%", and that the model "displays substantial bias with respect to observed data".

### 3. Covasim 4.0.2: exact baseline plus statistical parity

Basis: source.
- **Architecture.** `covasim/sim.py` defines `cv.Sim(ss.Sim)`, a thin wrapper over Starsim, and `covasim/version.py` records `__version__ = '4.0.2'`. The changelog says that 4.0.0 (2026-10-04) changed Covasim "from a standalone library to one built on the Starsim framework".
- **Seeding for multiple runs.** `covasim/run.py:951-953` (`single_run`): `sim['rand_seed'] += ind # Reset the seed, otherwise no point of parallel runs`, then `sim.set_seed()`. `multi_run` dispatches with `sc.parallelize(...)`, using processes (`run.py:1058`).
  - Derived: the seed is set by run index, so results do not depend on worker count or scheduling. This was not executed.
- **Exact self-consistency gate.** `tests/test_baselines.py:11-14` says: "v4 is deterministic for a fixed seed (per-distribution CRN), so the default sim reproduces its saved summary exactly. (v4 is NOT bit-for-bit identical to v3; …)".
  - The scenario is `pop_size=20e3`, `pop_type='hybrid'`, `n_days=60`, `rand_seed=2`, `use_waning=True`, with interventions `test_prob`, `vaccinate_prob('pfizer')`, `change_beta`, `contact_tracing` (`:31-47`).
  - `test_baseline` compares `sim.summary` with `cv.diff_sims(old, new, die=True)` (`:87-101`). `diff_sims` defaults to `atol=1e-9, rtol=0` and uses `np.isclose` per key (`covasim/misc.py:149`, value loop `:203-212`). This is effectively exact on count-valued summary keys. Only end-of-run summary keys are compared, not the daily time series.
- **Cross-version parity gate.** `tests/migrate3to4/parity.py:3-8` computes `z = (v4_mean - v3_mean) / sqrt(v3_SE^2 + v4_SE^2)` over per-seed summaries (standard error = std with ddof=1 / √n). The default threshold is |z|≥3 (`:31`).
  - `tests/migrate3to4/README.md` documents per-feature gates:
    - natural history uses |z|<5, an explicit decision because the metrics agree within about 3% but the 40-seed standard error is small;
    - variant metrics that diverge are "INFORMATIONAL, not gated", for example roughly 7–10× more delta infections in v4 under static cross-immunity;
    - testing and vaccination metrics match within |z|<2 to 2.1.
  - The README states the RNG difference directly: v3.1.8 used "global numba RNG" and v4 uses "Starsim CRN".
- **Precision.** `covasim/settings.py:218-219` says: "Set arithmetic precision (shared with Starsim) -- 32-bit by default for efficiency", overridable through `COVASIM_PRECISION`. The baseline therefore pins 32-bit results. A 64-bit run is a different reproducibility class whose divergence from the baseline was not measured.

**Contrast with CovidSim.**
Basis: derived.

| Property | CovidSim | Covasim 4.0.2 |
|---|---|---|
| Stochastic unit | Per-thread stream inside one process | Per-distribution common random numbers inside one process; one seed per run |
| Parallelism that affects results | Thread count (OpenMP, inside one simulation) | None documented inside a simulation. Process-level parallelism across runs is seed-indexed. |
| Golden artefact | SHA-512 of full output files and frames, one set per thread count | End-of-run summary dict; tolerance `atol=1e-9` |
| Cross-version criterion | Regenerate goldens with `--accept` after manual inspection | Multi-seed z-score parity against frozen v3.1.8 runs |
| Default arithmetic | `double` (C++) | 32-bit |

### 4. EpiEstim: renewal-equation estimator, re-derived

**Model.**
Basis: normative (Cori et al. 2013) + source.
- Incidence follows I_t ~ Poisson(R_t Λ_t), with Λ_t = Σ_{s≥1} w_s I_{t−s}. In the source this is `overall_infectivity`, `R/overall_infectivity.R:52-63`: `lambda[t] <- sum(si_distr[seq_len(t)] * rowSums(incid[seq(t, 1), c("local","imported")]))`. Here `si_distr[1]` is P(SI=0) and must be 0 (`R/utilities.R:225-226`).
- R is assumed constant on a window [t_start, t_end] and given a Gamma(a, scale b) prior with a = (μ_p/σ_p)² and b = σ_p²/μ_p (`R/estimate_R.R:601-602`). The posterior is

  a_post = a + Σ_{t∈window} I_t^local,  b_post = 1 / (1/b + Σ_{t∈window} Λ_t)

  (`R/estimate_R.R:519-541`, `posterior_from_si_distr`). Only local cases enter the numerator, while both local and imported cases generate infectivity.
- The posterior mean is a_post·b_post and the posterior SD is √a_post·b_post (`:772-773`). Quantiles come from `qgamma`.
- An estimate is produced only if `t_end[t] > final_mean_si` (`:527-539`).
- A warning fires if the first window has fewer than `ceiling(1/cv_posterior^2 - a_prior)` cases (`:612-621`).

**Defaults.**
Basis: source (`R/make_config.R`).

| Parameter | Default | Line |
|---|---|---|
| `mean_prior`, `std_prior` | 5, 5 (so a_prior = 1, b_prior = 5) | `:294-295` |
| `cv_posterior` | 0.3 | `:296` |
| `t_start`, `t_end` | `seq(2, T-6)`, `seq(8, T)`: weekly sliding windows | `:312-313` |
| `n1`, `n2` (uncertain-SI resampling) | 500, 50 | `:280-281` |

**Serial-interval discretisation.**
Basis: source + execution.
`discr_si(k, mu, sigma)` (`R/discr_si.R:52-76`) models SI−1 as Gamma with shape ((μ−1)/σ)² and scale σ²/(μ−1). It integrates against a triangular kernel and truncates negative values at 0. The discretised SD exceeds the continuous σ. The package snapshot for μ=2.6, σ=1.5 reports `SI.Moments` mean 2.6 and SD 1.55488, and the Python transcription reproduces 2.600000 / 1.554880. In the parametric branch the pmf is computed on 0..T−1 and zero-padded to length T+1 (`R/estimate_R.R:756-761`).

**Differential check of the transcription.**
Basis: execution, comparing upstream snapshot output with an independent transcription.
`support/probe_renewal.py` Part A feeds the incidence vector printed in `tests/testthat/_snaps/estimate_R.md`, "Example 3" (Flu2009, `parametric_si`, mean 2.6, SD 1.5, windows 2–26 to 8–32; first case imported). Across all 25 windows the maximum deviation is 4.55×10⁻⁸ in posterior mean and 4.68×10⁻⁹ in posterior SD, which is the precision at which the snapshot is printed. The formulas above are therefore what the package computes for this path. Runtime is 0.10 s wall for the whole probe.

**Bias catalogue.**
Basis: Gostic et al. 2020 (documentation for the direction), plus execution (toy model, deterministic renewal epidemic, not EpiEstim's R runtime and not real data) for the illustrative magnitudes. In the toy, the true GI is a discretised gamma with mean 6.5 and SD 4.0, and R is 2.0 until day 40, 0.8 until day 90, and 1.15 afterwards. The window is 7 days and estimates are attributed to the window end.

| Error source | Effect (Gostic et al.) | Toy magnitude | Correction available in EpiEstim 3.0.0 |
|---|---|---|---|
| GI mean too short (4.5 vs 6.5) | Estimates "closer to 1 than the true value" | R=2.0 → 1.584; R=0.8 → 0.857; R=1.15 → 1.103 | `uncertain_si`/`si_from_sample` resample SI parameters. Gostic et al.: uncertainty "around an incorrect value can widen the resulting 95% interval but will not shift the assumed central value toward the truth". |
| GI mean too long (8.5) | "Further from 1": too high when R>1, too low when R<1 | 2.0 → 2.540; 0.8 → 0.751; 1.15 → 1.204 | Same as above |
| Correct GI | none | 2.002 / 0.802 / 1.152 | n/a |
| Window length τ, end-of-window reporting | "Rt estimates reported at the end of a window are based entirely on data from the past and therefore lag"; Gostic et al. recommend the midpoint | First t_end with R̂<1 after the drop at day 41: τ=1 → day 41; 7 → 46; 14 → 52; 21 → 57 | None. The user chooses `t_start`/`t_end` and can re-index estimates to the window midpoint. |
| Reporting delay used as if infection date | "Observations at time t inform R_{t−d}" | Report-date counts (delay mean 8 d): first R̂<1 at t_end 55 vs 46 | None in `estimate_R`. Gostic et al. recommend deconvolution, done externally. |
| Right truncation (recent infections not yet reported) | Recent infections "appear artificially low" | Analysis day 60: last-window R̂ 0.187 vs 0.801 untruncated (true 0.8). Day 100: 0.268 vs 1.153 (true 1.15) | None. Requires a nowcast before estimation. |
| Early missing generations | Early-epidemic bias | not measured | `backimputation_window` (EpiEstim 2.5; log-linear fit on `log(local + 0.5)`, `R/backimputation.R:1-8`) |
| Non-daily data | n/a | not measured | `dt >= 2` routes to `estimate_R_agg` (`R/estimate_R.R:383-404`); back-imputation is then unsupported (`:385-386`) |
| SI estimated from pairs during outbreak | Right censoring | not measured | `si_from_data` emits a warning that the method "does not correct for right censoring" (`:443-450`) |

Gostic et al. also note that the EpiEstim functions "quantify uncertainty arising from the Rt estimation model but currently not from uncertainty arising from imperfect observation or delays". They also note that Wallinga–Teunis estimates (the case reproductive number) lead Cori estimates by roughly one mean generation interval.

### 5. Forecast hub: collection, ensemble construction and interval scoring

**Submission format.**
Basis: documentation (`data-processed/README.md` at the pinned hub revision).
- Teams supplied 23 quantiles `c(0.01, 0.025, seq(0.05, 0.95, by = 0.05), 0.975, 0.99)` (`:303-305`), or 7 quantiles `c(0.025, 0.100, 0.250, 0.500, 0.750, 0.900, 0.975)` for the weekly incident-case target (`:311-313`).
- Point forecasts are optional. "When point forecasts are not included, the median for every location-target pair will be used" (`:290-291`).
- Evaluation and ensembling stopped on 2023-02-20 for cases, 2023-03-06 for deaths, and 2024-05-01 for hospitalisations (`:14-18`).

**Ensemble construction.**
Basis: documentation + source.
- `data-processed/COVIDhub-ensemble/metadata-COVIDhub-ensemble.txt` records equal-weight combinations of eligible models through May 2020. It then records: "July 28: switched to using a per-quantile median prediction across all eligible models", keeping automated checks for cumulative deaths that the 1-week 10th percentile is at least the latest observed value and that quantiles are non-decreasing over time.
- The covidEnsembles weekly driver (`code/application/weekly-ensemble/build_ensembles.R:136-170`) calls `build_covid_ensemble(..., combine_method = 'median', quantile_groups = rep(1, 23), missingness = 'by_location_group', required_quantiles = required_quantiles, do_baseline_check = FALSE, do_sd_check = do_sd_check # implement CDC exclusion requests)`. It drops locations where at most one model contributed (`:175-181`).
- **Missingness rule:** `calc_forecast_missingness` (`R/model_eligibility.R:263-350`) marks a model `"missing required forecasts"` for a location if `any(is.na(...))` over that location's required targets × quantiles. The last eligibility file (`ensemble-metadata/2024-04-29-inc_hosp-model-eligibility.csv`) lists 684 eligible and 31 ineligible location–model pairs, all 31 for missing required forecasts. The matching weights file contains 0/1 indicators per location, so the median is taken over eligible members only.
- The hub also archived `trained_ensemble-metadata/` and `4_week_ensemble-metadata/` weight files for the alternatives evaluated by Ray et al. (Int. J. Forecasting 39:1366-1383, 2023, DOI `10.1016/j.ijforecast.2022.06.005`). This report does not analyse them.

**Scores.**
Basis: normative (Bracher et al. 2021; Gneiting & Raftery 2007) + source (scoringutils).
- Interval score: IS_α(F,y) = (u−l) + (2/α)(l−y)·1{y<l} + (2/α)(y−u)·1{y>u}.
- Weighted interval score: WIS = (1/(K+½))·(½|y−m| + Σ_k (α_k/2)·IS_{α_k}).
- scoringutils `interval_score` (`R/metrics-interval-range.R:154-200`) computes the three components without the 2/α factor when `weigh = TRUE`. In that mode the penalties are `(lower - observed) * (observed < lower)` and `(observed - upper) * (observed > upper)`, and dispersion is multiplied by `alpha / 2`. The code comment reads "the weight alpha / 2 cancels analytically with the 2 / alpha factor". With `weigh = FALSE`, an observation outside a 100% interval yields `Inf`.
- `wis()` (`R/metrics-quantile.R:176-262`) aborts unless the levels form symmetric pairs, or drops incomplete pairs when `na.rm = TRUE` (`:186-205`). It then takes `weighted.mean` over the intervals, with weight 0.5 on the median row (`:233`: `reformatted[, weight := ifelse(interval_range == 0, 0.5, 1)]`). This reproduces the 1/(K+½) normaliser.
- `count_median_twice = TRUE` uses weight 1 instead, giving normaliser K+1.
- `quantile_score()` (`:683-725`) is `2 * (1{y ≤ q} − τ) * (q − y)`, averaged over levels.
- On the hub's 23 levels, K = 11 intervals with α ∈ {0.02, 0.05, 0.1, …, 0.9} (Bracher et al.).

**Probe results.**
Basis: execution (toy model, `support/probe_wis.py`; a Python transcription of the formulas above, not the R package).

| Check | Result |
|---|---|
| F1: WIS equals the mean of quantile scores (23 levels, 2000 random normal forecasts and outcomes) | max \|difference\| 1.42×10⁻¹⁴ |
| F2: normaliser variants for one forecast | default 1.603159; `count_median_twice` 1.661360. The two variants rescale scores and are not interchangeable across reports. |
| F3: propriety for quantile forecasts (truth Normal(50,10); expected WIS by trapezoidal integration) | true quantiles 5.0336; shift ±2: 5.1342; SD ×0.8: 5.1019; SD ×1.25: 5.1132 |
| F4: missing forecasts (40 synthetic weeks, every 5th week has 10× larger counts) | Model A forecasts all 40 weeks, mean WIS 62.55. Model B skips the 8 high-count weeks and is biased +10%, mean WIS 7.38. On the 32 overlapping weeks the mean-score ratio B/A is 1.353, so B is worse. |
| F5: quantile-set convention (constructed example) | C is exact except that its 0.01/0.99 quantiles collapse onto 0.05/0.95. D has SD ×1.05. Expected WIS on 23 levels: C 5.0522, D 5.0372 (D better). On 7 levels: C 4.2925, D 4.2971 (C better). |

**Propriety boundaries.**
Basis: normative + derived.
- Gneiting and Raftery define a score as proper if the true distribution minimises expected score. The quantile (pinball) score is proper for its quantile, and any nonnegative weighted sum of quantile scores is proper for the vector of those quantiles. Bracher et al. state that WIS "is proper for any set of nonnegative (unnormalized) weights".
- **WIS is not strictly proper relative to full predictive distributions.** It depends on F only through the 2K+1 reported quantiles, so any two laws that agree at those levels score identically for every outcome. Basis: derived directly from the definition.
- Bracher et al. note that the FluSight practice of truncating the log score at −10 makes it improper, and that the multibin log score is improper.
- Averaging proper scores over targets preserves propriety (Bracher et al., §2). It does not neutralise scale: WIS is in the units of the data, so averages across locations are dominated by high-count locations. Bosse et al. (PLoS Comput Biol 19:e1011393, 2023, DOI `10.1371/journal.pcbi.1011393`) propose scoring on transformed, for example log, scales.

**How published rankings were computed.**
Basis: documentation.
- Cramer et al. (PNAS 2022) admitted a weekly submission only if it was the team's designated primary model, covered at least 25 of 51 focal locations, covered all 1–4-week-ahead incident-death targets, and "contained a complete set of quantiles". A model was evaluated only with eligible submissions in at least 47 of 79 weeks (60%). 28 models qualified.
- Their relative WIS adjusts for differing forecast sets by combining pairwise comparisons. On that measure the ensemble scored 0.61, about 39% less probabilistic error than the baseline.
- scoringutils implements the same idea. Mean-score ratios are computed only on "the overlapping set of available forecasts common to both models", and the relative skill is the geometric mean of all ratios involving a model (`R/pairwise-comparisons.R:7-42, 293-311`).
- It also offers explicit imputation strategies, `impute_worst_score`, `impute_mean_score`, `impute_na_score` and `impute_model_score` (`R/impute-missing-scores.R`), "to ensure all models are evaluated on the same set of targets".

### 6. Cross-cutting resource, comprehension and validation analysis

**Performance and footprint (L1–L6).**
Every cell is measured (command and host in Evidence), cited, or `not measured`.

| Level | CovidSim | Covasim | EpiEstim | Hub / scoringutils |
|---|---|---|---|---|
| L1 authoring or repair velocity | not measured | not measured | not measured | not measured |
| L2 toolchain build | Single-shot `g++ -O2 -g` of 19 translation units: 19.07 s wall, 17.25 s user, peak RSS 270,364 kB (measured) | not measured | not measured | not measured |
| L3 elaboration or setup latency | Not separable from L4 in the test harness; network build is inside run 1 | Benchmark harness exists (`tests/test_baselines.py:104-170`, CPU-normalised to an i9-8950HK reference); not run | not measured (R); Python transcription of the whole probe 0.10 s | not measured |
| L4 execution | US integration test, 3 simulations of a 640,386-person population: 57.11 s (j1), 50.40 s (j2) wall (measured). UK test, 3,100,000 people: 5:51.63 (j2) wall (measured); j1 time contended. Report 9 reproduction: about 3 days on 64 cores, about 1 day HPC (cited, certificate). | not measured | not measured | Python WIS probe 3.97 s wall total (toy; not the R package) |
| L5 certificate or verification checking | SHA-512 comparison of 12 (US) or 50–60 (UK) files; time not separated (not measured) | `diff_sims` on one summary dict; not measured | n/a | n/a |
| L6 memory and artefacts | Peak RSS 3,245,216 kB for the US test and 3,522,936 kB for the UK test (measured); binary 4,471,928 bytes with `-g` (text 461,565 B, bss 68,574,288 B; measured with `size`); golden files 10,500 B (UK j1), 2,100 B (US j1) (tree metadata) | `tests/baseline.json` 1,971 B (tree metadata) | not measured | Hub tree has 12,074 entries at the pinned revision (tree metadata); bytes not measured |

**Human comprehensibility (C1).**
Basis: derived.
- CovidSim's reproducibility contract is four seeds plus an effective thread count plus a network file that must match that thread count. That is a six-part key once the binary's floating-point semantics are included. The effective thread count is not even an explicit input: it is min(`/c`, OpenMP's available threads, 96), so the same command line yields different realisations on hosts with different CPU counts or `OMP_NUM_THREADS`. The coupling between thread count and network file is documented only in `report9/README.md:51-52`.
- A test failure yields a SHA-512 mismatch with no location. The script's own remedy is to clone a good tree and a bad tree and diff the `.xls` output in a GUI tool (`integration-test.py:20-58`).
- The FMA probe shows the cost: one last-digit change in one cell anywhere in the output fails the gate exactly as a real behavioural change would.
- Covasim's z-score gates give per-metric z values that name the metric, but thresholds were chosen per feature (3, 5, informational), and those choices must be read from prose.
- EpiEstim's estimator is a closed-form conjugate update that a reader can check by hand. The main legibility hazard is temporal: estimates are attributed to the window end by default.
- WIS decomposes into dispersion, underprediction and overprediction, which aids diagnosis. The normaliser (`count_median_twice`) and the quantile set are silent conventions that change reported numbers.

**Simplicity and model refinement (C2).**
Basis: derived.
- **CovidSim** mixes two things: the semantic invariant (one realisation per seed tuple) and a realisation-medium accident (which stream a given agent draws from depends on thread scheduling). A counter-based generator keyed by entity and event would make results independent of thread count and remove the per-thread golden files. Examples are keying by (seed, agent id, time step, event type) or using Starsim-style per-distribution streams. The cost is generator bandwidth and a full re-baselining. This is a design hypothesis; it was not implemented or measured.
- **Golden files.** The byte-identity gate and a tolerance gate are two mechanisms aimed at one invariant. Covasim's split is more orthogonal: exact gates detect unintended change within a version, statistical gates detect behavioural change across RNG architectures.
- **EpiEstim** concentrates several distinct concerns in user preprocessing: generation-interval specification, delay deconvolution, truncation nowcasting and window placement. Of these, EpiEstim parameterises only the generation interval and the window.

**Validation coverage (V1–V4).**
Basis: derived, unless stated.

| Class | Evidence present | Absent or not examined |
|---|---|---|
| V1 specification adequacy and non-vacuity | EpiEstim snapshot tests pin numerical outputs, and the independent transcription agrees to 4.6×10⁻⁸ (execution). CovidSim's run-1 vs run-2 equality test is non-vacuous only because it requires at least 3 non-trivial files (`integration-test.py:321-323`). | No mutation testing found in any subject. Covasim gates compare summaries only. |
| V2 compiler and lowering | CovidSim cross-compiler claim (documentation). This report's flag matrix: `-O0`/`-O2`/`-O3`/`-ffp-contract=off` pass; FMA contraction and `-ffast-math` fail (execution). | No differential testing across OpenMP runtimes. MSVC and Intel builds not run. CI images (`.github/workflows/linux_distribution_check.yml`) vary distributions but not FP flags. |
| V3 concurrency | CovidSim tests run 1 and 2 threads only. Static schedules make results a function of thread count (source). | No test at more than 2 threads in CI. Floating-point reduction-order sensitivity not tested. No race detector (for example ThreadSanitizer) runs found. |
| V4 field and plant validation | Edeling et al.: CovidSim "fails to describe validation data well" (cited). Forecast hubs validate prospectively against later observed truth (Cramer et al.). | CODECHECK explicitly does not test correctness. Covasim real-data calibration not examined. |

## Boundaries

- **Not examined.**
  - Build or run of the CODECHECK-era revision `b125307e…`.
  - MSVC, Clang, Intel and AArch64 builds of CovidSim.
  - Thread counts other than 1 and 2.
  - CMake's exact `RelWithDebInfo` flags (the build used direct `g++`).
  - Whether the double-precision OpenMP reductions at `SetupModel.cpp:646-666, 818-820` feed any hashed output.
  - The Report 9 policy conclusions themselves.
- **Unknown.** Whether CovidSim at a fixed thread count is reproducible across OpenMP runtimes (libgomp vs LLVM libomp vs MSVC), given floating-point reductions whose combination order is implementation-defined. The passing 2-thread tests on one runtime do not settle this.
- **Known not to apply.**
  - The claim "deterministic across compilers" does not extend to builds with FMA contraction or `-ffast-math`. On this host `-march=native -ffp-contract=fast` and `-ffast-math` both failed the US goldens, and both produced divergent realisations.
  - The certificate's "deterministic across all platforms" refers to a fixed *effective* thread count. It does not cover a changed `/c:`, since all 50 common UK golden hashes differ between 1 and 2 threads. Nor does it cover hosts where `/c:` exceeds the available OpenMP threads.
- **Not measured.**
  - Every L1 cell.
  - Covasim and EpiEstim runtimes and memory.
  - R-package runtimes of scoringutils.
  - Per-run (as opposed to per-test) CovidSim timing.
  - The magnitude of 32- vs 64-bit divergence in Covasim.
- **Not run in Covasim.** Covasim was not installed or executed because no package installation was performed. All Covasim statements are source or documentation. The z-score values quoted are upstream claims, not reproduced here.
- **EpiEstim.** The R package was not executed. The transcription was validated only on the `parametric_si` certain-SI path (snapshot Example 3). `uncertain_si`, `si_from_data`, back-imputation and aggregated-data paths are described from source only.
- **Toy-model limits.**
  - The renewal toy is deterministic (expected values, no Poisson noise), so it shows bias direction and lag but not variance or coverage.
  - The truncation example multiplies each infection day by the delay CDF, which is an idealised fully known delay.
  - The WIS F4 and F5 cases are constructed to exhibit a mechanism. They do not show that any hub model behaved this way.
- **Unsupported stronger conclusions.**
  - Neither the passing checksum tests nor the CODECHECK certificate establishes that CovidSim's outputs are correct or calibrated.
  - The ensemble's relative WIS of 0.61 is specific to Cramer et al.'s 79-week incident-death period and eligibility rules.
  - Propriety of ratio-based relative WIS rankings under strategic submission was not analysed (unknown).
  - The CMake WIN32 `fp:strict` observation is a static reading of CMake semantics. Its practical effect on MSVC builds, which default to `/fp:precise`, was not tested.

## Evidence

Evidence acquired on 2026-11-20. GitHub revisions resolved through the GitHub REST API; file contents read from `raw.githubusercontent.com` at the pinned SHAs. DOIs verified against Crossref (journal articles) and DataCite (`10.25561/77482`, `10.5281/zenodo.3865491`).

**Source locations.**
- `mrc-ide/covid-sim@b719de9df5909f8fc47753dd1d2baf89fc415943`: `src/Rand.cpp:28-81`; `src/Constants.h:88-89`; `src/SetupModel.cpp:39-43, 294-297, 646-666, 818-820`; `src/CovidSim.cpp:176, 245-255, 316-370, 1431-1435`; `src/CLI.cpp:164-174`; `src/CMakeLists.txt:14, 24-32`; `tests/CMakeLists.txt:6-38`; `tests/integration-test.py:60-83, 307-399`; `tests/{uk,us}-input/results-j{1,2}.cksum`; `README.md:23-26`; `report9/README.md:6, 12, 49-58`.
- `mrc-ide/covid-sim@b125307e13d0a5226bff78b472b61a51516064e7`: `tests/CMakeLists.txt` (single test per input), `tests/integration-test.py:200-262` (`mt_loop[1]='st-'`, `mt_loop[2]='mt-'`), `tests/*/results.checksums.txt`, `src/CMakeLists.txt:17`.
- `codecheckers/covid-report9@7e3d7b0559659699ea90be612ad0479db62fb1fa`: `codecheck/codecheck.Rmd:75-117, 120-188, 211-219`; `codecheck.yml`; `GB_suppress_release/runonce.sh`.
- `InstituteforDiseaseModeling/covasim@9454c841cda45d431d7c0eb9ec1edfa28240b11a`: `covasim/version.py`; `covasim/sim.py:1-10`; `covasim/run.py:904-1065`; `covasim/misc.py:149-260`; `covasim/settings.py:218-222`; `tests/test_baselines.py:11-170`; `tests/baseline.json`; `tests/migrate3to4/parity.py:1-64`; `tests/migrate3to4/README.md`; `CHANGELOG.md` (4.0.0–4.0.2).
- `mrc-ide/EpiEstim@402982637562690073884b58100c80d98b6a8538`: `R/estimate_R.R:383-485, 519-621, 756-800`; `R/make_config.R:280-313`; `R/discr_si.R:52-76`; `R/overall_infectivity.R:52-63`; `R/utilities.R:225-226`; `R/backimputation.R`; `tests/testthat/test-estimate_R.R`; `tests/testthat/_snaps/estimate_R.md` (Examples 1 and 3); `NEWS.md`.
- `reichlab/covid19-forecast-hub@3a6997b6abdcfabe321dd059ebe32334095d49b5`: `data-processed/README.md:1-20, 286-315`; `data-processed/COVIDhub-ensemble/metadata-COVIDhub-ensemble.txt`; `ensemble-metadata/2024-04-29-inc_hosp-model-{eligibility,weights}.csv`; `ensemble-metadata/2020-05-19-model-eligibility.csv`.
- `reichlab/covidEnsembles@9b46312a6fd3635ac4e7e9c03ac29ccb0ad69b5f`: `code/application/weekly-ensemble/build_ensembles.R:55-190`; `R/model_eligibility.R:263-350`; `R/qra_fit_convenience.R:225-240`.
- `epiforecasts/scoringutils@779d7d68fa34d80146fdfd4b46f5919c5d61d982`: `R/metrics-interval-range.R:154-200`; `R/metrics-quantile.R:85-262, 683-725`; `R/pairwise-comparisons.R:1-50, 280-320`; `R/impute-missing-scores.R:1-40`.

**Literature (all DOIs verified).**
- Cori, Ferguson, Fraser, Cauchemez, Am J Epidemiol 178:1505-1512 (2013), `10.1093/aje/kwt133`.
- Gostic et al., PLoS Comput Biol 16:e1008409 (2020), `10.1371/journal.pcbi.1008409`. Quoted passages on GI misspecification, smoothing windows and right truncation, and the EpiEstim uncertainty statement.
- Bracher, Ray, Gneiting, Reich, PLoS Comput Biol 17:e1008618 (2021), `10.1371/journal.pcbi.1008618`.
- Gneiting & Raftery, JASA 102:359-378 (2007), `10.1198/016214506000001437`.
- Cramer et al., PNAS 119:e2113561119 (2022), `10.1073/pnas.2113561119`.
- Ray et al., Int J Forecast 39:1366-1383 (2023), `10.1016/j.ijforecast.2022.06.005`.
- Bosse et al., PLoS Comput Biol 19:e1011393 (2023), `10.1371/journal.pcbi.1011393`.
- Kerr et al., PLoS Comput Biol 17:e1009149 (2021), `10.1371/journal.pcbi.1009149`.
- Ferguson et al., Report 9, Imperial College London (2020), `10.25561/77482`.
- Eglen, CODECHECK certificate 2020-010, Zenodo (2020), `10.5281/zenodo.3865491`.
- Nüst & Eglen, F1000Research 10:253 (2021), `10.12688/f1000research.51738.2`.
- Edeling et al., Nat Comput Sci 1:128-135 (2021), `10.1038/s43588-021-00028-9`.
- L'Ecuyer & Côté, ACM TOMS 17:98-111 (1991), `10.1145/103147.103158`.

**Execution records.**
Host for all executions: x86-64 Linux workstation, Intel Xeon @ 2.60 GHz (`fma` flag present), 96 logical CPUs, Debian GCC 15.2.0, Python 3.13.15.

1. CovidSim build.
   - Source: `codeload.github.com/mrc-ide/covid-sim/tar.gz/b719de9df5909f8fc47753dd1d2baf89fc415943` (94,454,825 bytes).
   - Command: `g++ -std=c++14 -O2 -g -fopenmp -DUNIX -Iinclude -Isrc <19 sources from src/CMakeLists.txt:4-6 plus src/Geometry/Vector2.cpp> -o CovidSim`.
   - `/usr/bin/time -v`: 0:19.07 wall, 17.25 s user, 270,364 kB maximum RSS.
2. US integration test. Command as in Findings §1, run from the extracted tree, with `--r 1.5 -j {1,2}`. Results: "SUCCESS: checksums match" for both. UK test: the same command with `--input tests/uk-input --popfile data/populations/wpop_eur.txt.gz --r 1.1`, also "SUCCESS" for both.
3. Flag variants. `support/covidsim_flag_variants.sh` rebuilds with each flag set and reruns item 2. Raw summary in `support/covidsim_flag_variants.out`. Per-file and per-cell differences against the default build's output were computed with `support/cmp_outputs.py <default-out> <variant-out> <golden.cksum>`. Final cumulative counts came from `support/final_counts.py <out-dirs...>`.
4. Thread-cap check: `OMP_NUM_THREADS=1 python3 tests/integration-test.py --input tests/us-input --checksums tests/us-input/results-j1.cksum ... --r 1.5 -j 2`. Result: "SUCCESS: checksums match", with stderr `Using 1 threads` for each of the 3 runs.
5. Renewal probe: `python3 support/probe_renewal.py`. Output preserved in `support/probe_renewal.out`.
6. WIS probe: `python3 support/probe_wis.py`. Output preserved in `support/probe_wis.out`.

## Revalidation

**CovidSim determinism contract.**
- Build the pinned tree with the command in Evidence item 1. Run `integration-test.py` for `us-input` with `-j 1` and `-j 2`. Pass/fail against `results-j{1,2}.cksum` is the whole check, at about 1 minute per thread count on the host above.
- To test a new toolchain, rebuild with the candidate flags and rerun both thread counts. For FMA contraction (`-ffp-contract=fast -march=<FMA target>`), a 1-thread failure confined to last-digit cells, together with a 2-thread failure that changes final counts, reproduces the sensitivity found here.
- To check the `/c:` cap, run the `-j 2` test under `OMP_NUM_THREADS=1` against `results-j1.cksum`. A pass means `/c:` is still an upper bound.
- To recheck the per-thread-count property without running anything, diff `results-j1.cksum` against `results-j2.cksum`. Any identical hash would contradict the finding.

**CovidSim floating-point flags.**
Read `src/CMakeLists.txt` and check whether a floating-point option is attached to the `CovidSim` target with `target_compile_options` before or after `add_executable`.

**CODECHECK scope.**
Re-read `codecheck/codecheck.Rmd:75-107, 182-188, 213-216` at the pinned `covid-report9` revision.

**Covasim criteria.**
Check `tests/test_baselines.py` for the scenario and the `diff_sims` tolerance, `tests/migrate3to4/parity.py` for the z formula and threshold, and `covasim/settings.py` for the default precision. In a newer Covasim, changed thresholds or a changed default precision invalidate the corresponding rows.

**EpiEstim estimator.**
Run `support/probe_renewal.py`. Part A must report max |mean − snapshot| ≲ 1×10⁻⁷. If EpiEstim's `_snaps/estimate_R.md` Example 3 changes, paste the new `Mean(R)`/`Std(R)` columns into `SNAP_MEAN`/`SNAP_STD`. Also grep `R/estimate_R.R` for `posterior_from_si_distr` and `R/make_config.R` for `mean_prior = 5`.

**WIS conventions.**
- Run `support/probe_wis.py` (F1 must be ≲ 1×10⁻¹²).
- In scoringutils, check that `R/metrics-quantile.R` still sets `weight := ifelse(interval_range == 0, 0.5, 1)` and that `interval_score` still multiplies dispersion by `alpha / 2` when `weigh = TRUE`.
- For hub ensembles, inspect the newest `ensemble-metadata/*-model-eligibility.csv` for the reasons column, and `build_ensembles.R` for `combine_method`.
