# 2020 U.S. census redistricting data disclosure avoidance (TopDown): privacy-loss budget, exact discrete Gaussian noise, constrained post-processing, the reconstruction debate, and how redistricting ensemble samplers consume the published counts

## Summary

- **Budget.** The production persons run (US, P.L. 94-171) uses zCDP with `global_scale = 339/542`, so global ρ = (542/339)² ≈ 2.5562. Geolevels US, State, County, Tract, custom Block Group and Block get 104, 1440, 447, 687, 1256 and 165 of 4099. Each level carries 10–11 marginal queries, each with noise σ² = global_scale²/(query share × level share). Running the release's `curve.py` converts this to ε = 17.1436 at δ = 10⁻¹⁰. The release paper reports ρ = 2.63 in total: 2.56 for persons and 0.07 for housing units.
- **Allocation.** Blocks get 4.0% of ρ: the block `detailed` query has σ² ≈ 10.09 and the block `total` query σ² ≈ 7963. The State `total` query takes 32.4% of ρ even though state totals are invariant. This is because State nodes are the AIAN and non-AIAN parts of each state.
- **Invariants.** The persons run holds exact the state population totals and the block counts of housing units and of group-quarters (GQ) facilities by type. It also imposes structural constraints. No person count below the state level is invariant.
- **Noise.** The release implements the Canonne–Kamath–Steinke exact discrete Gaussian sampler with rational arithmetic and no floating point. Running that file unmodified matched the exact distribution: variances within 1% of exact, χ² p ≥ 0.068. Throughput was 84–99 k samples/s with a stand-in uniform source and 43 k/s with the release's RDRAND⊕urandom source.
- **Post-processing.** Each parent runs multi-pass inverse-variance non-negative least squares, then multi-pass binary controlled rounding, under hard parent-sum equalities. This makes the output consistent, non-negative and integral by construction, but biased. In the paper's 2010 tests, the median error was +2 for empty blocks and −26 for blocks with 1,000 or more people. A toy model reproduces the sign pattern.
- **Reconstruction.** The Census Bureau reported 46.48% exact matches and 16.85% putative re-identification. Ruggles–Van Riper's chance model, which uses block sizes and modal block race, reaches 40.9%. On blocks with fewer than 10 people, reconstruction matched about 20% against 2.6% by chance.
- **Impacts (cited).** On DAS-12.2 data, 9,915 of 10,000 Pennsylvania plans within 0.1% parity exceeded 0.1% under true counts (Kenny et al.). Production-setting data cut deviations about 10×. Cohen et al. found that ReCom districts cancel most block-level noise.
- **Samplers.** GerryChain and redist use population only in balance tests against targets computed from the supplied counts. redist's C++ core requires unsigned-integer populations. In a toy ReCom run, 36–38% (σ² ≈ 10) to 62–68% (σ² = 100) of plans that were balanced on noisy counts violated 2% on true counts, with or without post-processing.

## Applicability

- **Primary subject.** `DAS_2020_Redistricting_Production_Code` at its 2021-10-27 head, persons US run. Puerto Rico is excluded. The run is defined by `source/configs/production/pl94/person_US.ini`, which includes `person_default.ini` and `prod_default.ini`.
- **Runs described only from the paper.** `person_US.ini` refers to a `person_PR.ini`, which is absent from the tree, and there is no housing-unit config. The Puerto Rico and housing-unit runs are therefore described only from the paper.
- **Comparison subject.** `census2020-das-e2e` (2019-07-11) is used only for comparison.
- **Design document.** Abowd et al. 2022 describes the design, and its production tables equal the code constants (§1).
- **Downstream consumers.** GerryChain 1.0.0 and redist 4.3.2 consume published counts and are not linked to the DAS code. The claims about them hold for any population vector.
- **Impact papers.** These measured **2010 demonstration vintages** (DAS-4.5, DAS-12.2, DAS-19.61), not 2020 error, which cannot be observed without the confidential file.
- **Execution.** Probes ran on an x86_64 Linux workstation (Xeon @ 2.60 GHz) under CPython 3.13.15 (`support/python_env.txt`), importing upstream files from tarballs at the pins. Spark, Gurobi and the full engine were **not run**.

## Findings

### 1. Privacy-loss accounting and budget allocation

Basis: source (config + strategy class + accounting code) + derived (exact rational arithmetic) + execution (release `curve.py`) + documentation (Abowd et al. 2022 Tables 6–7).

Configuration:
- `prod_default.ini:63–66`: `approx_dp_delta = 1e-10`, `privacy_framework= zcdp`, `dp_mechanism =discrete_gaussian_mechanism`.
- `person_default.ini:70`: `global_scale = 339/542`.
- `person_US.ini:29–31`: `geolevel_budget_prop = 104/4099, 1440/4099, 447/4099, 687/4099, 1256/4099, 165/4099` (top-down order), `strategy = ProductionCandidate20210527US_mult8_add02_dsepJune3`, `query_ordering = Strategy1b_ST_CTY_TR_BG_isoTot_Ordering_dsepJune3`.

The per-query precision is computed in `engine_utils.py:488–490`:

```python
global_scale = self.budget.global_scale
if self.setup.privacy_framework in (CC.ZCDP,):
    return dpq_prop * geolevel_prop  / (global_scale**2)  # in zCDP, global_scale is not in squared units in config
```

This is 1/σ² (`primitives.py:209`: `self.sigma_sq = 1/inverse_scale`). A marginal under bounded neighbors has squared L2 sensitivity 2, so ρ_q = 1/σ², and the ρ_q sum to the global value 1/global_scale² (`budget.py:160`). `probe_budget.py` confirms the sum with exact `Fraction`s: 293764/114921.

| Geolevel | share | ρ_level | `total` q-share → σ² | `detailed` (2,016 cells) q-share → σ² | largest other query |
|---|---|---|---|---|---|
| US | 104/4099 | 0.0649 | (no `total` query) | 189/241 → 19.66 | va×hisp×cenrace 26/241 → 142.9 |
| State | 1440/4099 | 0.8980 | 3773/4097 → **1.209** | 230/4097 → 19.84 | va×hisp×cenrace 2/241 → 134.2 |
| County | 447/4099 | 0.2788 | 3126/4097 → 4.702 | 754/4097 → 19.49 | va×hisp×cenrace 101/4097 → 145.5 |
| Tract | 687/4099 | 0.4284 | 1567/4102 → 6.110 | 241/2051 → 19.86 | hisp×cenrace 1933/4102 → **4.953** |
| custom BG | 1256/4099 | 0.7833 | 1705/4099 → 3.069 | 1288/4099 → 4.063 | hisp×cenrace 1055/4099 → **4.960** |
| Block | 165/4099 | 0.1029 | 5/4097 → **7963** | 3945/4097 → **10.09** | va×hisp×cenrace 71/4097 → 560.8 |

The full 65-query table is in `support/probe_budget_out.txt`. Three consequences follow from the table (derived):
1. The strategy docstring says "increase hisp*cenrace rho by 0.2 in Tract, BG". The table agrees: ρ for that query is 0.2019 at Tract and 0.2016 at custom BG.
2. The `total` queries take 1.5293/2.5562 = 59.8% of ρ, and the `detailed` queries take 0.5481 = 21.4%.
3. The 10 non-`detailed` block queries together get 0.0038 ρ, or 0.15% of the total. A block's published total therefore comes mostly from the block `detailed` measurement plus consistency with its parents, not from the block `total` query.

Paper and code match: Abowd et al. 2022 Tables 6 and 7 equal `person_US.ini:29` and `strategies.py:886–911`. The paper also gives housing-unit level proportions of 1/205, 1/205, 7/82, 364/1025, 1759/4100 and 99/820, and states that "ρ = 2.56 used for person tables and ρ = 0.07 for housing-units tables".

**Executed conversion.** `budget.py:131` calls `zCDPEpsDeltaCurve(...).get_epsilon(float(self.delta), self.global_scale, bounded=True, tol=1e-7, zcdp=True)`. `curve.py:175–199` implements the zCDP→(ε,δ) conversion (Canonne et al., Corollary 13) by bisecting over α. Running it on the production allocations returned **ε = 17.1436 at δ = 10⁻¹⁰**. The run also printed numpy divide-by-zero warnings at the α = 1 endpoint, which the comments at `curve.py:188–189` anticipate. Kenny et al.'s "DAS-19.61" label is consistent with 17.14 plus about 2.47 for units; the units ε was not computed here. The paper calls any single (ε,δ) pair "a very incomplete analysis".

Privacy-loss checking happens in three places:
- **Static spine check.** `optimize_spine.py:441–444` asserts, with exact `Fraction` equality, that the PLB summed along every root-to-block path equals the configured total (`assert sensitivity == target_plb`). It is invoked with `check_final_plb=True` at `define_spines.py:285–288`.
- **Runtime engine check.** `topdown_engine.py:89–95` guards the runtime engine check with `if self.getboolean(CC.CHECK_BUDGET, default=True)`. Production sets `check_budget = off` (`prod_default.ini:59`), so the engine logs "Skipping privacy checks".
- **Reported total.** The reported global ε is computed in `Budget.computeTotal` from the config, not from the measurements actually taken.

### 2. Geographic spine and per-geounit allocation

Basis: source.

`prod_default.ini:31` sets `spine = opt_spine`, and `person_US.ini:13` sets `target_das_aian_areas = True`. Under `opt_spine`, `topdown_engine.py:129–130` returns a **per-geocode** PLB (`self.budget.plb_allocation.value[node.geocode]`), not the per-level share. The spine optimizer can bypass a geounit, and when it does it moves the PLB to new nodes (`optimize_spine.py:310–315`):

```python
if unit_level == CC.BLOCK_GROUP:
    plb_above_blocks[highest_geounit + 1] = plb_above_blocks[unit] + plb_blocks[unit]
    plb_blocks[highest_geounit + 1] = Fraction(0, 1)
else:
    plb_above_blocks[highest_geounit + 1] = plb_above_blocks[child] + plb_above_blocks[unit]
    plb_above_blocks[child] = Fraction(0, 1)
```

With a Gaussian-type mechanism (`epsilon_delta=True`, which is the case here), `bypassing_improves_parent` (`:350–355`) bypasses only units with a single child, or units at levels listed in `bypass_geolevels`. That list holds the internally built tract-group level when the configured hierarchy has none (`:560`), which is the case for this run. Per-path sums are preserved, so the privacy guarantee per person is unchanged. Individual nodes, however, can receive more than their level's nominal σ⁻². The table in §1 is therefore the **nominal** allocation; per-node σ² for bypassed chains differs, and no node-level PLB file was examined.

State-level nodes are keyed by `(state, aian, ...)` (`define_spines.py:13`). The state invariant is enforced as a grouped sum over the AIAN and non-AIAN parts. A comment in the engine (`topdown_engine.py:326–328`) calls this "hard-coded for a good reason ... a quirk". The "Block_Group" level is a custom block group; the paper calls it CBG and notes that it differs from tabulation block groups.

### 3. Invariants and structural constraints (persons, US)

Basis: source.

| Level | Config (`person_default.ini:75–78`, `person_US.ini:40–41`) | Meaning (source) |
|---|---|---|
| Block | `theInvariants.Block = gqhh_vect, gqhh_tot` | Unit-table counts: housing units plus GQ facilities by 8 types, and their total (`invariantsmaker.py:35–36`) |
| Block | `theConstraints.Block = hhgq_total_lb, hhgq_total_ub, nurse_nva_0` | No `tot` invariant at the block, so the bound is units × `hhgq_lb` ≤ persons in type ≤ units × 99999. `hhgq_lb[0] = 0` because "Unit table includes vacant housing units" (`Constraints_PL94_2020.py:26–27`), and 1 for GQ types (`querybase_constraints.py:121–124,183`). `nurse_nva_0` makes minors in nursing facilities a structural zero (`Constraints_PL94.py:22–26`). |
| State | `theInvariants.State = tot`; `theConstraints.State = hhgq_total_lb, hhgq_total_ub` | The person total is exact. The GQ bounds use the total: ub = total − (minimum people in other types), and lb = all persons when only one type exists (`querybase_constraints.py:160–179`). |
| US | `theConstraints.US = total` | `total` is an equality on the node's `tot` invariant (`Constraints_PL94.py:28–33`). At the US level this equals the sum of state totals (derived; how the invariant is aggregated upward was not traced). |

The release paper says invariants "deliberately bypass the DP mechanism and are reported with certainty". Hotz et al. note (citing Gong and Meng) that constraints which depend on confidential data violate the conditions of the post-processing immunity theorem. The DP guarantee therefore does not automatically cover what the invariants reveal.

### 4. Noise mechanism and its exact integer arithmetic

Basis: source + execution (upstream file) + documentation.

`primitives.py:26` selects `_rng_factory = DASRDRandIntegers`, and `RationalDiscreteGaussianMechanism` (`:199–219`) draws `RationalSimpleDiscreteGaussian(sigma_sq=self.sigma_sq, size=size, rng=rng)` and adds the draws to the true integer answer. The scalar sampler (`discrete_gaussian_utility.py:60–69`):

```python
ssqn, ssqd = sigma_sq
t: int = floorsqrt(ssqn, ssqd) + 1
c: bool = False
while not c:
    y: int = RationalScalarDiscreteLaplace(s=1, t=t, rng=rng)
    aux1n: int = abs(y) * t * ssqd - ssqn
    gamma = (aux1n * aux1n, t * ssqd * t * ssqn * 2)
    c: bool = bool(RationalScalarBernoulliExp(gamma=gamma, rng=rng))
```

This is rejection from a discrete Laplace proposal with scale t = ⌊σ⌋+1. It accepts with probability exp(−(|y|−σ²/t)²/(2σ²)), and with σ² = n/d the exponent equals (|y|·t·d − n)²/(2t²dn), exactly the tuple above (derived). The building blocks:
- **Discrete Laplace** (`:113–124`): `u = rng.integers(0, t)`, accepted with Bernoulli(exp(−u/t)); `v` counts Bernoulli(exp(−1)) successes; `y = (u + t*v) // s`; random sign, rejecting −0.
- **Bernoulli(exp(−γ))** (`:167–180`): for γ = gn/gd ≤ 1 it runs the alternating-series loop `a = rng.integers(low=0, high=gdn * k) < gn` and returns `k % 2`. For γ > 1 it decomposes γ into ⌊γ⌋ Bernoulli(exp(−1)) trials and one trial on the fractional part.
- **`floorsqrt`** (`:183–208`) uses integer comparisons only.

Floats appear only when `computeDiscreteGaussianVariance` computes the variance used to weight the optimizer (`primitives.py:293–322`), never in sampling.

The uniform source (`rngs.py:39–41,89–94`) stacks 64-bit `randomgen.RDRAND()` draws, XORs them with the same number of `os.urandom` bytes, and maps the result to [0, s) by OpenBSD rejection (`threshold = (2^L − s) mod s`). Python integers have arbitrary size, so the large denominators that γ produces are handled exactly. The paper estimates the census needs "roughly 90TB of random bytes".

**Probe** (`support/probe_dgauss.py`). It calls `RationalSimpleDiscreteGaussian` from the unmodified file and computes exact pmf, variance and fourth moment by direct summation.

| σ² (production query) | N | empirical var / exact | rel. dev (z) | χ² GOF (dof, p) | throughput |
|---|---|---|---|---|---|
| 214437516707/177339451520 ≈ 1.2092 (State total) | 200,000 | 1.2125 / 1.2092 | +0.27% (+0.87) | 6.68 (7, 0.463) | 84,209/s |
| 214437516707/21246481300 ≈ 10.0928 (Block detailed) | 200,000 | 10.0414 / 10.0928 | −0.51% (−1.61) | 28.85 (19, 0.068) | 99,036/s |
| 643312550121/80785100 ≈ 7963.26 (Block total) | 50,000 | 7888.35 / 7963.26 | −0.94% (−1.49) | 538.05 (535, 0.455) | 98,210/s |
| ≈10.0928 with the upstream `rngs.RDRandLbitInts` (unseeded) | 20,000 | 10.1394 / 10.0928 | +0.46% (+0.46) | not run | 42,919/s |

Throughput did not grow from σ² ≈ 1.2 to σ² ≈ 7963, consistent with the expected constant number of rejection rounds. The RDRAND path ran at 0.43–0.51× the stand-in's rate; it makes an `os.urandom` syscall per draw. Peak RSS for the whole process was 102,404 kB. **Not established by this probe:** RNG quality, timing behavior, or anything about Spark.

### 5. Post-processing: multi-pass NNLS then multi-pass controlled rounding

Basis: source + documentation.

The configuration (`person_default.ini:57–62`):
- `l2_optimization_approach = DataIndUserSpecifiedQueriesNPass`
- `rounder_optimization_approach = MultipassRounder`
- `DataIndNPass_toleranceType = opt_tol`
- `opt_tol_slack = 0.1`
- `seq_optimization_approach = L2PlusRounderWithBackup_interleaved`

For each (parent, children) group, top-down, the steps are:

1. **L2 objective.** For each query term, the objective is wt·(Ax−b)² with `weight = ss.diags(np.hstack([np.repeat(1. / v, n_ans) for v in st_dpq.VarList]))` (`geo_optimizers.py:141,192`). Variables have `lb = 0 if self.nnls`, so they are non-negative (`:105`). Cellwise parent equality is imposed as `model.addConstr(cons_expr == parent_sub, name=name)` (`optimizer.py:811–813`).
2. **Pass order** (`strategies.py:1791–1817`). At State, County, Tract and custom BG, pass 0 targets `('total',)` and pass 1 targets the rest. US and Block use a single pass.
3. **Pass coupling.** Pass k+1 constrains each earlier estimate to |Qx − est| ≤ tol (`l2_dataIndep_npass_optimizer.py:101–102`). tol is the smallest feasible value found by a barrier LP capped at `BarIterLimit = 50`, plus `opt_tol_slack` (`:44,150–158`).
4. **Rounding.** The rounder uses binary variables over ⌊x⌋ (`simple_rounder.py:72`, `vtype=gb.GRB.BINARY`), the same hard parent equalities, a cellwise objective (1−2·frac)·b (`:95`), and per-query L1 penalties |Q(⌊x⌋+b) − round(Q x)| (`multipass_rounder.py:133–134`). Earlier passes are then frozen with `csrQ @ x - np.around(csrQ @ x.X) == 0.0` (`:142`).
5. **Failure handling.** The interleaved optimizer has no failsafe. `sequential_optimizers.py:343–344` raises `NotImplementedError("ERROR: Interleaved optimization does not currently support failsafe!")` on a non-acceptable L2 status.

**Source observation (consequence not determined).** The config distinguishes `L2_acceptable_statuses = OPTIMAL, SUBOPTIMAL, ITERATION_LIMIT` from `Rounder_acceptable_statuses = OPTIMAL` (`prod_default.ini:107–108`). But the interleaved path checks the rounder's final status with `checkModelStatus` (`sequential_optimizers.py:351`), whose test is `if m_status not in self.acceptable_l2_statuses:` (`:244`). A rounder status of `SUBOPTIMAL` would therefore be accepted. A suboptimal solution still satisfies the hard equalities, so consistency would be unaffected. Whether any production node hit this is unknown.

Which properties hold, and on what basis:

| Property of published tables | How established |
|---|---|
| Hierarchical consistency (children sum to parent, cellwise) | By construction (hard equality in both stages), conditional on solver success |
| Non-negativity, integrality | By construction: variable bounds; binary round-up over floor (L2 values < 1e-7 are zeroed, `geo_optimizers.py:244–245`) |
| Invariants and structural zeros | By construction (equality and inequality constraints) |
| zCDP of the noisy measurements | By proof in the cited mechanism paper + composition; implementation correspondence checked by code reading and by the moment and pmf probe (§4) |
| Privacy of published tables | Post-processing of measurements **plus** invariants; the invariant part is outside DP accounting (§3) |
| Unbiasedness | Measurements are unbiased; published counts are **not** (§7) |

### 6. Differences from the 2018 end-to-end release

Basis: source.

| Aspect | e2e (`E2E_2018_CONFIG.ini`, `programs/engine/`) | 2021 production |
|---|---|---|
| Privacy definition | pure ε-DP, `epsilon_budget_total: 0.2499`, `global_sensitivity: 2.0` (lines 67–68) | zCDP ρ ≈ 2.5562 (persons), δ only for reporting |
| Levels | Block, Block_Group, Tract, County with `geolevel_budget_prop: 0.25,0.25,0.25,0.25` (71) | 6 levels on an optimized spine with per-node PLB |
| Queries | `detailedprop: 0.1`, `DPqueries: hhgq, va_hisp_race`, `queriesprop: 0.225, 0.675` (74–78) | 11 marginals per level, rational shares |
| Noise | Two-sided geometric as the difference of two `numpy` geometric draws with float `self.p = 1 - np.exp(-epsilon / float(sensitivity))` (`primitives.py:67`), reseeding numpy's generator from the OS before each scalar (`:27–28`) | Rational, float-free discrete Gaussian; RDRAND⊕urandom integers |
| Invariants | Block `gqhh_vect, gqhh_tot`; County `tot` (83–84) | Block `gqhh_vect, gqhh_tot`; State `tot` |
| Post-processing | L2 then integer rounding with a backup-feasibility path (`geoimpgbopt.py`) | Multi-pass L2 and multi-pass rounder, no failsafe on the interleaved path |
| Shipped tests | 134 `.py` files under test directories, including `programs/engine/unit_tests` | No engine or optimizer tests in the tree. Test directories exist only under `python_dvs/` and `das_framework/ctools/`, and source comments reference absent `programs.engine.tests` modules (`primitives.py:14–17`). |

### 7. Post-processing bias: production evidence and a toy mechanism

Basis: documentation (release paper experiments on 2010 data) + execution (toy model of NNLS and rounding, not the production optimizer).

Abowd et al. 2022 Table 12 (baseline1 = June 8, 2021 production-settings demonstration, ρ = 2.56) gives signed error in the block total by true size:
- **population 0** (191,175 blocks): mean |e| 2.746, median **+2**, 97.5th percentile +11.
- **1–9** (1,823,665): median +1.
- **10–99** (3,666,266): median 0.
- **100–999** (707,291): median −5.
- **1,000 or more** (9,805): mean |e| 27.124, median **−26**, 25th percentile −41.

In Table 9, mean absolute total-population error is 0.00 for State and US, 1.75 for County, 1.94 for Tract, 16.00 for "Block Group" and 4.85 for Block. A fresh-randomness rerun changes these by at most 0.01, and ρ + 10% lowers them by about 3%. The paper attributes the bias to post-processing, not to the DP mechanism: "the noisy measurements themselves are unbiased".

**Toy** (`support/probe_toy.py`, part A). The setup:
- 100 cells under one parent with invariant total T = 3324: 40 zero cells, 30 in 1–5, 20 in 6–30, and 10 in 100–500.
- Noise is drawn by the upstream sampler; 4,000 trials.
- `l2proj` is the Euclidean projection onto {x ≥ 0, Σx = T} followed by largest-remainder rounding.

Mean signed error per cell (95% half-width ≤ 0.09):

| σ² | method | 0 | 1–5 | 6–30 | 100–500 | total error |
|---|---|---|---|---|---|---|
| 10.0928 | raw | −0.001 | +0.009 | +0.005 | −0.010 | +0.22 |
| 10.0928 | clamp at 0 | +1.258 | +0.439 | +0.007 | −0.010 | +63.51 |
| 10.0928 | l2proj | **+0.920** | −0.251 | −0.979 | −0.966 | 0 |
| 100 | l2proj | **+2.300** | +0.579 | −3.348 | −4.240 | 0 |

The mechanism (derived): projecting onto the simplex subtracts one common threshold θ from every cell above it and zeroes the rest. The positive mass forced into zero and small cells is therefore taken from the larger cells, which explains the sign pattern in Table 12. The toy has one level and one query and does no multi-pass weighting. Its magnitudes are **not** predictions for the production system.

### 8. Reconstruction evidence and the Ruggles–Van Riper critique

Basis: documentation. The Census Bureau's own declaration and slides were not examined; the numbers below come from Ruggles–Van Riper's account of them and from Hotz et al.

The experiment, as described by Ruggles–Van Riper (citing Abowd 2021):
- It used 6.2 billion statistics from nine 2010 tables and solved for record-level rows in about 6.3 million inhabited blocks with Gurobi.
- 46.48% of reconstructed rows matched a real person on block, age, sex, race and ethnicity.
- 57% of real persons are unique on that tuple within their block.
- Linking to commercial data matched 45% of rows on block, age and sex; 38% of those names were confirmed, giving 16.85% putative re-identification.
- This was extrapolated to "at least 52 million" (17%) or, with better commercial data, about 179 million (58%) people. Hotz et al. quote "between 52 million and 179 million of the almost 309 million".

Ruggles–Van Riper's null model:
- 10,000 simulated blocks drawn from the population-weighted block-size and age–sex distributions. A random age–sex pair is present 52.6% of the time; at the average person's block size of 249.5 the rate is 75.8%.
- Assigning each block's modal race and ethnicity is correct 77.8% of the time, giving **40.9%** on all four attributes.
- In the swapping experiment, the match rate was 44.6% unswapped versus 42.7% under extreme swapping.

| | Establishes | Does not establish |
|---|---|---|
| Census Bureau experiment | Large-scale reconstruction from published 2010 tables is computationally feasible; record-level agreement and putative re-identification rates under its metrics | Excess risk over a baseline; no null was reported for either the match step or the name step |
| Ruggles–Van Riper | Much of the aggregate 46.48% is reachable by a chance model, and the 45% commercial match is below their 52.6% age–sex chance rate | Their null is **not** information-free: it uses published block-size distributions and modal block race (derived). On blocks under 10 people, reconstruction (~20%) beat their chance rate (2.6%) roughly 8× (derived from their numbers), and they attribute the ~20% to 5-year age groups. They give no null for name confirmation. |

Dinur–Nissim (2003) is the theoretical result both sides cite, and Garfinkel–Abowd–Martindale (2019) is the expository account. Both DOIs were verified, but their content was not examined for this report.

### 9. Independent impact analyses (2010 demonstration data)

Basis: documentation.

**Kenny et al. 2021** (Science Advances; PMC full text). The study's Table 1 lists 12 cases across 10 states, comparing precinct populations under 2010 Census, DAS-4.5 and DAS-12.2 data. It ran the redist package (version 3.x as cited): SMC for congressional plans and merge-split MCMC for most state-legislative plans, with 10,000–200,000 simulations per case.
- A GAM on precinct error by turnout, partisanship, density, White share and HHI "explains about 9 to 12%" of the variance. Mixed-race and mixed-partisan precincts are systematically undercounted.
- The enacted Pennsylvania congressional map has a maximum difference of 283 people (0.04%). That difference is 3,893 under DAS-4.5 and 2,287 under DAS-12.2. Of 10,000 plans simulated on DAS-12.2 at 0.1% parity, 9,915 exceed 0.1% under true counts.
- The Louisiana State Senate enacted map has parity 4.97% under true counts and exceeds 5% under the DAS data.
- A postscript on DAS-19.61 reports enacted congressional-district deviations of −216 to 319, versus −2153 to 2164 under DAS-12.2, "a nearly 10-fold improvement". It also reports that the Louisiana enacted map stays valid at 5%. Qualitative partisan, racial and majority-minority district shifts persisted, and BISG underestimated minority voters in the school-board case.
- The authors state that the Bureau had not released noise-only data, so the effects of noise and post-processing could not be separated.

**Cohen et al. 2021** (FORC; arXiv v1; reconstructed Texas data). The study ran TopDown and the ToyDown simplification over Dallas County with k = 4 and k = 175 districts: 400 districts per algorithm, 16 noising runs each.
- ReCom districts built from blocks have error much closer to tract-built districts than to disconnected block-built ones, because ReCom keeps higher-level units whole.
- Spatially autocorrelated post-processing corrections reduce cancellation for compact districts.
- For districts of about 13,000 people at ε = 1, errors were "in the low hundreds".
- Conclusion: "TopDown will not threaten the ability to produce districts with tolerable population balance or to detect signals of racial polarization".

**Mueller and Santos-Lozada 2022.** Only the abstract was examined. It reports significant discrepancies at the county level in counts and 2000–2010 growth rates for non-Hispanic Black, Hispanic and non-Hispanic American Indian populations, with discrepancies "increas[ing] dramatically" from urban to rural. The total and non-Hispanic White populations were the exceptions. Its numeric results were not examined.

**Hotz et al. 2022** is an essay. It argues for benefit–cost assessment and for a disclosure-risk measure other than DP, and it notes the invariant and post-processing theorem gap.

The studies disagree, and the disagreement is preserved here rather than resolved. Kenny et al. (precinct-built plans, strict parity, DAS-12.2) and Cohen et al. (ReCom districts, tolerable balance, ε = 1 TopDown run on reconstructed data) studied different data vintages, geographic building blocks and tolerances.

### 10. How ensemble samplers consume population, and their response to perturbation

Basis: source + execution (real GerryChain on toy data).

**GerryChain.**
- `recom` merges two adjacent districts and calls `epsilon_tree_bipartition`. That function sets `lb_pop = pop_target * (1 - epsilon)` and `ub_pop = pop_target * (1 + epsilon)` and raises `PopulationBalanceError` unless both halves satisfy `lb_pop <= x <= ub_pop` (`tree_proposals.py:95–97,127–139`).
- Candidate cuts use `abs(population - self.ideal_pop) <= self.epsilon * self.ideal_pop` (`bipartition_tree.py:189`). For bisection, a cut qualifies only if both sides pass (`:714–716`).
- `within_percent_of_ideal_population` fixes `ideal_population = total_population / number_of_districts` from the **initial partition's** tally and bounds every district (`validity.py:92–97`).

Population is thus used only additively, as node values summed over subtrees, plus one ratio test. Sign and integrality are not checked: negative or fractional values are summed like any others (derived from the code; not executed with negative inputs).

**redist.**
- `redist_map` sets `target <- sum(x[[pop_col]])/ndists` and `pop_bounds <- target*c(1 - pop_tol, 1, 1 + pop_tol)` (`redist_map.R:242–243`).
- `redist_smc` aborts if any unit's population is at least `pop_bounds[3]` (`redist_smc.R:191–198`) and passes `pop_bounds[2], pop_bounds[1], pop_bounds[3]` to `smc_plans` (`:266–267`).
- The C++ entry point is `List smc_plans(int N, List l, const uvec &counties, const uvec &pop, ...)` (`smc.cpp:17`). A cut is admissible only if `lower < below && below < upper` (`:535,539`; strict inequalities, unlike GerryChain's inclusive bound). With `pop_temper > 0`, each split adds `pop_temper*pop_pen` with `pop_pen = sqrt(n_distr-2)*log(1e-12 + dev)` (`:450–456`).
- Because `pop` is `arma::uvec`, populations are unsigned integers. Raw noisy measurements (negative or non-integer) are outside the input domain, while post-processed counts satisfy it (derived; the R-to-uvec conversion of negative doubles was not executed).

**Toy ensemble** (`support/probe_toy.py`, part B).
- Graph: a 20×20 grid with heterogeneous populations (10% zeros, log-normal otherwise; T = 18,864), k = 4.
- Sampler: ReCom with ε = 0.02, plus contiguity and 2% bounds on the supplied counts. 3,000 steps per chain, seeds 11 and 12.
- Each plan is evaluated on true populations.
- Vote shares follow a fixed west–east gradient and are not noised.

| node noise σ² | input | plans > 2% under true counts | mean / p95 / max true deviation | A-seat mean |
|---|---|---|---|---|
| — | TRUE | 0.000 / 0.000 | 1.50% / 1.96% / 1.99% | 1.928 / 1.935 |
| 10.0928 | RAW (noise only) | 0.374 / 0.364 | 1.79% / 2.83% / 3.65% | 1.951 / 1.985 |
| 10.0928 | PP (noise + l2proj, total invariant) | 0.384 / 0.364 | 1.78% / 2.79% / 3.69% | 1.956 / 1.933 |
| 100 | RAW | 0.676 / 0.671 | 2.56% / 4.38% / 6.83% | 1.974 / 1.933 |
| 100 | PP | 0.618 / 0.639 | 2.40% / 4.13% / 5.94% | 1.957 / 1.950 |

Paired values are seed 11 / seed 12. For the deviations, the mean and p95 are averaged over the two seeds, and the max is taken over both. In this toy:
- Population-balance validity degrades mainly because of noise. Post-processing changed the violation rate by ≤ 0.06.
- The seat distribution moved by less than the seed-to-seed spread. For example, the share of one-seat plans was 0.086 versus 0.032 for RAW at σ² ≈ 10 across seeds, so a seat effect cannot be detected at this chain length.

None of this transfers quantitatively to real states.

### 11. Performance and resource footprint (L1–L6)

| Level | DAS production | GerryChain / redist |
|---|---|---|
| L1 authoring/maintenance | Release size: 36,705 lines of Python under `source/programs`, excluding `tests/` directories (`wc -l`). Effort per line and change cost: not measured. | not measured |
| L2 toolchain build | Not applicable (interpreted Python); Gurobi 9.1, Spark 3.0.1 and EMR 6.2 per the paper. Build time: not measured. | pip install of GerryChain and its dependencies succeeded; time not measured. redist build: not measured. |
| L3 solve latency | Gurobi per-node solve times: not measured (no license). Config: thread counts 96 (root and State), 32 County, 16 Tract, 8 BG, 4 Block (`prod_default.ini:91–101`); `optimalitytol = 1e-6`, `feasibilitytol = 1e-7` (`:80,83`). The paper says production started June 25, 2021, with the MDF on June 26. | not applicable |
| L4 execution | Discrete Gaussian: 84–99 k samples/s (stand-in RNG), 43 k samples/s (upstream RDRAND path), single core (measured). Each geounit measures 2,603 cells (2,602 at US), summed from the query cardinalities in Table 7 (derived). | ReCom on 400 nodes, k = 4: 104–174 steps/s (measured, toy). redist runtime: not measured. |
| L5 proof/certificate checking | Not applicable: no machine-checked proof. The "DAS Certificate" PDFs are run attestations, not checkable certificates. | not applicable |
| L6 memory/disk | Paper: about 90 TB of random bytes; r5.24xlarge nodes (96 cores, 768 GiB), 8–30 workers, 64 GiB executor memory. Probe peak RSS 102 MB. Release tarball 5,570,306 bytes. | Toy probe peak RSS 106 MB; GerryChain tarball 21,464,524 bytes; redist 1,789,070 bytes |

### 12. Comprehensibility and simplicity (C1–C2)

**C1 (human).** Predicting one block's published count requires about seven concepts at once: global ρ; six level shares; eleven query shares and their σ²; the optimized spine (custom block groups, AIAN-split states, PLB moved by bypassing); invariants versus edit constraints versus structural zeros; two-pass NNLS with solver-determined tolerances; and multi-pass rounding. The reasoning is **nonlocal**: a block's error depends on noise at every ancestor and on how siblings were adjusted, as the size-dependent bias in §7 shows. The budget is fully auditable: this report re-derived ρ and ε exactly from rational config values. Post-processing is not: its output depends on Gurobi tolerances, the iteration cap in the tolerance search, and status handling, and per-node solver diagnostics are not published. For agents, the exact rational config is easy to process. The opacity is in the optimizer, not in the accounting.

**C2 (simplicity).**
- *Core invariants:* (a) per-person ρ along every root-to-block path equals the configured total; (b) outputs are consistent, non-negative, integral, and satisfy the invariants.
- *Accidents of the realization medium:* custom block groups, the AIAN state split and the "quirk" sum constraint that goes with it, and Python `assert` as the only enforcement of per-path sums. An `assert` is skipped under `python -O`, and whether production ran that way is unknown.
- *Several mechanisms for one invariant:* invariant (a) is computed or checked in three places with different strengths. The spine assertion is exact; the engine check is disabled in production; the reported ε is computed from config.
- *A unifying model (derived proposal, not a measured improvement):* treat every measurement as a weighted row (query, node, σ²), with priority classes for estimation. Two-pass NNLS, frozen rounding passes and pass-specific tolerances then become instances of prioritized least squares followed by one controlled-rounding problem. The proposal does not remove the difficulty of explaining bias to users, which comes from imposing non-negativity, not from the code structure.

### 13. Validation (V1–V4)

- **V1 (adequacy).**
  - *Checked here:* code constants equal the paper's Tables 6–7; the release's `curve.py` gives ε = 17.1436 at δ = 10⁻¹⁰; the sampler matches the exact distribution's moments and pmf at three σ².
  - *Missing from the release:* engine and optimizer unit tests (§6). Mutation testing, property-based testing of the post-processing guarantees, and differential testing against an independent optimizer were not found in the release and were not run.
- **V2 (lowering and checker soundness).** No independent re-implementation of TopDown was examined. Kenny et al. could not separate noise from post-processing; the toy in §7 separates them only in caricature. Malformed-certificate fuzzing is not applicable.
- **V3 (physical randomness).** Production trusts RDRAND⊕urandom (`rngs.py:39–41`). Its entropy and statistical quality were not tested here. The paper states that exact rational sampling avoids the floating-point vulnerabilities described by Mironov (2012). Timing side channels of the variable-time rejection sampler and Spark-level determinism were not examined.
- **V4 (field validation and user comprehension).** Real-world validation consists of 2010-data runs (paper Tables 9–12) and independent demonstration-data studies (§9). Studies of whether data users' mental models of the error are correct: none were found or examined.

## Boundaries

- **Not examined:**
  - the housing-unit and Puerto Rico runs, other 2020 products, and 2020 noisy measurement files;
  - node-level PLB under `opt_spine`;
  - the reader, writer and validator modules;
  - the certificate and memo PDFs in `docs/`;
  - the Bureau's 2021 declarations and slides;
  - full texts of Mueller–Santos-Lozada (abstract only), Dinur–Nissim, Garfinkel et al., Abowd 2018, and Cohen et al.'s HDSR version (FORC/arXiv v1 examined instead);
  - DeFord et al. and McCartan–Imai beyond their abstracts;
  - redist execution;
  - GerryChain with negative or fractional populations.
- **Not measured** (the "not measured" cells in §11): Gurobi solve time and memory; production wall-clock beyond the paper's dates; per-geounit cost; authoring effort; build times; RDRAND/urandom quality; sampler timing leakage; redist runtime.
- **Unknown:** whether any production rounder returned `SUBOPTIMAL` (§5), and whether production ran Python with assertions enabled.
- **Known not to apply:** toy results (§7 part A, §10 table) are not properties of the production DAS or of any state. The sampler probe used a stand-in uniform source except in the 20,000-draw RDRAND pass.
- **Conclusions the evidence does not support:**
  - that 2020 errors equal those of any demonstration vintage;
  - that chance explains all reconstruction success (small blocks contradict this);
  - that reconstruction implies confirmed re-identification beyond the reported metrics;
  - that ensemble analyses are robust, or fragile, in general (Kenny et al. and Cohen et al. differ in data, tolerances and building blocks);
  - that passing the moment and χ² checks proves exactness (p = 0.068 at σ² ≈ 10 is unremarkable, not strong evidence).

## Evidence

Evidence was gathered on 2026-11-21 (UTC).

**Pinned trees.** Each was fetched as a codeload tarball and its head verified with `gh api repos/<r>/commits/HEAD`:
- `uscensusbureau/DAS_2020_Redistricting_Production_Code` @ `289ee463936a6f0efcf2e378abe410ec01d0e140`, files:
  - `source/configs/production/{prod_default.ini,pl94/person_default.ini,pl94/person_US.ini}`
  - `source/programs/engine/{budget.py,curve.py,discrete_gaussian_utility.py,engine_utils.py,primitives.py,rngs.py,topdown_engine.py}`
  - `source/programs/strategies/strategies.py:873–914,1764–1850`
  - `source/programs/geographic_spines/{optimize_spine.py:275–446,define_spines.py:13,285–288}`
  - `source/programs/invariants/invariantsmaker.py`
  - `source/programs/constraints/{Constraints_PL94.py,Constraints_PL94_2020.py,querybase_constraints.py:103–183}`
  - `source/programs/optimization/{sequential_optimizers.py,l2_dataIndep_npass_optimizer.py,geo_optimizers.py,optimizer.py:690–813,multipass_rounder.py,simple_rounder.py}`
- `uscensusbureau/census2020-das-e2e` @ `d9faabf3de987b890a5079b914f5aba597215b14`: `E2E_2018_CONFIG.ini:66–90`, `programs/engine/{primitives.py,topdown_engine.py:607–682}`.
- `mggg/GerryChain` @ `0edc2789b82e239c407e2da6d1bfe3c2ad111276`: `gerrychain/proposals/tree_proposals.py:55–323`, `gerrychain/tree/bipartition_tree.py:137–213,622–718`, `gerrychain/constraints/validity.py:73–97`.
- `alarm-redist/redist` @ `2cc8b137cebbe15b8fc96295b7e2f1dd390c5577`: `R/redist_map.R:226–245`, `R/redist_smc.R:185–275`, `src/smc.cpp:17–60,335–460,505–565`.

**Literature.** DOIs were verified with the Crossref works API unless noted.
- **Full text examined:**
  - 10.1162/99608f92.529e3cb9 (via arXiv HTML v1);
  - 10.1126/sciadv.abk3283 (via PMC8494446);
  - 10.1007/s11113-021-09674-3;
  - 10.1073/pnas.2104906119.
- **Abstract only:**
  - 10.1007/s11113-022-09698-3;
  - 10.1162/99608f92.eb30390f (arXiv:1911.05725);
  - 10.1214/23-AOAS1763 (arXiv:2008.06131);
  - 10.29012/jpc.784 (arXiv:2004.00010).
- **10.4230/LIPIcs.FORC.2021.5:** not in Crossref; verified through the doi.org handle API, which resolves to the Dagstuhl DROPS record. Text examined via arXiv:2203.05085 v1 HTML.
- **Metadata only, content not examined:**
  - 10.1162/99608f92.22fd8a0e (Cohen et al., HDSR);
  - 10.1145/773153.773173 (Dinur–Nissim);
  - 10.1145/3219819.3226070 (Abowd 2018);
  - 10.1145/3287287 (Garfinkel et al.).

**Execution.** Support files are in `support/`. The probes were run as follows, where `<DAS>` is the extracted production tree and `<VENV>` holds the packages in `python_env.txt`:

```
<VENV>/bin/python probe_budget.py --curve <DAS>/source/programs/engine          # -> probe_budget_out.txt
<VENV>/bin/python probe_dgauss.py <DAS>/source/programs/engine --rdrand         # -> probe_dgauss_out.txt
<VENV>/bin/python probe_toy.py    <DAS>/source/programs/engine 3000             # -> probe_toy_out.txt
```

The seeds are fixed in the scripts: 20251121–20251123 for the sampler; 7, 99, 2026, 11 and 12 for the toy. The RDRAND pass is unseeded. `/usr/bin/time -v` peaks are in `probe_resource_usage.txt`.

## Revalidation

- **Budget.** Diff `person_US.ini`, `person_default.ini` and the selected strategy class at a new revision, then rerun `probe_budget.py`. The global ρ must equal the sum of per-query ρ, and `curve.py` ε must match the published value.
- **Sampler.** Diff `discrete_gaussian_utility.py:51–208` and `rngs.py`. If they changed, rerun `probe_dgauss.py`. A correct exact sampler should give |z| ≲ 3 for the variance and an unremarkable χ² p-value. Increase N to sharpen the check.
- **Post-processing semantics.** Check that `l2_optimization_approach`, `rounder_optimization_approach`, `opt_tol_slack`, the acceptable-status lists, and `checkModelStatus` (`sequential_optimizers.py:234–246`) are unchanged.
- **Production bias.** Compare new releases' size-stratified signed-error tables against Table 12 of the release paper.
- **Samplers.**
  - In GerryChain, check that `is_within_epsilon` and `epsilon_tree_bipartition` keep the inclusive bound.
  - In redist, check that `smc_plans` still takes `const arma::uvec &pop` and the strict `lower < below && below < upper` test.
  - Rerun `probe_toy.py` (about 4 minutes) after sampler upgrades. Only the violation-rate pattern is meaningful; seat differences require much longer chains.
