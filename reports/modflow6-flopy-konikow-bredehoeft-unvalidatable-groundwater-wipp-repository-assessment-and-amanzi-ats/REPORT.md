# MODFLOW 6 and FloPy convergence, mass balance and test suites, Amanzi/ATS verification, the "groundwater models cannot be validated" debate, and the 1996 WIPP performance-assessment structure

## Summary

- **MODFLOW 6 decides nonlinear convergence only on the head change, and its mass balance is a report, not a gate.** At `MODFLOW-ORG/modflow6@6565dc81cada70781208a1a1659565597046c171` (version string `6.9.0.dev0`), an outer iteration converges when `abs(max_dvc) <= dvclose` (`src/Solution/NumericalSolution.f90:3173-3183`). The budget percent discrepancy is `100*(in-out)/((in+out)/2)` and is printed with `F15.2`, i.e. to two decimals (`src/Utilities/Budget.f90:262-269,300-301`). In a measured Newton–Raphson unconfined-flow run, `OUTER_DVCLOSE = 1 m` stopped after 6 outer iterations. The run exited with code 0, reported `PERCENT DISCREPANCY = -0.76` and carried a 2.6 cm head error relative to a tightly converged run. With `OUTER_DVCLOSE <= 0.01 m`, the closure error fell to `<= 1.2e-10 m`. The remaining 1.2 cm difference from the Dupuit analytical solution is spatial-discretization error, not closure error. `Basis: source + execution`
- **The IMS `COMPLEXITY` presets loosen the head-closure tolerance as the declared problem difficulty rises.** SIMPLE sets `dvclose = 1e-3`, 25 outer iterations and no under-relaxation. MODERATE sets `1e-2`, 50 iterations and delta-bar-delta under-relaxation. COMPLEX sets `1e-1`, 100 iterations, delta-bar-delta and backtracking (`NumericalSolution.f90:2618-2666`). `Basis: source`
- **MODFLOW 6 transport advection schemes trade overshoot against numerical dispersion, and implicit time stepping adds its own dispersion.** The probe was a 1-D Ogata–Banks problem at grid Péclet number 10 with a daily time step. `CENTRAL` overshot to `C/C0 = 1.0353`. `UPSTREAM` stretched the 10–90 % breakthrough rise from 41 d (analytical) to 106 d. `TVD` and `UTVD` gave 59 d with no overshoot beyond `1e-12`. Even at grid Péclet number 2.5, every scheme gave 57–73 d. The residual is time-discretization dispersion: `v^2*dt/2 = 0.0201 m^2/d` equals the physical `D = 0.0200 m^2/d`. Cutting `dt` tenfold gave 42.5 d against 40.4 d. `Basis: execution + derived`
- **Test-suite classes differ by code.** The MODFLOW 6 `autotest/` directory has 479 `test_*.py` files. Results are compared against reference executables (`mf6_regression`, `mf2005`, `mfnwt`, `mflgr`, `mfusg`, `libmf6`) and against per-test `check` functions. Amanzi `test_suites/` separates 18 analytic-solution verification problems from code-to-code benchmarks against PFLOTRAN, CrunchFlow and TOUGHREACT. ATS (`amanzi/ats-regression-tests@5093ad458f1a8629ae838deb0515874107c9d5f7`) has 121 gold-file regression tests with a default tolerance of `1.0e-5 relative`. Amanzi's flow PK prints reservoir water mass and cumulative influx, but its "water balance error" line is commented out (`src/pks/flow/Flow_VandV.cc:226-230`). `Basis: source`
- **The validation critique concerns the meaning of terms, and regulation answered it with probabilistic compliance.** Konikow and Bredehoeft (1992) argue that groundwater models "cannot be proven or validated, but only tested and invalidated". Oreskes et al. (1994) argue that verification and validation of models of open natural systems "is impossible" and that confirmation "is inherently partial". Bredehoeft (2005) reports that conceptual-model "surprises" occur in "20–30% of model analyses". The WIPP regulation (40 CFR 191.13(b)) explicitly does not require "complete assurance". It asks instead for a "reasonable expectation", demonstrated by a distribution of complementary cumulative distribution functions (CCDFs) whose size and confidence are fixed numerically by 40 CFR 194.34(d)–(f). `Basis: documentation + normative`
- **The 1996 WIPP PA rests on three entities.** EN1 is a probability space for stochastic futures: drilling intrusions are Poisson in time and space, and potash mining occurs at rate `1e-4 /yr`. EN2 is a model chain: `BRAGFLO`, `CUTTINGS_S`, `BRAGFLO_DBR`, `NUTS`/`PANEL`, `SECOFL2D` and `SECOTP2D`. EN3 is a probability space for `nV = 57` subjectively uncertain parameters. Each CCDF is a Monte Carlo average over `nS = 10,000` sampled futures. Three replicated Latin hypercube samples, labelled R1–R3, propagate subjective uncertainty. Solving `1 - 0.99^n >= 0.95` gives `n >= 299` for simple random sampling, the bound behind 194.34(d). `Basis: documentation + normative + derived`

## Applicability

Subjects and their relation:

- **MODFLOW 6.** Source inspection covered `MODFLOW-ORG/modflow6@6565dc81cada70781208a1a1659565597046c171`, which reports itself as `mf6: 6.9.0.dev0+6565dc8`. That same tree was built from source and executed. The build used meson 1.12.1, ninja 1.13.2 and gfortran 15.2.0, with `--buildtype=release -Dunit_tests=disabled` and no PETSc or NetCDF, so the build is serial. Every execution finding applies to this serial build and to the stated input decks only.
- **FloPy.** Only source was inspected: `modflowpy/flopy@996687f33cd0e2880e83c4cfd3957870256be352` (`3.13.0.dev0`). FloPy was **not executed**: the host had no `pandas`, which `flopy/utils/mflistfile.py` imports at module level (line 14). The probes wrote native MF6 input files and read binary output directly instead.
- **Amanzi and ATS.** Source and test layout were inspected at `amanzi/amanzi@e38fee614cbf0829b51405020a24011ba2b75d1e`, `amanzi/ats@2f7afaf04b67a93b7c75c9f32b1463c82f90b04c` and the ATS regression-test submodule `amanzi/ats-regression-tests@5093ad458f1a8629ae838deb0515874107c9d5f7`, which is the gitlink recorded in the ATS tree. Neither code was built or run.
- **PFLOTRAN.** Represented only by Hammond, Lichtner and Mills (2014), whose bibliographic metadata was verified. No source revision was examined. The only GitHub copy found, `petsc/pflotran`, is a mirror last pushed in 2017 and was not used.
- **Literature and regulation.** Konikow–Bredehoeft 1992, Oreskes et al. 1994 and Bredehoeft 2005 are cited from their abstracts. The 1996 WIPP PA structure comes from the Sandia preprint of Helton et al. (2000), *Conceptual Structure of the 1996 Performance Assessment for the Waste Isolation Pilot Plant*, and from Sandia conference paper SAND98-0983C. 40 CFR 194 text was read from the eCFR versioner API (2026-11-01 point-in-time XML). For 194.34, the text matches the quotation in the Helton et al. preprint. For other sections, the 1996 promulgation text was **not** compared with the current text.

The report covers a comparison: what each code's machinery checks, against what the validation literature says such checks can establish, and how one regulatory performance assessment turned that limit into numeric acceptance criteria. Execution host for all measurements: Intel Xeon @ 2.60 GHz, 96 vCPUs, 236 GB RAM, Linux 7.1. The host was shared, with load average 150–200 during runs, so wall-clock figures carry interference noise.

## Findings

### 1. MODFLOW 6 groundwater-flow discretization and nonlinear control

**Conductance.** In the default configuration, horizontal inter-cell conductance is the harmonic mean of the two cells' transmissivities (`src/Model/ModelUtilities/GwfConductanceUtils.f90:262-264`):

```fortran
case (CCOND_HMEAN)
  if (t1 * t2 > DZERO) then
    condmean = width * t1 * t2 / (t1 * cl2 + t2 * cl1)
```

Here `t1 = k1*thick1` and `t2 = k2*thick2`, and `cl1`/`cl2` are centre-to-face distances. Alternatives selectable through the NPF `ALTERNATIVE_CELL_AVERAGING` option are `LOGARITHMIC`, `AMT-LMK` and `AMT-HMK` (`gwf-npf.f90:1602`). When the Newton formulation is active and cells are convertible, conductance is the upstream wetted fraction times saturated conductance (`GwfConductanceUtils.f90:90-109`): `if (hn > hm) sat_up = satn else sat_up = satm; condnm = sat_up * condsat`. This first-order upstream weighting of saturated thickness is the source of the spatial error measured in §1.2. `Basis: source`

**Outer-iteration control.** Convergence is a pure head-change test (`NumericalSolution.f90:3179`, `if (abs(max_dvc) <= this%dvclose)`); the budget does not enter it. Package-level convergence (`sln_package_convergence`) and `OUTER_RCLOSEBND` exist but were not exercised. The `COMPLEXITY` presets (`sln_setouter`, lines 2618–2666; linear presets in `ImsLinearSettings.f90:94-126`):

| Preset | `dvclose` (outer) | `mxiter` | Under-relaxation | Backtracking | Linear method / `iter1` / inner `dvclose` / `rclose` |
|---|---|---|---|---|---|
| SIMPLE | `1e-3` | 25 | none (`nonmeth=0`) | off | method 1 (CG) / 50 / `1e-3` / `1e-1` |
| MODERATE | `1e-2` | 50 | DBD (`nonmeth=3`, theta 0.9, kappa 1e-4) | off | method 2 (BiCGSTAB) / 100 / `1e-2` / `1e-1`, relax 0.97 |
| COMPLEX | `1e-1` | 100 | DBD (theta 0.8, kappa 1e-4) | 20 steps, `btol 1.05`, `breduc 0.1`, `res_lim 0.002` | method 2 / 500 / `1e-1` / `1e-1`, ILUT level 5, droptol `1e-4` |

`Basis: source`

**Budget.** `Budget.f90:262-269` computes `pdiffr = hund * diffr / avgrat` with `avgrat = (totrin + totrot) / two`, and line 300 formats it `F15.2`. FloPy's list-file reader takes the printed text, so the two-decimal rounding carries through. It keys the line `PERCENT DISCREPANCY` (`flopy/utils/mflistfile.py:811`), and `compare_list_budget` defaults to `max_cumpd = 0.01` and `max_incpd = 0.01` percent (`flopy/utils/compare.py:180-185`). A discrepancy below 0.005 % therefore prints as `0.00` and cannot be resolved from the LST file. `Basis: source`

#### 1.2 Measured: closure tolerance vs head error vs mass balance

Input deck: 1 layer, 1 row and 100 columns with `DELR = 10 m` and `K = 10 m/d`. The bottom is at 0 m, the top at 50 m and `ICELLTYPE = 1`. Recharge is `1e-3 m/d` (RCH with `READASARRAYS`), and CHD fixes `h = 20 m` in column 1 and `10 m` in column 100. Other settings: `NEWTON`, `UNDER_RELAXATION none`, BiCGSTAB, `INNER_RCLOSE 1e-6`. The analytical solution is Dupuit–Forchheimer between the two CHD cell centres: `h^2 = h1^2 + (h2^2-h1^2) x/L + (R/K) x (L-x)`, `L = 990 m`. The reference run used `OUTER_DVCLOSE = 1e-12` and took 9 outer and 19 inner iterations. The table reproduces the probe's printed output.

| `OUTER_DVCLOSE` (m) | outer / inner iters | LST % discrepancy | rate in / out (m³/d) | recomputed % | max abs(h − h_ref) (m) | max abs(h − h_Dupuit) (m) |
|---|---|---|---|---|---|---|
| 1 | 6 / 12 | −0.76 | 2.0064 / 2.0218 | −0.7646 | 2.567e-02 | 1.391e-02 |
| 0.1 | 7 / 14 | −0.01 | 2.011 / 2.0111 | −0.0050 | 3.477e-05 | 1.204e-02 |
| 0.01 | 8 / 15 | −0.0 | 2.011 / 2.011 | 0.0000 | 1.225e-10 | 1.207e-02 |
| 1e-4 | 8 / 16 | −0.0 | 2.011 / 2.011 | 0.0000 | 0 | 1.207e-02 |
| 1e-10 | 9 / 18 | −0.0 | 2.011 / 2.011 | 0.0000 | 0 | 1.207e-02 |

`Basis: execution (real MODFLOW 6 binary at the pinned revision)`. Derived reading:

- Closure error and budget error vanish together once `dvclose` reaches 0.01 m.
- The 1.207 cm floor against Dupuit does not change with `dvclose`, so it is discretization error.
- At COMPLEX's preset `dvclose = 0.1`, this problem had a 3.5e-5 m closure error and a −0.005 % discrepancy.

Nothing here establishes how `dvclose = 0.1` behaves on a strongly nonlinear field model.

### 2. MODFLOW 6 transport advection schemes

`tsp-adv.f90:132-146` selects `UPSTREAM` (default), `CENTRAL`, `TVD` or `UTVD`. TVD is implemented as a deferred correction: the face value is first-order upstream in the matrix, and a van Leer-limited correction goes on the right-hand side using the current iterate (`InterpolationScheme/TVDScheme.f90:115-120`):

```fortran
smooth = (this%phi(iup) - this%phi(i2up)) / elup2up * &
         elupdn / (this%phi(idn) - this%phi(iup))
...
alimiter = DTWO * smooth / (DONE + smooth)
phi_face%rhs = -DHALF * alimiter * (this%phi(idn) - this%phi(iup))
```

The second-upstream node `i2up` is chosen as the neighbour with the largest inflow into `iup`. The high-order term is therefore only as converged as the outer iteration. `Basis: source`

**Measured (probe B).** 1-D confined flow: 200 m long, `K = 1 m/d`, CHD of 10 m and 0 m, porosity 0.25, so `v = 0.2010 m/d`. Dispersion: `ALH = 0.1 m`, `DIFFC = 0`, `XT3D_OFF`. A CNC cell with `C = 1` sits in column 1. The run used 400 one-day steps; GWF and GWT were coupled by a `GWF6-GWT6` exchange, with BiCGSTAB at `1e-9` tolerances. The observation point is 50 m downstream, and the comparison is against Ogata–Banks with `D = ALH*v`.

| `DELR` (grid Pe) | scheme | RMSE vs analytical | t50 sim / ana (d) | t10–90 sim / ana (d) | max C/C0 | min C/C0 | GWT % disc. |
|---|---|---|---|---|---|---|---|
| 1.0 (10) | upstream | 0.0884 | 247 / 249 | 106 / 41 | 1.000000 | ≥0 | 0.0 |
| 1.0 (10) | central | 0.0330 | 251 / 249 | 59 / 41 | **1.035257** | ≥0 | 0.0 |
| 1.0 (10) | tvd | 0.0354 | 246 / 249 | 59 / 41 | 1.000000 | −1.3e-12 | 0.0 |
| 1.0 (10) | utvd | 0.0354 | 246 / 249 | 59 / 41 | 1.000000 | −2.0e-12 | 0.0 |
| 0.25 (2.5) | upstream | 0.0500 | 250 / 250 | 73 / 41 | 1.000000 | ≥0 | −0.0 |
| 0.25 (2.5) | central | 0.0283 | 250 / 250 | 58 / 41 | 1.000029 | ≥0 | −0.0 |
| 0.25 (2.5) | tvd | 0.0281 | 250 / 250 | 57 / 41 | 1.000000 | ≥0 | −0.0 |

Time-step refinement at `DELR = 0.25` with TVD:

- 400 steps (Courant 0.80): t10–90 = 57.0 d against 41.0 d.
- 4000 steps (Courant 0.08): 42.5 d against 40.4 d, RMSE 0.0052.

`Basis: execution`

Derived: backward-Euler time stepping adds an effective dispersion of about `v^2*dt/2`, which equals 0.0201 m²/d for `dt = 1 d` and matches the physical `D`. The rise time scales as `sqrt(D_eff)`, so `41*sqrt(2) = 58 d`, consistent with the 57–59 d measured for every non-upstream scheme. Upstream weighting adds a grid-induced `v*DELR/2` on top. The test does not separate the time-weighting option.

### 3. Test-suite taxonomy

| Suite (revision) | Analytical / manufactured | Code-to-code benchmark | Regression against prior output | Pass criterion examined |
|---|---|---|---|---|
| MODFLOW 6 `autotest/` (6565dc8) | Yes, inside individual `check` functions. 13 of the 479 `test_*.py` files mention "analytical" (grep count). | Yes: `framework.py:203-207` lists comparison programs `mf6, mf6_regression, libmf6, mf2005, mfnwt, mflgr`, and `compare.py` adds `mfusg`. | `mf6_regression` compares against a previous MF6 build; 11 files use snapshots (`__snapshots__/`, 12 entries). | Head and budget comparison with tolerances adjusted to IMS `dvclose`/`rclose` (`framework.py:444-453`). 424 files pass a `check=` callable. |
| MODFLOW 6 Fortran unit tests | 33 `Test*.f90` files in `autotest/` | – | – | not executed (`-Dunit_tests=disabled`) |
| Amanzi `test_suites/` (e38fee6) | 18 verification directories, e.g. `theis_isotropic_1d`, `hantush_anisotropic_2d`, `butler_strip_2d`, `infiltration_dry_sand_1d`, `unconfined_seepage_1d`, `dispersion_45_point_2d`, `dual_porosity_1d` | `benchmarking/chemistry/*` against `pflotran`, `crunchflow`, `toughreact`; `coupled_flow_transport/single_fracture` | – | not examined |
| ATS regression (5093ad4) | `00_analytic` (4 tests, exponential decay) | – | 121 tests in 13 categories, `00_analytic` through `12_engineered_water`, compared against gold files | `default = 1.0e-5 relative` (`00_analytic/analytic.cfg:8`) |

Per-category ATS counts: 00 analytic 4, 01 Richards steady-state 3, 02 Richards 15, 03 surface water 7, 04 integrated hydrology 9, 05 surface balance 5, 06 transport 22, 07 reactive transport 18, 08 energy 13, 09 multiscale 13, 10 seawater intrusion 4, 11 sediment transport 2, 12 engineered water 6. `Basis: source (counts by grep over section headers in each *.cfg)`

**Amanzi water-balance reporting.** `Flow_PK::VV_ReportWaterBalance` (`src/pks/flow/Flow_VandV.cc:195-231`) sums `ws*rho*phi*V` over cells and accumulates boundary influx, then prints `"reservoir water mass=" ... ", total influx="` (line 223). The balance-error computation itself is commented out (lines 226–230):

```cpp
  // if (report_water_balance) {
  //  if (mass_initial == 0.0) mass_initial = mass_amanzi;
  //  double mass_lost = mass_amanzi - mass_bc - mass_initial;
  //  *vo_->os() << " T=" << S->time() << " water balance error=" << mass_lost << " [kg]" << std::endl;
  // }
```

The function is called only from `Richards_PK.cc:1026-1028` and only at `VERB_HIGH`. Consequence (derived): in this revision, Richards mass conservation must be checked by post-processing the printed mass and influx; Amanzi does not compute or test a balance error. `Basis: source`

**ATS surface–subsurface coupling.** `src/pks/mpc/mpc_coupled_water.hh` documents the coupled-water MPC. It enforces flux continuity and pressure continuity, `p|_Γ = p_s`, by discretely eliminating the surface unknowns into the subsurface operator. This requires an `mfd:*` face-unknown subsurface discretization. The header's citation text reads "Coon et al WRR 2020" (line 36) but links DOI `10.1016/j.advwatres.2020.103701`, which Crossref resolves to *Advances in Water Resources* 144:103701. This is a documentation labelling inconsistency, not a code defect. `Basis: source + documentation`

### 4. Verification, validation and confirmation: the arguments

| Source | Core claim (quoted from abstract) | Distinction it draws |
|---|---|---|
| Konikow & Bredehoeft 1992, *Adv. Water Resour.* 15(1):75–83 | "Ground-water models are embodiments of scientific hypotheses. As such, the models cannot be proven or validated, but only tested and invalidated." Errors "arise from conceptual deficiencies, numerical errors, and inadequate parameter estimation"; "calibration produces a nonunique solution"; "validation and verification are misleading and their use ... should be abandoned in favor of more meaningful model-assessment descriptors." | Code testing (benchmarking) vs calibration (history matching) vs prediction; predictive accuracy is limited even after a good calibration. |
| Oreskes, Shrader-Frechette & Belitz 1994, *Science* 263:641–646 | "Verification and validation of numerical models of natural systems is impossible ... because natural systems are never closed and because model results are always nonunique. Models can be confirmed ... but confirmation is inherently partial" | Verification = establishing truth (possible only for closed systems); validation = establishing legitimacy; confirmation = agreement with observation (partial, affirming the consequent). |
| Bredehoeft 2005, *Hydrogeol. J.* 13:37–46 | "Surprise is defined as new data that renders the prevailing conceptual model invalid"; "surprises occur in 20–30% of model analyses"; "Conceptual model uncertainty is exacerbated in making long-term predictions." | Conceptual-model uncertainty dominates and is not reduced by calibration. |

`Basis: documentation`. The K&B text is the USGS publication-page abstract, the Bredehoeft text the publisher-page abstract, and the Oreskes text the abstract as reproduced by an indexed copy. The full texts were not examined.

Published responses whose bibliographic identity was verified (Crossref). Their **content was not examined**, so nothing is claimed about their arguments:

- de Marsily, Combes and Goblet (1992), comment, *Adv. Water Resour.* 15(6):367–369, DOI 10.1016/0309-1708(92)90003-K, and the authors' reply, 371–372, DOI 10.1016/0309-1708(92)90004-L.
- Bredehoeft and Konikow (1993), "Ground-water models: validate or invalidate", *Groundwater* 31(2):178–179.
- Tsang (1991), "The modeling process and model validation", *Groundwater* 29:825–831, with Konikow's discussion, 30:622–623.
- Hassanizadeh and Carrera (1992), editorial, *Adv. Water Resour.* 15(1):1–3.
- Refsgaard and Henriksen (2004), "Modelling guidelines—terminology and guiding principles", *Adv. Water Resour.* 27:71–82.
- Rykiel (1996), "Testing ecological models: the meaning of validation", *Ecol. Model.* 90:229–244.

Mapping onto the code machinery (derived):

- MODFLOW 6 analytical `check` functions and Amanzi's verification suite exercise **code verification** in K&B's "benchmarking" sense: closed mathematical problems.
- `mf6_regression`, mf2005 comparisons and ATS gold files are **consistency or regression** checks. They detect change, not correctness.
- None of the examined suites performs history matching or post-audit prediction against field data. That activity sits outside the code repositories, which is exactly where both critiques place the unresolvable part.

### 5. The 1996 WIPP performance-assessment structure

**Regulation (normative).** 40 CFR 191.13(a), as quoted in Helton et al.: cumulative releases over 10,000 years shall "(1) Have a likelihood of less than one chance in 10 of exceeding the quantities calculated according to Table 1 ... and (2) Have a likelihood of less than one chance in 1,000 of exceeding ten times the quantities". 191.13(b): "Performance assessments need not provide complete assurance ... what is required is a reasonable expectation". 40 CFR 194.34 (eCFR 2026-11-01, identical to the Helton et al. quotation):

- (a) results assembled into CCDFs;
- (b) probability distributions for uncertain parameters;
- (c) "Computational techniques, which draw random samples from across the entire range of the probability distributions";
- (d) "the maximum CCDF generated exceeds the 99th percentile of the population of CCDFs with at least a 0.95 probability" at releases 1 and 10;
- (e) display the full range;
- (f) "at least a 95 percent level of statistical confidence that the mean of the population of CCDFs meets the containment requirements".

194.32(b): mining "with a one in 100 probability in each century". 194.33(b)(2)–(3): drilling "at random intervals in time and space", with the rate taken from the "past 100 years" of Delaware Basin drilling. `Basis: normative`

**Software-quality and peer-review controls (normative, as the regulation states them).**

- 194.22(a)(1): QA "that implements the requirements of ASME NQA-1-1989 edition, ASME NQA-2a-1990 addenda, part 2.7 ... and ASME NQA-3-1989". (a)(2)(iv) explicitly covers "Computations, computer codes, models and methods".
- 194.23(a)(3)(iii)–(iv): documentation that "Numerical models provide numerical schemes which enable the mathematical models to obtain stable solutions" and that "computer codes are free of coding errors and produce stable solutions".
- 194.23(a)(2): "plausible, alternative conceptual model(s) seriously considered but not used".
- 194.23(b): code documentation per NQA-2a part 2.7.
- 194.27: peer review of conceptual models, waste characterization and engineered barriers "compatible with NUREG-1297".
- 194.22(b): pre-QA data qualified by peer review, corroborating data, confirmatory testing or equivalent QA.

Which control was applied to which code in 1996, and with what outcome, was **not examined** (see Boundaries).

**Structure (documentation: Helton et al. 2000 preprint, Sections 3–5).**

- **EN1, stochastic.** Futures are vectors `x_st = [t1, l1, e1, b1, p1, a1, ..., tn, ln, en, bn, pn, an, t_min]`: drilling time, location, excavated-area penetration, Castile brine-pocket hit, plugging pattern (continuous, two-plug or three-plug), waste type hit, and mining time. Drilling is Poisson in time and space, and mining is Poisson with `λm = 1e-4 /yr`. The per-epistemic-sample CCDF is `prob(Rel > R) ≈ Σ_i δ_R[f(x_st,i)]/nS` with `nS = 10,000`. The models are evaluated only for representative futures, and results for the other futures are constructed from them.
- **EN2, model chain:**

| Function | Code | Consumes |
|---|---|---|
| two-phase flow in repository/Salado | `BRAGFLO` | – |
| cuttings/cavings and spallings releases | `CUTTINGS_S` | BRAGFLO (spallings) |
| direct brine release | `BRAGFLO_DBR` | BRAGFLO + CUTTINGS_S |
| release via anhydrite marker beds; Dewey Lake; land surface; to Culebra | `NUTS` or `PANEL` | BRAGFLO |
| Culebra flow field | `SECOFL2D` | – (intrusions assumed not to perturb Culebra flow) |
| Culebra groundwater transport to accessible environment | `SECOTP2D` | SECOFL2D + NUTS/PANEL |

- **EN3, subjective.** A probability space over `nV = 57` imprecise inputs (SAND98-0983C: "the nV = 57 elements of xsu"), sampled by LHS. The mean CCDF is estimated as `Σ_k Σ_i δ_R[f(x_st,i, x_su,k)]/nS/nLHS`. Figure labels "BRAGFLO (E0, R1, R2, R3)" show three replicated samples.

**Sample-size arithmetic for 194.34(d) (derived and toy execution).** For simple random sampling from a continuous population, `P(max > q_0.99) = 1 − 0.99^n`. The smallest `n` meeting 0.95 is 299: `1 − 0.99^299 = 0.9505`, while `n = 298` gives 0.94998. A toy Monte Carlo with 20,000 trials of `n = 300` gave 0.9492. In a one-dimensional toy, a single 100-point Latin hypercube always samples the top 1 % stratum (probability 1.0000). That is a property of 1-D stratification and does **not** carry over to the 57-dimensional input-to-CCDF map. `Basis: derived + execution (toy model, not WIPP)`

### 6. Performance and resource footprint (L1–L6)

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring | Source size: MF6 `src/` Fortran | 280,763 lines in 531 files (`wc -l`) | measured |
| L1 | MF6 `autotest/test_*.py` | 161,970 lines in 479 files | measured |
| L1 | FloPy `flopy/` Python; Amanzi `src/` C++; ATS `src/` C++ | 195,310; 345,569; 99,790 lines | measured |
| L1 | person-months, LLM/agent token budgets, repair cost on change | not measured | – |
| L2 build | MF6 from-scratch release build, `ninja -j16` (536 steps) | 25.6 s wall, 133.8 s user; largest child RSS 131 MB | measured (`/usr/bin/time -v`) |
| L2 | Amanzi/ATS/PFLOTRAN build | not measured | – |
| L3 compile/setup latency | MF6 input parse and setup for the probe decks | included in L4 runtimes below; not separated | – |
| L4 execution | Probe A (100 cells, Newton, steady) | 0.011–0.025 s wall per run | measured |
| L4 | Probe B (200 cells × 400 steps, GWF+GWT) | 0.12 s (upstream/central) to 0.27 s (UTVD); 800 cells: 0.36–0.76 s; 800 cells × 4000 steps TVD: 6.0 s | measured |
| L4 | PFLOTRAN parallel scaling | Hammond et al. 2014 is the source; its figures were not read here | not examined |
| L5 certificate checking | – | not applicable (no proof or certificate artifacts in these codes) | known not to apply |
| L6 footprint | `mf6` executable; `libmf6.so` (BMI) | 18,476,752 B; 19,139,032 B (unstripped release build) | measured |
| L6 | Peak RSS of `mf6` on the probes | 9.3–14.8 MB | measured |
| L6 | WIPP 1996 PA compute cost (CPU-hours) | not measured; not found in the sources read | – |

### 7. Human comprehensibility and conceptual simplicity (C1–C2)

- **C1: legibility of convergence.** MF6's "converged" means only "max head change ≤ `dvclose`". A user who sees a converged run with `PERCENT DISCREPANCY = -0.76` must know that the two are decoupled. The two-decimal print further hides discrepancies below 0.005 %. Recomputing from `TOTAL IN` and `TOTAL OUT` (§1.2) restores four significant figures. The COMPLEXITY presets loosen `dvclose` as difficulty rises, which inverts a natural reading of "COMPLEX = stricter". `Basis: derived`
- **C1: WIPP.** The EN1/EN2/EN3 separation turns one opaque number into two orthogonal questions: how likely each future is, and how uncertain each parameter is. A reviewer can audit them separately. The cost is a nested Monte Carlo (10,000 futures × LHS replicates) whose CCDF-of-CCDFs output needs statistical literacy to read. `Basis: derived`
- **C2: minimal abstraction.** Every examined suite uses one mechanism, "compare outputs to a reference within tolerance". Only the reference changes: an analytical solution, another code, a previous version, a gold file or field data. Making the reference type an explicit, required test attribute would make K&B's benchmarking versus history-matching distinction machine-visible. In the examined trees it is implicit in directory names (Amanzi) or check-function bodies (MF6). This is a hypothesis about a design improvement, not an upstream property. `Basis: derived`

### 8. Validation coverage of the examined machinery (V1–V4)

| Class | Present in examined sources | Absent / not examined |
|---|---|---|
| V1 specification adequacy / non-vacuity | MF6 analytical checks; Amanzi verification problems with analytic solutions; probes A/B here (analytical Dupuit and Ogata–Banks) | mutation testing of test suites; whether checks would fail under seeded discretization bugs: not examined |
| V2 lowering / differential | MF6 cross-code comparisons (mf2005, mfnwt, mfusg, mflgr) and `mf6_regression`; Amanzi benchmarks against PFLOTRAN/CrunchFlow/TOUGHREACT | compiler-differential (gfortran vs ifx) and fuzzing of input parsers: not examined |
| V3 concurrency / crash / physical leakage | MF6 has 36 `test_par*` parallel tests (grep count) | not executed (serial build); crash/restart fault injection: not examined |
| V4 plant falsification / field replay | none inside the code repositories; WIPP regulation relies on probabilistic PA, QA (NQA-1/2a/3), peer review (NUREG-1297) and alternative-conceptual-model documentation (194.23(a)(2)) | post-audit studies of MF6 or WIPP predictions against later observations: not examined |

## Boundaries

- **Not examined:**
  - FloPy execution (no `pandas` on the host), so its budget utilities were read but not run. `ZoneBudget6` and `postprocessing.get_specific_discharge` were not exercised.
  - Amanzi and ATS builds and runs; ATS regression pass/fail state at the pinned revision.
  - PFLOTRAN source and any PFLOTRAN performance numbers. The Hammond et al. 2014 content was not read.
  - The MF6 parallel (PETSc/MPI) build and the 36 `test_par*` tests.
  - MF6 Fortran unit tests.
  - XT3D, BUY/VSC, CSUB, UZF and other packages.
  - Under-relaxation and backtracking behaviour on a hard nonlinear problem. Probe A converged without them.
- **Unknown:** whether the 1.207 cm discretization error in probe A would shrink at the expected first-order rate under grid refinement. Only one grid was run for probe A.
- **WIPP:**
  - **not examined**: the per-replicate LHS size. Secondary summaries report 100 per replicate (300 in total), but this was not confirmed in a primary text read here. The arithmetic statement `300 ≥ 299` is therefore conditional.
  - **not examined**: which QA and peer-review controls were applied to which of `BRAGFLO`, `CUTTINGS_S`, `BRAGFLO_DBR`, `NUTS`, `PANEL`, `SECOFL2D` and `SECOTP2D`, and EPA's 1998 certification findings on them. Only the regulatory requirements were read.
  - **not examined**: the screening of features, events and processes (FEPs), beyond 194.32/194.33.
  - **known not to apply**: the 2026 eCFR text was not verified to equal the 1996 promulgation, except for 194.34.
- **Unsupported stronger conclusions:**
  - "MF6 has a mass-balance bug": no. The decoupling of convergence from budget is documented behaviour and was shown only on a mild problem.
  - "TVD eliminates numerical dispersion": no. Time-step dispersion dominated at Courant 0.8.
  - "Amanzi does not conserve mass": no. Only the *reporting* of the error is disabled. Conservation of the discretization was not tested.
- **Responses literature:** only metadata was verified for the de Marsily et al. comment and reply, Bredehoeft & Konikow 1993, Tsang 1991, Hassanizadeh & Carrera 1992, Refsgaard & Henriksen 2004 and Rykiel 1996. Their arguments are not characterized here.

## Evidence

Observation dates: all source, execution and literature evidence was gathered on 2026-11-20 (UTC).

- **Source** (path:lines at the pinned revisions):
  - modflow6:
    - `src/Solution/NumericalSolution.f90:2618-2666` (`sln_setouter`), `3173-3183` (`sln_has_converged`);
    - `src/Solution/LinearMethods/ImsLinearSettings.f90:94-126`;
    - `src/Model/ModelUtilities/GwfConductanceUtils.f90:90-109,236-294`;
    - `src/Model/GroundWaterFlow/gwf-npf.f90:1602`;
    - `src/Utilities/Budget.f90:262-269,300-301`;
    - `src/Model/TransportModel/tsp-adv.f90:132-146`;
    - `src/Model/TransportModel/InterpolationScheme/TVDScheme.f90:60-121`;
    - `autotest/framework.py:203-207,415-453`; `autotest/compare.py:11-17`.
  - flopy: `flopy/utils/mflistfile.py:14,811`; `flopy/utils/compare.py:180-225`.
  - amanzi:
    - `src/pks/flow/Flow_VandV.cc:195-231`;
    - `src/pks/flow/Richards_PK.cc:1026-1028`;
    - `test_suites/README`;
    - `test_suites/verification/**` and `test_suites/benchmarking/**` directory listing.
  - ats: `src/pks/mpc/mpc_coupled_water.hh` (doc block, line 36).
  - ats-regression-tests: `*/**.cfg` section headers and `00_analytic/analytic.cfg:8`.
- **Execution:**
  - Build: `meson setup <build> --buildtype=release -Dunit_tests=disabled && /usr/bin/time -v ninja -j 16`.
  - Probe scripts and full outputs are preserved in `support/`:
    - `mf6_probe.py` writes native MF6 decks for probes A and B and reads binary heads and concentrations; run as `python3 mf6_probe.py <mf6> <workdir>`;
    - `mf6_probe_dt.py` (time-step refinement);
    - `ccdf_sample_size_toy.py`;
    - `mf6_probe_out.txt`, `mf6_probe_dt_out.txt`, `ccdf_sample_size_toy_out.txt`.
- **Normative and documentation:**
  - 40 CFR Part 194, eCFR versioner API, point-in-time 2026-11-01, sections 194.22, 194.23, 194.27, 194.32, 194.33 and 194.34.
  - 40 CFR 191.13 as quoted in the Helton et al. preprint (OSTI 755471), which also carries the EN1–EN3 structure, model chain, `nS = 10,000` and `λm = 1e-4/yr`.
  - SAND98-0983C (OSTI 656529) for `nV = 57` and the R1–R3 labels.
  - USGS publication page for the K&B abstract; Springer page for the Bredehoeft 2005 abstract.
  - All DOIs in §4–§5 resolved through Crossref on the observation date:
    - Helton et al. 2000: 10.1016/S0951-8320(00)00030-2;
    - companion papers: 10.1016/S0951-8320(00)00022-3, 00031-4, 00032-6, 00019-3;
    - SAND98-0365: 10.2172/1024;
    - Langevin et al. 2017 (MF6 GWF): 10.3133/tm6A55;
    - Langevin et al. 2022 (MF6 GWT): 10.3133/tm6A61;
    - Hughes et al. 2017 (MF6 framework): 10.3133/tm6A57;
    - Provost et al. 2017 (XT3D): 10.3133/tm6A56;
    - Bakker et al. 2016: 10.1111/gwat.12413;
    - Hammond et al. 2014: 10.1002/2012WR013483;
    - Coon et al. 2016: 10.1016/j.envsoft.2015.12.017;
    - Coon et al. 2020: 10.1016/j.advwatres.2020.103701.

## Revalidation

1. **Convergence and budget semantics.** Diff `sln_has_converged`, `sln_setouter` and `Budget.f90`'s percent-discrepancy block (`git diff 6565dc8..<new> -- src/Solution/NumericalSolution.f90 src/Utilities/Budget.f90`). If unchanged, the semantic findings hold. Rerun `support/mf6_probe.py` against the new `mf6` (under 10 s) to refresh the tables. A change in the 1.207 cm Dupuit floor means the NPF/Newton discretization changed.
2. **Transport schemes.** Rerun probe B. A change in the central-scheme maximum, 1.035257, or in the upstream rise time, 106 d, indicates a change in advection discretization.
3. **Amanzi water balance.** `grep -n "water balance error" src/pks/flow/Flow_VandV.cc`. If the line is no longer commented out, update §3.
4. **ATS tests.** Read the `testing/ats-regression-tests` gitlink in the new ATS tree and recount the section headers.
5. **WIPP.** The regulatory quotes are stable text. Re-read 194.34 through the eCFR API. For the per-replicate LHS size, consult SAND98-0365 (DOI 10.2172/1024) or Helton et al. 2000 (RESS 69) directly. That primary read was not completed here.
