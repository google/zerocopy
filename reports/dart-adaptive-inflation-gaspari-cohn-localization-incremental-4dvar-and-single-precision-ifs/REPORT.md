# DART adaptive inflation and Gaspari–Cohn localization, OOPS incremental 4D-Var, and precision/reproducibility acceptance in ecTrans and WRF

## Summary

- **DART** assimilates observations one at a time. Each observation gets an ensemble adjustment Kalman filter (EAKF) increment: the observation ensemble is shifted to the posterior mean and contracted by $\sqrt{R/(\sigma_p^2+R)}$. That increment is then regressed onto each state variable and scaled by a Gaspari–Cohn factor. By default `cutoff = 0.2` is a *half-width*, so the factor reaches zero at `2*cutoff`, and inflation is off.
- **DART adaptive inflation** is updated per variable inside the same loop. Flavor 2 (Anderson 2009) weights the update by $\gamma=$ localization × |corr|; flavor 5 (El Gharamti 2018) uses an inverse-gamma prior. The prior `inf_lower_bound` is `0.0` in the `filter_mod.nml` template but `1.0` in the code and `.rst`.
- **OOPS 4D-Var** runs an explicit outer loop: linearize, minimize, add the increment, reset. The Derber–Rosati minimizers precondition with $B$ and never apply $B^{-1}$, and `ninner` and `gradient norm reduction` are mandatory. Tangent-linear (TL) and adjoint (AD) correctness is enforced by interface tests with YAML tolerances; the online checks only write to the log.
- **Acceptance standards** differ by code:
  - Bitwise equality: ecTrans optional checksum tests (per-compiler references, invariant across MPI, OpenMP and NPROMA layouts) and WRF `diffwrf` (serial vs OpenMP vs MPI).
  - Numeric tolerance: the ecTrans round trip, bounded by `ncheck × epsilon`, with Legendre tables kept in double precision.
  - Statistical: the literature (Váňa et al. 2017; Hong et al. 2013; Baker et al. 2015).
- **Toy probes** (Python, not the real codes):
  - The DART Gaspari–Cohn function is $C^1$, and its localization matrix becomes indefinite once `2*cutoff` exceeds half the periodic domain.
  - A Lorenz-96 EAKF was stable in every run only when it used both localization and inflation.
  - float32 and reordered float64 runs diverge from the float64 trajectory but have the same climate statistics.

## Applicability

| Subject | Revision (inspected 2026-11-20) | Examined surface |
|---|---|---|
| `NCAR/DART` | `df5b08d03aa44c3a6b2b561a903b00b7193611ca` | `assimilation_code/modules/assimilation/` (filter, assim_tools, adaptive_inflate, cov_cutoff, algorithm_info), `location/oned`, `types_mod.f90`, `models/lorenz_96`, `.github` CI |
| `JCSDA/oops` | `5625198ec14e3ad6ec0c77f59f9de9d210d4dcac` | `src/oops/assimilation/*`, `src/test/interface/LinearModel.h`, `src/oops/util/{TestReference.cc,FloatCompare.h}`, Lorenz-95 (L95) and quasi-geostrophic (QG) test YAML and reference outputs |
| `ecmwf-ifs/ectrans` | `e63c36a5902444284a5650325be72a34097f7362` | `CMakeLists.txt`, `cmake/`, `src/trans/cpu/`, `src/programs/ectrans-benchmark.F90`, `tests/` |
| `wrf-model/WRF` | `06d4240ae989cc3e50af412bb472df3d9048783c` | `arch/configure.defaults`, `tools/regtest.csh`, `.sane/wrf/`, `external/io_netcdf/diffwrf.F90`, `run/README.namelist`, selected `phys/`, `dyn_em/` |

The subjects are compared, not combined. DART (ensemble) and OOPS (variational) are data-assimilation frameworks. ecTrans (the spectral transforms of ECMWF's Integrated Forecasting System, IFS) and WRF are forecast-model codes, examined only for precision and reproducibility practice. The papers listed as subjects supply the reference equations; numbers quoted from papers describe the IFS configurations they ran, not this ecTrans revision.

Scope: the deterministic EAKF with state-space inflation (DART); strong-constraint 4D-Var with the `DR*` minimizers (OOPS); CPU builds and tests (ecTrans); the ARW build and regression machinery (WRF). All defaults and line numbers are revision-specific.

## Findings

### 1. DART EAKF update

Basis: source, read against Anderson 2001, Evensen 1994, and Houtekamer & Mitchell 1998.

The prior observation ensemble $h_n$ has mean $\bar h$ and variance $\sigma_p^2$ (divisor $N-1$; `assim_tools_mod.f90:947-948`). `obs_increment_eakf` (`:1113-1133`) computes:

$$\rho=\frac{R}{\sigma_p^2+R},\quad \bar h^a=\rho\Big(\bar h+\frac{\sigma_p^2y}{R}\Big),\quad \delta h_n=\sqrt{\rho}\,(h_n-\bar h)+\bar h^a-h_n$$

The code is `var_ratio = obs_var / (prior_var + obs_var)`, `new_mean = var_ratio * (prior_mean + prior_var*obs / obs_var)`, `a = sqrt(var_ratio)`, `obs_inc = a * (ens - prior_mean) + new_mean - ens` (1126-1131). The posterior variance is exactly $\rho\sigma_p^2$, and the members keep their ranks.

States are then updated by regression (`update_from_obs_inc`, 1472-1559):

$$\beta=\widehat{\mathrm{cov}}(x,h)/\sigma_p^2,\qquad x_n\leftarrow x_n+f\beta\,\delta h_n$$

The covariance is computed at line 1495, $\beta$ at 1497-1501 ($\beta=0$ if $\sigma_p^2\le0$), and the state update at 2059 (`ens = ens + final_factor * increment`).

- $f$ is `comp_cov_factor(dist, cutoff_rev)` times an optional impact-table factor (2065-2100). With groups, it is also capped by `reg_factor` (2052-2056).
- Observations not yet assimilated (line 817) receive the same regression update.
- The filter kind defaults to `EAKF` when no QCF table is given (`algorithm_info_mod.f90:501,512`).
- If $R$ and $\sigma_p^2$ are both zero, the run stops with a fatal error. $R=0$ sets every member to $y$; $\sigma_p^2=0$ gives no increment (`assim_tools_mod.f90:979-997`).
- Spread restoration is rejected at initialisation (241-245).
- `net_a` is initialised to `0.0_r8` directly below the comment "Null value of net spread change factor is 1.0" (943-944).
  - The EAKF path then overwrites it with `a = sqrt(var_ratio)`, through the `intent(out)` dummy `a` of `obs_increment_eakf` (1113-1131). Other filter kinds leave it at 0.
  - It is then passed to `update_from_obs_inc` as `net_a_in` (`intent(in)`, 1484). Neither `net_a_in` nor the local `net_a` declared at 1489 is referenced in that routine's body, so the inconsistent null value does not affect the regression update.
  - Basis: source.

**Reproducibility.**

- The stochastic EnKF and kernel filters start their random streams from `my_task_id() + 1` (1338). The comment says these "will reproduce exactly for multiple runs with the same task count, but WILL NOT reproduce for a different number of MPI tasks" (1330-1336, again at 1435-1436).
- Non-deterministic inflation carries the same caveat (`adaptive_inflate_mod.f90:248`).
- `perturbation_method='model'` falls back to "a perturbation that is bitwise across any number of tasks" (`filter_mod.f90:209-210`).
- No such claim exists for the EAKF. `sum_across_tasks_real` uses `MPI_Allreduce(... MPI_SUM ...)` (`mpi_utilities_mod.f90:1348`), whose summation order is not fixed by MPI, so EAKF task-count invariance is not established.

### 2. Gaspari–Cohn localization

Basis: source, read against Gaspari & Cohn 1999 eq. 4.10; execution of a toy transcription.

With $r=|z|/c$, `comp_cov_factor` (`cov_cutoff_mod.f90:122-146`; `select_localization = 1` at line 27) evaluates the following in Horner form:

$$G(r)=\begin{cases}-\tfrac14r^5+\tfrac12r^4+\tfrac58r^3-\tfrac53r^2+1 & r\le1\\ \tfrac1{12}r^5-\tfrac12r^4+\tfrac58r^3+\tfrac53r^2-5r+4-\tfrac{2}{3r} & 1<r<2\\ 0 & r\ge2\end{cases}$$

- The expanded forms are kept as comments (132-135, 141-144). A boxcar (shape 2) and a ramp (shape 3) are at 148-164.
- The `.rst` calls `cutoff` "the value, in radians, of the half-width" (`assim_tools_mod.rst:35-39`).
- The periodic 1-D distance is the shorter arc on a unit circle (`location/oned/location_mod.f90:91-92`).

| `assim_tools_nml` | Default (line) | Effect |
|---|---|---|
| `cutoff` | `0.2` (138) | Half-width; zero beyond `2*cutoff` |
| `special_localization_obs_types/_cutoffs` | empty (225-226) | Per-type half-width; disables `close_obs_caching` (290-293) |
| `adaptive_localization_threshold` / `adaptive_cutoff_floor` | `-1` / `0.0` (142-143) | If > 0, shrink the half-width (square-root area scaling, floored) until the nearby-observation count meets the threshold (2143-2150, 2269-2281) |

**Probe 1** (`support/gc_probe.py`; Basis: execution of a Python transcription, not DART):

- The Horner and expanded forms differ by at most 3.997e-15; evaluating in float32 instead of float64 changes the value by at most 1.114e-06.
- At $r=1$ the value is 5/24 from both sides, and the slope is −3.54167 vs −3.54166 per unit distance (for $c=0.2$). At $r=2$ the value is 0.
- Minimum eigenvalue of the localization matrix on a 40-point periodic grid with DART's 1-D distance:

| `c` | 0.05 | 0.10 | 0.20 (default) | 0.25 | 0.30 |
|---|---|---|---|---|---|
| min eig | +1.389e-02 | +2.183e-03 | +2.958e-04 | +1.531e-04 | **−2.320e-03** |

When `2c` > 0.5, the capped arc distance folds the support and the matrix becomes indefinite. DART never forms this matrix (it scales individual regressions); the effect on DART output was not examined.

### 3. DART inflation

Basis: source, read against Anderson 2007 and 2009, El Gharamti 2018, and Whitaker & Hamill 2012.

**Flavors** (`adaptive_inflate_mod.f90:61-66`):

- 0: none.
- 1: observation-space inflation; deprecated (58) and rejected (`filter_mod.rst:491`).
- 2: spatially varying.
- 3: spatially constant.
- 4: RTPS (relaxation to prior spread).
- 5: enhanced; stored as flavor 2 with a sub-flavor (284-287).

Validation rejects a flavor outside 0–5 (437), a flavor-5 `inf_sd_max_change` outside [1, 2] (503-510), and stochastic inflation with `inf_lower_bound < 1` (289-291).

**Applying inflation:**

- *Deterministic:* $x_n\leftarrow\bar x+\sqrt\lambda(x_n-\bar x)$, written as `ens * sd_inflate + mean * (1 - sd_inflate)`. The comment there reads: "Following line can lead to inflation of 1.0 changing ens on some compilers" (556-560).
- *RTPS:* resets the copy to `inf_initial(POSTERIOR_INF)` (`filter_mod.f90:1594-1595`), then overwrites it with $1+\alpha(\sigma_b-\sigma_a)/\sigma_a$, which scales the spread linearly (550-552).
- *Stochastic:* never deflates (584-593).
- *Damping:* $\lambda\leftarrow1+d(\lambda-1)$ (`filter_mod.f90:824-827,924-927`).

**Flavor 2** (Anderson 2009) runs once per (observation, state) pair (`assim_tools_mod.f90:796-805`; `adaptive_inflate_mod.f90:707-756`). It takes $\bar h$ and $\sigma_p^2$ from the original inflated prior:

1. Compute $\gamma=f|\mathrm{corr}|$ (729).
2. Deflate: $\tilde\sigma_p^2=\sigma_p^2/(1+\gamma(\sqrt{\lambda_0}-1))^2$ (732-737). The already-applied inflation $\lambda_0$ is held in the ensemble-SD copy (`assim_tools_mod.f90:456-458`).
3. Model the innovation as $y-\bar h\sim\mathcal N(0,\theta^2)$ with $\theta^2=(1+\gamma(\sqrt\lambda-1))^2\tilde\sigma_p^2+R$ (1071).
4. `linear_bayes` (1060-1116) linearises the likelihood as $\ell+\ell'(\lambda-\bar\lambda)$, with an analytic $\ell'$ (1092-1094). Maximising prior × likelihood gives $\lambda^2+b\lambda+c=0$, where $b=\ell/\ell'-2\bar\lambda$ and $c=\bar\lambda^2-\sigma_\lambda^2-\ell\bar\lambda/\ell'$. The code takes the root nearer $\bar\lambda$ (1102-1114). Basis: derived. The discriminant is $(\ell/\ell')^2+4\sigma_\lambda^2\ge0$, so `solve_quadratic` (1197-1222) never takes the square root of a negative number.
5. The new SD is $\sqrt{-\sigma_\lambda^2/(2\ln r)}$ (894). It is left unchanged if it is within `TINY` of `inf_sd_lower_bound` (862), if $r>0.99$ (886), or if it would grow (898-901).
6. $\lambda$ is clamped to `[inf_lower_bound, inf_upper_bound]` (641-648). If `inf_sd <= 0`, nothing adapts (624).

**Flavor 5** uses an inverse gamma prior (`change_GA_IG`, 908) and a $-1/N$ innovation term (1135-1140). It keeps the old SD if `shape <= 2` (924-927, 952-955) or if the new SD exceeds `inf_sd_max_change` times the old (961-965). Lines 938-939 repeat a `density_1 /= density_1` test; the duplicate is harmless. **Flavor 3** sets $\gamma=1$ and passes one value from task to task (`assim_tools_mod.f90:462-465,733-740`).

### 4. Inflation defaults and documentation drift

| Item | `filter_mod.f90` | `filter_mod.rst` | `filter_mod.nml` |
|---|---|---|---|
| `inf_flavor` | `0,0` (248) | `0,0` (69) | `0,0` (42) |
| `inf_initial`, `inf_deterministic`, `inf_sd_initial`, `inf_sd_max_change`, `inf_damping` | `1.0`, `.true.`, `0.0` (no adaptation), `1.05`, `1.0` (251-255) | same | same |
| `inf_lower_bound` | **`1.0, 1.0`** (256) | **`1.0, 1.0`** (74) | **`0.0, 1.0`** (47) |
| `inf_upper_bound` / `inf_sd_lower_bound` | `1e6` / `0.0` (257-258) | same | same |

Basis: source + documentation.

- Namelist reads set only listed items, so the Fortran initialiser is the effective default.
- A setup copied from the template therefore allows prior deflation to 0, which the code default forbids. El Gharamti 2018 found that "allowing moderate deflation is shown to be useful".
- The Lorenz-96 `input.nml` keeps `inf_flavor = 0,0` but pre-fills `inf_damping 0.9`, `inf_sd_initial 0.6`, `inf_sd_lower_bound 0.6` and `inf_lower_bound 1.0` (`models/lorenz_96/work/input.nml:72-82`). With the SD starting at its lower bound, the `TINY` test freezes the SD, so only $\lambda$ adapts.

### 5. Failure modes and their controls

| Failure | Mechanism | DART controls | Basis |
|---|---|---|---|
| Filter divergence | $\sigma_p^2$ too small, so increments vanish | `inf_*`, `cutoff`, `ens_size` | Anderson 2001/2007/2009; probe 2 |
| Spurious updates; imbalance | Sampling noise $\sim1/\sqrt N$; radius too small (the `.rst` advises erring large) | `cutoff`, `special_localization_*`, adaptive localization, `sampling_error_correction` | Hamill et al. 2001; `.rst` |
| Runaway inflation or excess deflation | Inflation absorbs bias or a wrong $R$; $\lambda<1$ | `inf_upper_bound`, `inf_lower_bound`, `inf_damping`, `inf_sd_*`, flavor 5 | Anderson 2009; El Gharamti 2018 |
| Single-precision breakdown | Underflow or overflow in correlations | warning at `assim_tools_mod.f90:1506-1509`; `r8 = r4` at `types_mod.f90:81-85` | source |

### 6. OOPS incremental 4D-Var

Basis: source, read against Courtier, Thépaut & Hollingsworth 1994 and Trémolet 2006/2007.

`IncrementalAssimilation` (`IncrementalAssimilation.h:37-173`) reads one configuration per outer iteration from `iterations` (51-53) and builds a single minimizer (58-60). Each outer iteration (90-127) does the following:

1. Calls `J.evaluate` with `linearize: true` (115-116). `CostFunction::evaluate` (`CostFunction.h:217-277`) builds a per-iteration inner geometry (230-233), runs the nonlinear model, and computes $J_o+J_c$ (247-254), then $B$ (259) and $J_b$ (266).
2. Minimizes (120).
3. Calls `addIncrement` (123).
4. Calls `resetLinearization` (126).

The inner problem, where $\delta x^{(j)}$ are the increments of earlier outer iterations, is:

$$J(\delta x)=\tfrac12\big(\delta x+\textstyle\sum_{j<k}\delta x^{(j)}\big)^TB^{-1}\big(\cdots\big)+\tfrac12\sum_i(\mathbf H_i\mathbf M_{0\to i}\delta x-d_i)^TR_i^{-1}(\cdots)+J_c$$

`DRMinimizer` accumulates $\nabla J_b$ (`*gradJb_ += dxh`, `DRMinimizer.h:149`) and the cross terms of $J_b$ (152-157) across outer iterations.

| `cost type` | $J_b$ class | Background time | Source |
|---|---|---|---|
| `CostFct4DVar` | `CostJb3D` | window start | `CostFct4DVar.h:121-125`; "a special case of the more general weak constraint 4D-Var cost function with one sub-window" (41-46) |
| `CostFct3DVar` | `CostJb3D` | midpoint | `CostFct3DVar.h:132-135` |
| `CostFct4DEnsVar` | `CostJb4D` | sub-windows | `CostFct4DEnsVar.h:171-178` |
| `CostFctWeak` | `CostJbJq` (adds $J_q$) | sub-windows | `CostFctWeak.h:173-180` |

`CostFct4DVar` runs TL forward and AD backward over the window (179-219) and adds only the initial-time increment (224-231). The `jcdfi` constraint adds a digital-filter $J_c$ (138-143).

### 7. OOPS minimizers and convergence

Basis: source.

`instantiateMinFactory.h:37-54` registers 17 minimizers.

- **`DR*` family** (Derber & Rosati 1989; `DRMinimizer.h:35-43`): preconditions with $B$ and carries $\hat x=B^{-1}x$, so $J_b=x^T\hat x$ needs neither $B^{-1}$ nor $B^{1/2}$.
- **`DRIPCG`**: Golub–Ye inexact-preconditioned CG for $A=B^{-1}+H^TR^{-1}H$ (35-74), with a variable limited-memory preconditioner (`QNewtonLMP`, 218/231) and full residual re-orthogonalization (194-197).

| Control | Default | Source |
|---|---|---|
| `ninner` | required | `DRMinimizer.h:83` |
| `gradient norm reduction`: stop when $\lVert r_k\rVert/\lVert r_0\rVert<$ tol | required | `DRMinimizer.h:84`; `DRIPCGMinimizer.h:210-223`; `DRPLanczosMinimizer.h:251-260` |
| `epsilon`: return early if $\lVert\text{rhs}\rVert^2<\epsilon$ | `double` machine epsilon | `DRMinimizer.h:127-133` |
| Throw if $J_b$ or $J_oJ_c$ is negative, infinite or NaN | every iteration | `MinimizerUtils.cc:21-36`; `DRIPCGMinimizer.h:188-191` |
| `online diagnostics.online adj test` | `false`; writes to the log only | `DRMinimizer.h:86`; `HtRinvHMatrix.h:98-105` |

Known gap, per a code comment: "in some cases ss goes to zero before rr. The convergence check below only checks for rr." (`DRIPCGMinimizer.h:204-205`).

**Reference case** (Basis: documentation; checked-in test output). `l95/test/testinput/4dvar_dripcg.yaml` runs 2 outer iterations of 40-variable L95 over 1 day, with `ninner: 10` and `gradient norm reduction: 1e-10` (38-63). `l95/test/testoutput/4dvar_dripcg.test`:

| Quantity | Outer 1 | Outer 2 | Final |
|---|---|---|---|
| Nonlinear $J$ | 124.18395294324809 | 3.2835358590317449 | 3.0311036008392005 |
| $J_o$ (160 obs) | 123.85634722309175 | 0.90193678402655553 | 0.51829565510585729 |
| Norm reduction | 5.1496837674222919e-03 | 4.6680464924192297e-02 | — |

The 1e-10 target is never reached; `ninner` binds. The logged `err = 4.0000000596046370e-01` is binary32(0.4) (probe 3: `0.4000000059604645`). Basis: derived; the storage path was not traced.

### 8. OOPS TL/AD and regression testing

Basis: source.

| Test (`src/test/interface/LinearModel.h`) | Assertion | Tolerance key (L95 / QG) |
|---|---|---|
| `testLinearModelZeroPert` (212-238) | TL and AD of zero give exactly 0 | exact |
| `testLinearModelLinearity` (242-274) | $\lVert M(3.1415\delta x)\rVert=\lVert3.1415M\delta x\rVert$ | `tolerance AD` (reused) |
| `testLinearApproximation` (278-337) | min relative TL error over 12 perturbation scales (`iterations TL`), each ÷10, below tol | `tolerance TL` `1.0e-07` / `1.0e-6` |
| `testLinearModelAdjoint` (341-377) | $\langle\delta x_1,M^T\delta x_2\rangle=\langle M\delta x_1,\delta x_2\rangle$ | `tolerance AD` `1.0e-14` / `1.0e-12` |

- The tolerance values come from `l95/test/testinput/linearmodel.yaml:29-32` and `qg/test/testinput/linear_model.yaml:30-33`.
- `oops::is_close` is relative: $|a-b|\le\max(|a|,|b|)\cdot$tol (`FloatCompare.h:52,122-127`).
- The runtime checks in `Minimizer.h` (100-143, 190-340) are off by default and write only to the log.
- Regression tests compare `Log::test()` output with a reference file. Default tolerances are relative `1.0e-6`, absolute `0.0`, integer `0` (`TestReference.cc:119-126`). A float fails only if it exceeds both rel·|mean| and abs (209-210).

### 9. Reduced precision: IFS evidence and ecTrans

Basis: normative literature (Crossref abstracts) + source.

- **Váňa et al. 2017.** Moving "almost all real-number variables" of the IFS forecast model from 64 to 32 bits gave "no noticeable reduction in accuracy" and "an average gain in computational efficiency by approximately 40%".
- **Lang et al. 2021.** The savings allowed the ensemble's vertical resolution to go "from 91 to 137 levels", and forecasts run "at single precision from IFS model cycle 47R2 onwards".

| ecTrans | Detail | Source |
|---|---|---|
| Precision features | `DOUBLE_PRECISION`, `SINGLE_PRECISION` both `DEFAULT ON`; `foreach( prec dp sp )` builds `ectrans_${prec}` with `parkind_${prec}`; `TRANSI` needs DP, `CUTLASS_3XTF32` SP; `ECTRANS4PY` "can only be built with one precision" | `CMakeLists.txt:58-69,92-95,142-145,193-196`; `src/trans/cpu/CMakeLists.txt:45-95` |
| Mixed precision | Legendre and Gaussian-latitude arrays are `REAL(KIND=JPRD)` in every build; `LLDOUBLE = (JPRB == JPRD)`; "Support for single precision" added in 2015 | `suleg_mod.F90:121-143,185` |
| Round-trip check | Fails if the maximum relative spectral-norm error exceeds `ncheck × epsilon(1.0_jprb)`; off (0) by default; tests use 100, or 1000000 for the fast Legendre transform | `ectrans-benchmark.F90:151-153,912-981`; `tests/CMakeLists.txt:206,218,318` |
| Checksum tests | `REFERENCE_TESTS` and `BITID_TESTS` default `OFF`; "a simple line-by-line diff" of Fletcher-16 checksums; a missing reference skips with exit code 77 | `CMakeLists.txt:211-215`; `ectrans-diff.py:11-21,444-448` |
| Layout invariance | Reference names are "independent of MPI/OpenMP/callmode variants": runs with 0/1/4 MPI tasks, 1/8 threads, `--nproma 16` or `--npromatr 20` all diff against one file | `ectrans_test_helpers.cmake:48-104`; `tests/CMakeLists.txt:172-190` |
| Per-platform references | Intel 2023.2 and NVHPC 24.5 sets; the T47/O48 DP file starts `cffa` vs `bc85`; Intel provenance: compiler 2021.10.0.20230609, MKL 2019.5.281, `MKL_CBWR = "AUTO,STRICT"`, AMD EPYC 7742 | `tests/references/*` |
| Build flags | The `BIT` build uses `-g -O2`; Intel adds `-march=core-avx2 -no-fma` for `BIT` and always adds `-fp-model precise -fp-speculation=safe` | `cmake/ectrans_compile_flags.cmake:9-15,55-63` |

Basis: derived. `ncheck` is a tolerance scaled to the working precision. The checksum tests require bit identity within a platform and across parallel layouts. Cross-compiler equality is not expected (inferred from the per-platform reference layout).

DART supports single precision only by a source edit, `r8 = r4` (`types_mod.f90:81-85`); `digits12` "MUST retain 64 bits" (93-98).

### 10. WRF reproducibility controls

Basis: source + documentation.

| Control or test | Behaviour | Source |
|---|---|---|
| Legacy regression | "bit-for-bit reproducibility … comparing single processor serial runs to OpenMP and MPI parallel runs"; `BIT4BIT` builds with `./configure -d` (no optimisation); `REAL8 = FALSE` | `tools/regtest.csh:14-18,273-281,2585-2589,2614-2616` |
| Pinning | Removes the AIX MASSV library; `-DREGTEST` fixes "a random number used in the SAS CU scheme" | `:2618-2635` |
| Non-vacuity guard | Compares file sizes first because "on a failure to run a forecast, the diffwrf will give a pass. We need to root out this evil." | `:3607-3651` |
| Current CI | SANE `wrf_coop` runs each namelist in `serial`/`mpi`/`openmp` mode; `compare_wrf.sh` diffs `wrfinput*`/`wrfout*` per domain | `wrf_coop.py:31-38,58,261-291`; `compare_wrf.sh:13-66` |
| Comparison criterion | Any `a .ne. b` (460-463) writes `fort.88`/`fort.98`, which means fail (515-519); "digits" of agreement are informational only | `diffwrf.F90` |
| Floating-point model | Intel targets use `-fp-model precise` ("aimed at accuracy"); removing it "enables non value-safe optimizations" | `arch/configure.defaults:283-288,332,2159` |
| Cross-ISA identity | "identical output model on ubuntu 18.04 with gcc 10.2 (on graviton and intel processors)" via `-DAARCH64_X86_CORRECTNESS_FIX`, which evaluates `LOG`/`ATAN`/`TAN` in double precision and rounds back | `configure.defaults:792-793`; `phys/module_sf_myjsfc.F:1215-1220,1257-1262`; `phys/module_cu_tiedtke.F:2938-2942` |
| Decomposition; random numbers | `nproc_x`, `nproc_y = -1` (automatic); `irr_ph = 1` "ensures repeatability across compilers" (`= 2` uses `RANDOM_SEED`) | `run/README.namelist:398-401,735-737` |

**Statistical evidence from the literature:**

- Hong et al. 2013 (one global model, 10 systems): differences from "compilers, parallel libraries, and optimization levels" grow with time, and the resulting seasonal spread "is comparable to" initial-condition spread.
- Ensemble consistency tests (ECT; Baker et al. 2015; Price-Broncucia et al. 2025, extended to MPAS-A) ask whether a run is "statistically distinguishable" from a control ensemble.

No such test was found in the WRF repository.

### 11. Toy probes

Basis: execution of toy models, not DART, IFS, ecTrans or WRF (x86-64 Linux workstation, Python 3.13.15, numpy 2.3.5; scripts and outputs in `support/`).

**Probe 2** (`support/l96_eakf_probe.py`) transcribes the EAKF increment, regression, GC localization (DART 1-D distance), `linear_bayes`, damping 0.9 and deflation. Lorenz-96 has 40 variables, F=8, and RK4 with dt=0.05. All variables are observed every step with R=1, for 3000 cycles; statistics cover cycles 500-2999. Each cell gives time-mean analysis RMSE / spread for random streams 1/2/3:

| Configuration | 20 members | 10 members |
|---|---|---|
| A: no localization, no inflation | 4.217/0.172, 4.197/0.173, 4.215/0.176 | 4.438/0.155, 4.536/0.158, 4.494/0.157 |
| B: GC `c=0.2` only | 0.207/0.180, 0.242/0.182, 0.197/0.182 | 2.865/0.179, 2.648/0.182, 1.931/0.176 |
| C: GC + fixed λ=1.05 | 0.199/0.228, 0.198/0.229, 0.196/0.229 | 0.199/0.218, 0.196/0.218, 0.200/0.219 |
| D: GC + adaptive (mean λ 1.048/1.018/1.048; 1.046/1.018/1.049) | 0.199/0.215, 0.195/0.213, 0.194/0.213 | 0.202/0.206, 0.197/0.204, 0.201/0.204 |
| E: fixed λ=1.05 only | 0.184/0.207, 0.186/0.207, 3.385/0.219 | 4.238/0.185, 4.206/0.186, 4.265/0.185 |

Basis: execution (toy). Observation error SD is 1 and climatological SD is 3.64 (probe 3). A always diverges (spread collapses to ≈0.17). B suffices at 20 members but not at 10. E holds in 2 of 3 runs at 20 and fails at 10. C and D stay at RMSE 0.194–0.202 in all 12 runs. These are not properties of DART: they show only that the transcribed equations reproduce the failure mode described in the literature.

**Probe 3** (`support/precision_probe.py`): first time the RMS difference from a float64 RK4 reference exceeds 1.0, from the same binary32-representable start:

| Model | float32 | float64, re-associated tendency |
|---|---|---|
| Lorenz-63, dt=0.01 | t=11.43 (bits differ from step 1) | t=32.67 (from step 10) |
| Lorenz-96, N=40, F=8, dt=0.05 | t=8.85 (step 1) | t=20.9 (step 1) |

The re-associated tendency `x[j+1]*x[j-1] - x[j-2]*x[j-1] + (F - x[j])` is algebraically equal to the reference, yet it diverges like float32, only later. This is the mechanism behind compiler-dependent output. The 50,000-step Lorenz-96 climate statistics still agree: mean/SD is 2.3441/3.6410 for float64 and 2.3451/3.6415 for float32, a difference smaller than the batch-mean standard errors (0.0060, 0.0063). This mirrors, but does not test, Váňa et al. 2017.

### 12. Performance and resources (L1–L6)

| Level | DART | OOPS | ecTrans | WRF | Basis |
|---|---|---|---|---|---|
| L1 lines / bytes | `assim_tools_mod.f90` 2617 / 110,704; `adaptive_inflate_mod.f90` 1538 / 58,054; `cov_cutoff_mod.f90` 176 / 5,493 | `CostFct4DVar.h` 277 / 11,358; `DRIPCGMinimizer.h` 241 / 8,311 | `ectrans-benchmark.F90` 2301 / 89,365; `suleg_mod.F90` 1209 / 40,725 | `solve_em.F` 5197 / 283,177; `regtest.csh` 3935 / 153,817 | measured (`wc -l -c`) |
| L1 effort; L2 build time; L3 compile latency | not measured | not measured | not measured | not measured | — |
| L4 run time | toy probe 2: 5–10 s per run (21–22 s adaptive; 8 concurrent processes) | not measured | SP IFS ≈40% faster (Váňa 2017) | not measured | measured (toy) / cited |
| L5 check speed | not applicable; CI time not measured | not measured | not measured | not measured | — |
| L6 repository size at the pinned revision | 3547 blobs, 306,535,350 B | 1548, 6,565,249 B | 1014, 5,029,410 B | 4944, 274,620,682 B | measured (sum of Git tree blob sizes) |
| L6 memory, energy | not measured | not measured | 4 vs 8 B per real (derived) | not measured | — |

### 13. Comprehensibility (C1) and simplicity (C2)

**C1: comprehension hazards.**

- `cutoff` is a half-width, but nothing in `input.nml` says so.
- $\lambda_0$ is stored in a slot named for the ensemble SD (`assim_tools_mod.f90:456-458`).
- The RTPS logical `IF` (`adaptive_inflate_mod.f90:550-552`) guards only `inflate = ...`, though the indentation suggests it also guards `ens = ...`. Basis: derived. It is harmless when `asprd = 0`; other cases are unexamined.
- Three sources disagree on `inf_lower_bound` (Finding 4).
- OOPS reuses `tolerance AD` for the linearity test (`LinearModel.h:272`).
- OOPS online TL/AD checks only write to the log.
- `ninner` silently binds before the requested reduction is reached (Finding 7).
- WRF signals pass or fail by whether `fort.88` exists, so it needs a guard against vacuous passes.

**C2: simplifications and one shared principle.**

- DART flavors 2, 3 and 5 are one model: a prior on λ, an innovation likelihood with γ-weighted variance, and a moment fit. They differ only in prior family and spatial support; flavor 5 is already coded as a sub-flavor of 2.
- All acceptance standards (bitwise; OOPS 1e-6; ecTrans `ncheck×eps`; ECT) reduce to one form: the difference in a chosen observable (bits, logged scalars, spectral norms, distributions) must be at most a threshold. Naming the observable explicitly, as ecTrans checksums and WRF "digits" partly do, would make every special case an instance of one rule.
- WRF `AARCH64_X86_CORRECTNESS_FIX` and ecTrans `suleg` share one principle, coded case by case in each: evaluate library-dependent or ill-conditioned kernels at higher precision and round once.

### 14. Validation coverage (V1–V4) and acceptance by change type

| | DART | OOPS | ecTrans | WRF |
|---|---|---|---|---|
| V1 adequacy / non-vacuity | CI builds L63/L96 with FP traps (`-ffpe-trap=invalid,zero,overflow`) and only runs `filter`; outputs are not compared (`build_run_model/action.yml:55-63,91-108`) | logged J/Jo/Jb checked against a reference; asserts on non-zero inputs (`LinearModel.h:355-367`) | `ncheck`; a missing checksum reference *skips* (exit 77) | size and time-count guards |
| V2 differential / metamorphic | not found | TL vs finite-difference NL; AD dot product; linearity | checksums invariant across MPI/OpenMP/NPROMA | serial vs OpenMP vs MPI; cross-ISA identity claimed for one GNU setup |
| V3 concurrency / hardware | task-count dependence documented for stochastic paths only | not examined | CPU model and `MKL_CBWR` recorded | decomposition tests; no fault injection found |
| V4 real data / human factors | not examined | not examined | not examined | literature only (Hong 2013; ECT) |
| Compiler change accepted by | CI completion only | relative 1e-6 on logged scalars | per-platform references | bitwise for `-d` builds; otherwise statistical |
| Precision change accepted by | manual `r8 = r4` | not examined | `ncheck×eps`; single-precision references | `REAL8` switch; no cross-precision comparison found |

## Boundaries

**Not examined:**

- DART: non-EAKF kinds; probit transforms; groups; sampling-error tables; `threed_sphere` and vertical localization; real-model runs; whether EAKF is bitwise reproducible across task counts.
- OOPS: weak-constraint, 4DEnVar and saddle-point formulations; `QNewtonLMP`; VarBC; model interfaces; operational use of the online diagnostics.
- ecTrans: GPU paths; current CI status of the reference and bit-identity tests; adjoint transform tests.
- WRF: NMM/HWRF; whether `AARCH64_X86_CORRECTNESS_FIX` gives identity beyond gcc 10.2 on Ubuntu 18.04.

**Unknown:** the significance testing in Váňa 2017 and Lang 2021 beyond their abstracts; whether operational single-precision IFS uses this ecTrans revision; the effect on DART of the probe-1 indefiniteness.

**Not measured:** cells so labelled in Finding 12. **Unsupported:** `spread_restoration = .true.`; `inf_flavor = 1`; RTPS as prior inflation; `ECTRANS4PY` with both precisions.

**Not established:**

- The toy probes say nothing about real DART configurations, the safety of single precision for any model, or the harmlessness of any compiler change.
- That ecTrans does not expect cross-compiler equality is inferred.
- The `net_a` and RTPS-`IF` notes describe behaviour; they are not demonstrated defects.

## Evidence

Files came from `raw.githubusercontent.com` and trees from the GitHub Git trees API, at the pinned revisions, on 2026-11-20. Path:line citations in Findings refer to:

- `NCAR/DART` @ `df5b08d03aa44c3a6b2b561a903b00b7193611ca`
- `JCSDA/oops` @ `5625198ec14e3ad6ec0c77f59f9de9d210d4dcac`
- `ecmwf-ifs/ectrans` @ `e63c36a5902444284a5650325be72a34097f7362`
- `wrf-model/WRF` @ `06d4240ae989cc3e50af412bb472df3d9048783c`

Spot-check anchors:

- `assim_tools_mod.f90:1332`: `! but WILL NOT reproduce for a different number of MPI tasks.`
- `filter_mod.nml:47`: `inf_lower_bound = 0.0, 1.0,`
- `TestReference.cc:119`: `tolRelativeFloat_ = conf.getDouble("float relative tolerance", 1.0e-6);`
- `ectrans-benchmark.F90:974`: `if (zmaxerrg > real(ncheck, jprb) * epsilon(1.0_jprb)) then`
- `diffwrf.F90:460`: `IF (a .ne. b) then`

**Literature** (DOIs resolved on 2026-11-20 via Crossref; the WRF technical note via DataCite): Lorenz 1963, 10.1175/1520-0469(1963)020<0130:DNF>2.0.CO;2; Evensen 1994, 10.1029/94JC00572; Courtier, Thépaut & Hollingsworth 1994, 10.1002/qj.49712051912; Houtekamer & Mitchell 1998, 10.1175/1520-0493(1998)126<0796:DAUAEK>2.0.CO;2; Gaspari & Cohn 1999, 10.1002/qj.49712555417; Anderson 2001, 10.1175/1520-0493(2001)129<2884:AEAKFF>2.0.CO;2; Hamill, Whitaker & Snyder 2001, 10.1175/1520-0493(2001)129<2776:DDFOBE>2.0.CO;2; Derber & Rosati 1989, 10.1175/1520-0485(1989)019<1333:AGODAS>2.0.CO;2; Trémolet 2006, 10.1256/qj.05.224; Trémolet 2007, 10.1002/qj.94; Anderson 2007, 10.1111/j.1600-0870.2006.00216.x; Anderson 2009, 10.1111/j.1600-0870.2008.00361.x; Anderson et al. 2009 (DART), 10.1175/2009BAMS2618.1; Whitaker & Hamill 2012, 10.1175/MWR-D-11-00276.1; Hong et al. 2013, 10.1175/MWR-D-12-00352.1; Baker et al. 2015, 10.5194/gmd-8-2829-2015; Váňa et al. 2017, 10.1175/MWR-D-16-0228.1; El Gharamti 2018, 10.1175/MWR-D-17-0187.1; Skamarock et al. 2019 (NCAR/TN-556+STR), 10.5065/1dfh-6p97; Lang et al. 2021, 10.1002/qj.4181; Price-Broncucia et al. 2025, 10.5194/gmd-18-2349-2025.

**Execution** (x86-64 Linux workstation; Python 3.13.15; numpy 2.3.5; outputs in `support/probe_outputs.txt`):

```text
python3 support/gc_probe.py
python3 support/l96_eakf_probe.py --nens 20 1 2 3
python3 support/l96_eakf_probe.py --nens 10 1 2 3
python3 support/precision_probe.py
```

## Revalidation

- **DART.** Diff the following regions:
  - in `assim_tools_mod.f90`: the namelist block, `obs_increment_eakf` and `update_from_obs_inc`;
  - `cov_cutoff_mod.f90`;
  - `adaptive_inflate_mod.f90`, from `inflate_ens` to `solve_quadratic`;
  - the `inf_*` initialisers, comparing `inf_lower_bound` across the `.f90`, `.nml` and `.rst` files.

  Rerun `support/gc_probe.py` if the Gaspari–Cohn code changes. EAKF task-count invariance needs `filter` runs under different `mpirun -n` values, diffed bitwise.
- **OOPS.** Re-check the required keys in `DRMinimizer.h`, the `TestReference.cc` default, and the tolerance keys in `LinearModel.h`/`linearmodel.yaml`; rerun L95 `4dvar_dripcg`.
- **ecTrans.** Re-check the precision and reference-test options, the reference-name rule, and `JPRD` in `suleg_mod.F90`; run `ctest -L reference_test` with `-DENABLE_REFERENCE_TESTS=ON -DENABLE_BITID_TESTS=ON`.
- **WRF.** Grep for `-fp-model precise` and `AARCH64_X86_CORRECTNESS_FIX`; re-check `a .ne. b` in `diffwrf.F90` and the `compare` lists in `wrf_coop.py`.
- **Probes.** The probes are deterministic for a fixed numpy version and host, and they check only toy properties.
