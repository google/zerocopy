# Point kinetics with delayed neutrons and xenon feedback, Monte Carlo k-eigenvalue convergence and subcritical limits, and CRAM burnup numerics: source-level behaviour of pyrk, OpenMC, OpenMOC and NJOY2016

## Summary

- **Point kinetics regime boundary is the delayed-neutron fraction β.** For the standard six-group benchmark data set (β = 0.007, Λ = 2×10⁻⁵ s) the linear point-kinetics matrix has a most-negative eigenvalue of −200.8 s⁻¹ and a dominant eigenvalue of +0.1235 s⁻¹ at ρ = 0.003 (stiffness ratio ≈ 1.6×10³), but at ρ = 0.008 (prompt supercritical) the dominant eigenvalue (+52.8 s⁻¹) exceeds every decay mode in magnitude and the problem is no longer stiff; it is growth-limited. An exact 50-digit matrix-exponential solution reproduces the published benchmark values (2.2098, 8.0192, 28.297 at ρ = 0.003; 6.1633×10²³ at t = 1 s for ρ = 0.008). Basis: execution + documentation.
- **pyrk** (`pyrk/pyrk@c2bfebf9…`) integrates the neutronics block with SciPy's explicit `dopri5` and samples external reactivity on its fixed output grid. Its RHS and loop reproduce the benchmark to ≤ 6×10⁻⁷ relative error. However, a step requested at `t_step` takes effect one output step early, which gives a 30 % power error for a prompt-supercritical step with `dt` = 5 ms. Its shipped precursor tables also contain several defects: `u235`/`fast` has Λ = 0 and a group-3 decay constant of 0.155 s⁻¹ where the internally consistent value is 0.1155 s⁻¹; `pu239` is all zeros; the `sfr` β values sum to 0.1789. pyrk has **no xenon/iodine model**. Basis: source + execution.
- **Xenon makes the coupled problem extremely stiff** (toy model, not pyrk): |Re λ| spans 850 s⁻¹ to 1.2×10⁻⁵ s⁻¹ (ratio 7×10⁷). Over 60 s an explicit RK45 needs about 5×10⁴ steps, against 1,394 Radau steps for a 72 h transient. Once power collapses by many decades without a source term, three implicit integrators disagree qualitatively about re-criticality. Basis: execution (toy model).
- **OpenMC k-eigenvalue statistics** (`openmc-dev/openmc@4743daa7…`): the per-batch `keff` standard deviation is the plain standard error of the mean, which assumes independent batches (`src/eigenvalue.cpp:409-413`). The 95 % t-multiplier is applied only when `confidence_intervals` is enabled, and that setting defaults to false. The combined estimator follows Urbatsch's three-estimator covariance formula. Shannon entropy is computed per generation as a diagnostic only. The batch logic in the files examined never consults it, and the number of inactive batches defaults to 0. Basis: source.
- **OpenMOC** (`mit-crpg/OpenMOC@c9ac4e1e…`) stops when the fission-source residual is below 10⁻⁵ and |Δk| is below 1 pcm. If it hits `max_iters` it only logs a warning. Basis: source.
- **Criticality-safety acceptance** (NUREG/CR-6698): USL = 1 + bias − σ_bias − Δ_SM − Δ_AOA, where positive bias is set to zero and Δ_SM ≥ 0.02. A calculation is acceptable if k_calc + 2σ < USL. Basis: normative (regulatory guidance).
- **OpenMC's CRAM** (`openmc/deplete/cram.py`) is the incomplete-partial-fraction form of order 16 or 48. Order 48 is the default. Executed verbatim:
  - Closed-system nuclide-number conservation holds to ~10⁻¹⁵ when max λΔt ≲ 10³.
  - Conservation degrades to 1.7×10⁻¹³ and 2×10⁻⁷ in toy matrices with λΔt up to ~3×10⁶ and ~3×10¹¹.
  - Tiny negative entries (≤ 4×10⁻¹⁷ of the inventory) occur routinely.
  - The integrator **clips negatives to zero** after every solve (`openmc/deplete/abc.py:764-766`), so it enforces non-negativity, not conservation.
  - Basis: source + execution (toy matrices).
- **NJOY2016 RECONR/BROADR** (`njoy/NJOY2016@ab27c641…`) accept a panel when linear interpolation at the panel **midpoint** matches the true cross-section within `err`. They also accept it when it is within `errmax` and the panel's resonance-integral contribution is below `errint`, or when a 7- to 9-significant-figure energy limit forces convergence. Defaults are errmax = 10·err and errint = err/20000, and the tolerance tightens 5× below 0.4999 eV. Basis: source.

## Applicability

Subjects and how they relate:

| Subject | Revision examined | Role in this report |
|---|---|---|
| pyrk | `pyrk/pyrk` @ `c2bfebf90f5cd36449b6f553675763a23f53aa06` | Point-kinetics + lumped thermal-hydraulics solver. Source read in full for the neutronics path; executed (Python 3.13, NumPy 2.3.5, SciPy 1.18.1, Pint 0.26.2). |
| OpenMC | `openmc-dev/openmc` @ `4743daa7f8966096aa866d3742074452225915d9` | Monte Carlo k-eigenvalue statistics and entropy diagnostics (C++ source read); depletion CRAM solver (Python file executed verbatim). |
| OpenMOC | `mit-crpg/OpenMOC` @ `c9ac4e1ecc9c13bacb44fd470f7fce8c9355606f` | Deterministic MOC eigenvalue solver; only its convergence criteria were read. |
| NJOY2016 | `njoy/NJOY2016` @ `ab27c6414a0f25b173f2b637e6dc7e428fdaff00` | RECONR/BROADR tolerance semantics (source read). ACER read only for its role. Nothing was executed. |
| NUREG/CR-6698 | U.S. NRC, ADAMS ML050250061 | Upper-safety-limit arithmetic. |
| Literature | DOIs in **Evidence** | Benchmarks, CRAM theory, entropy diagnostic, clustering. |

The subjects are examined **side by side, as layers of one analysis chain**: data processing (NJOY), then transport eigenvalue (OpenMC/OpenMOC), then depletion (OpenMC CRAM), with kinetics (pyrk) alongside. No coupled multi-code workflow was run.

Scope limits:
- pyrk results use its own `Neutronics` class, `driver.f_n` RHS, `Timer` and `StepReactivityInsertion`. The outer loop is reproduced from `driver.solve` (lines 167-185) with the thermal-hydraulics block omitted (`feedback=False`, no components). pyrk's temperature-feedback path was not executed.
- The CRAM probes execute `openmc/deplete/cram.py` (SHA-256 `a779066d…7c26`) unchanged. Its two imports, `openmc.checkvalue` and `openmc.deplete.abc.DepSystemSolver`, are replaced by trivial stand-ins. The test matrices are **toy matrices**, not OpenMC chain files; OpenMC transport was never run.
- All OpenMC eigenvalue statements are about source code at the pinned revision; no OpenMC simulation was executed.
- The xenon results come from a toy model written for this report. They do not describe pyrk, OpenMC, or any reactor.

## Findings

### 1. Point-kinetics formulation and regime boundaries

The six-group point-kinetics equations, as implemented by pyrk (`pyrk/neutronics.py:103` `dp = power * (rho - beta) / Lambda + precursors`; `:122` `return beta_j * power / Lambda - lambda_j * zeta`):

```text
dP/dt  = ((ρ(t) − β)/Λ) P + Σ_j λ_j C_j
dC_j/dt = (β_j/Λ) P − λ_j C_j            j = 1..6,  β = Σ β_j
equilibrium start: P = 1, C_j = β_j / (λ_j Λ)   (pyrk driver.py:118-122)
```

For a constant ρ this is linear: y(t) = exp(Mt) y₀. The dominant eigenvalue ω₀ satisfies the inhour relation ρ = ωΛ + Σ β_j ω/(ω + λ_j).

Eigenvalue structure for the benchmark data (β_j = 0.000266, 0.001491, 0.001316, 0.002849, 0.000896, 0.000182; λ_j = 0.0127, 0.0317, 0.115, 0.311, 1.40, 3.87 s⁻¹; Λ = 2×10⁻⁵ s):

| ρ (Δk) | regime | most negative eig (s⁻¹) | dominant eig (s⁻¹) | \|min\|/\|dominant\| |
|---|---|---|---|---|
| 0.003 | delayed supercritical | −200.765 | +0.123537 | 1.63×10³ |
| 0.007 (= β) | prompt critical | −13.2449 | +11.6443 | 1.14 |
| 0.008 | prompt supercritical | −5.15829 | +52.8035 | 0.098 |

Basis: execution (`pk_probe.py`, NumPy eigvals of the exact matrix).

Below β, an explicit integrator's step is limited by stability against the fast negative mode, not by accuracy. Above β, accuracy against the fast positive mode, with an e-folding time ≈ Λ/(ρ − β) to first order, dominates. Implicit methods buy nothing there. Basis: derived (from the table).

Exact reference (50-digit `mpmath.expm`, step at t = 0 from equilibrium):

| ρ | t (s) | exact P(t) |
|---|---|---|
| 0.003 | 0.1 / 1 / 10 / 20 | 1.799528209 / 2.209840457 / 8.019199973 / 28.2974 |
| 0.007 | 0.01 / 0.1 / 0.5 / 1 / 2 | 4.50885849 / 45.22304458 / 5345.8876 / 1.805731634×10⁶ / 2.059156×10¹¹ |
| 0.008 | 0.01 / 0.1 / 1 | 6.202853575 / 1410.421804 / 6.16333375×10²³ |

These match the "Exact" column of the published comparison (2.2098, 8.0192, 28.297 at t = 1, 10, 20 s for ρ = 0.003; 6.1634×10²³ for ρ = 0.008) in McMahon & Pierson, arXiv:1001.4100 v2, Tables 1-2. That column is attributed there to Chao & Attard (1985). Basis: execution + documentation.

### 2. pyrk: what its solver actually does

| Mechanism | Source (pyrk @ c2bfebf9) | Consequence |
|---|---|---|
| Neutronics ODE: `ode(f_n).set_integrator('dopri5')`; thermal-hydraulics is a **separate** `ode(f_th)` (`driver.py:167,171`). | Loop `driver.py:175-184`: `si.timer.advance_one_timestep()`, then `n.integrate(...)`, then `th.integrate(...)`. | Explicit Dormand–Prince 5(4) with SciPy defaults (rtol 1e-6) inside each output step. Neutronics and TH are **operator-split**: each block sees the other's state frozen at the last output step. |
| Reactivity evaluated at the timer index, not the ODE time: `f[i] = si.ne.dpdt(si.timer.ts, ...)` (`driver.py:69`). | `reactivity(t_idx, ...)` sums component feedback and `self._rho_ext(t_idx=t_idx)` (`neutronics.py:148-155`). | ρ is piecewise constant over each output interval, evaluated at the interval's **end** index. Feedback is lagged by one output step. |
| Step insertion: `if x < self.timer.t_idx(self.t_step): return self.rho_init else: return self.rho_final` (`reactivity_insertion.py:73-77`); `t_idx` rounds (`timer.py:58` `return int(round(num / denom))`). | `advance_one_timestep` increments `ts` **before** integrating the interval. | The interval (t_step − dt, t_step] already uses `rho_final`, so the step is applied `dt` early. |
| Feedback gate: `if self.feedback and t_idx > self._timer.t_idx_feedback` (`neutronics.py:149`). | Component reactivity is `alpha_temp * dtemp(timestep)` (`th_component.py:176`). | Linear temperature coefficients only. There is no fission-product poison state. A text search of every `.py` file in the tree finds no `xenon`, `iodine` or `xe135`. |

Execution of pyrk's own RHS and loop with the benchmark data injected into its `PrecursorData` instance (`pk_probe.py`). Here `rhs_calls` counts calls to `driver.f_n`:

| ρ | dt (s) | rhs_calls | worst relative error vs exact at checked times |
|---|---|---|---|
| 0.003 | 0.005 | 16,096 (t ≤ 10 s) | 3.0×10⁻⁷ (t = 0.01 s), ≤ 1.5×10⁻¹¹ for t ≥ 0.1 s |
| 0.003 | 0.001 | 80,000 | 1.5×10⁻⁸ |
| 0.007 | 0.005 | 1,600 (t ≤ 1 s) | 2.0×10⁻⁹ |
| 0.008 | 0.005 | 280 (t ≤ 0.1 s) | 6.3×10⁻⁷ |
| 0.008 | 0.001 | 800 | 5.5×10⁻¹⁰ |

The RHS count is about eight calls per output step at small ρ. Basis: execution.

**Step-time sampling defect, observed.** The step is requested at t_step = 0.1 s with dt = 5 ms:

| ρ | pyrk P(t_end) | exact, step at 0.100 s | ratio | exact, step at 0.095 s | ratio |
|---|---|---|---|---|---|
| 0.003 (t_end = 1 s) | 2.1696281 | 2.16750428 | 1.00098 | 2.16962811 | 1.00000 |
| 0.008 (t_end = 0.2 s) | 1838.0382 | 1410.4218 | **1.30318** | 1838.03704 | 1.00000 |

The error is a pure time shift of `dt`, so its size is exp(ω₀·dt). It is negligible below β and large above prompt critical. Basis: execution + source.

**Precursor-data defects in `pyrk/data/precursors.py`** (all observed by instantiating `Neutronics`):

| Key | Data | Observation |
|---|---|---|
| `u235`/`thermal` | betas `[0.00247, 0.0013845, 0.001222, 0.0026455, 0.000832, 0.000169]` (`:58-63`), Σ = 0.008723; λ = ln2/[54.51, 21.84, 6.00, 2.23, 0.496, 0.179] (`:114-116`); Λ = 1.08×10⁻⁵ s (`:137`). | The comment cites arXiv:1001.4100, but that paper contains neither these β_j nor Λ (text search of the PDF). The half-lives are Keepin's **fast**-fission U-235 set. The thermal U-235 β commonly quoted is ≈ 0.0065 (secondary sources), so Σβ_j = 0.008723 is about 34 % above it. This was not cross-checked against Keepin's tables. |
| `u235`/`fast` | λ = `[0.0127, 0.0317, 0.155, 0.311, 1.4, 3.87]` (`:117`); Λ = `0` (`:138`). | ln2/6.00 s = 0.1155 s⁻¹, so the group-3 value 0.155 is inconsistent with the same file's half-life. The identical list (with 0.155) appears in the input listing of arXiv:1001.4100 §step reactivity. That paper's ramp section and its tabulated results use 0.115. With 0.155 the exact solution gives P(1/10/20 s) = 2.2248/8.7994/34.330 instead of the tabulated 2.2098/8.0192/28.297. Because Λ = 0, `driver.y0` silently produces precursor initial values of `inf` (NumPy RuntimeWarning only). |
| `pu239`/`*` | all β, λ, Λ = 0 (`:70-81,118-119,139-140`). | Accepted by `validate_supported` (`neutronics.py:42-43`). `driver.y0` yields `nan`. |
| `sfr`/`fast` | betas `[0.009, 0.087, 0.070, 0.0014, 0.0060, 0.0055]` (`:82-87`). | Σ = 0.1789, more than 20× any physical delayed fraction. These are not relative abundances either (they do not sum to 1). The shipped SFR example uses this key with feedback off (`examples/sfr/input.py:109,112,115`). |
| units | `units.define('MeV = 1.6e-19 * joules')` (`pyrk/utilities/ur.py:13`). | Converting `1 MeV` gives `1.6e-19 joule` (should be 1.602×10⁻¹³ J). No `.py` file in the tree uses `MeV`, so the defect is latent. |

Basis: source + execution (`u235fast_check.out`, `lambda3_check.out`).

### 3. Stiffness and xenon/iodine coupling (toy model)

`Basis: execution (toy model of 6-group point kinetics + one-group I-135/Xe-135 + lumped power coefficient; not pyrk, not a reactor).`

Constants:
- I-135 and Xe-135 half-lives 6.57 h and 9.14 h, and σₐ(Xe-135) = 2.6×10⁶ b, as given in the U.S. DOE Fundamentals Handbook DOE-HDBK-1019/2-93.
- Illustrative values: γ_I = 0.061, γ_Xe = 0.003, ν = 2.43, full-power flux φ₀ = 3×10¹³ cm⁻²s⁻¹.
- Kinetics data: the benchmark set above.

```text
dI/dt = γ_I Σ_f φ − λ_I I
dX/dt = γ_X Σ_f φ + λ_I I − λ_X X − σ_X φ X,   φ = φ₀ P
ρ = ρ_ext + α_P (P − 1) + (ρ_X − ρ_X,eq),   ρ_X = −σ_X X/(ν Σ_f)
```

Measured outputs:
- Equilibrium xenon worth: −0.02074.
- Jacobian |Re λ| at full power ranges from 850.2 s⁻¹ down to 1.186×10⁻⁵ s⁻¹ (ratio 7.17×10⁷).
- Scram (ρ_ext = −0.05) from equilibrium: xenon peaks at 1.866× equilibrium after 8.32 h, with worth −0.0387. It falls back below equilibrium only at 25.9 h.
- Integrator cost: Radau needs 1,394 steps (9,796 RHS calls, 0.4 s) for 72 h. RK45 needs 51,746 steps (362,120 RHS calls, 6.2 s) for the **first 60 s** alone, about 2×10⁸ steps if extrapolated to 72 h at the stability limit.
- Rod insertion with rods then held fixed (α_P = −0.01):
  - ρ_ext = −0.005: power falls to 0.198 at 1 h. Xenon build-up then drives the toy reactor deeply subcritical.
  - **Without a source term**, Radau, BDF and LSODA agree to 1 h. Afterwards they disagree qualitatively: Radau gives P(24 h) = 0.342, BDF gives ≈ −1×10⁻¹⁶, and LSODA gives `nan`. Radau and BDF produce negative powers down to −9×10⁻¹⁸ and −2×10⁻¹⁶.
  - With ρ_ext = −0.002 the three integrators also disagree at 24 h: LSODA gives 0.665, while Radau and BDF give ≈ 0.
  - With a source of 10⁻⁶ s⁻¹, all three agree (P(24 h) = 0.378, minimum P = 1.56×10⁻⁹). The toy model then shows a xenon-driven second collapse by 48 h.

This toy does not reproduce the setting reviewed in INSAG-7. It shows only the generic coupling the IAEA's updating report discusses, in which xenon poisoning after a power reduction limits controllability. The IAEA publication page states that INSAG-7 "shift[s] the emphasis of its conclusions from the actions of the operating staff to faulty design of the reactor's control rods and safety systems". Basis: documentation (IAEA page) for INSAG-7; toy execution for the numbers.

### 4. OpenMC k-eigenvalue statistics and source convergence

Source-level semantics at `openmc-dev/openmc@4743daa7…`:

| Item | Code | Meaning |
|---|---|---|
| Per-generation k | `calculate_generation_keff` (`src/eigenvalue.cpp:47-81`): track-length tally difference divided by `settings::n_particles` (`:77`). A comment notes `TODO: This should be normalized by total_weight, not by n_particles` (`:75`). | With variance reduction or weighted sources, normalization uses the nominal particle count, not the banked weight. |
| Active-batch mean and σ | `:393-413`: `k_sum[0] += k`; `k_sum[1] += k²`; `keff_std = t_value * sqrt((k_sum[1]/n − keff²)/(n − 1))`. | The standard error assumes independent generations. No autocorrelation or batch-means correction is applied. |
| Confidence multiplier | `if (settings::confidence_intervals) t_value = t_percentile(1 − α/2, n − 1); else t_value = 1.0` (`:401-407`); `CONFIDENCE_LEVEL {0.95}` (`include/openmc/constants.h:47`); default `confidence_intervals {false}` (`src/settings.cpp:54`). | By default the reported σ is 1 standard error, not a 95 % interval. |
| Combined k | `openmc_get_keff` (`:428-585`): Urbatsch three-estimator (collision, absorption, track-length) covariance weighting. It falls back to two estimators when any pair agrees within `FP_REL_PRECISION = 1e-5` (`constants.h:54`, `eigenvalue.cpp:484-505`). With n ≤ 3 realizations it returns the simple mean, with σ = ∞ for n ≤ 1 (`:435-443`). | The variance formula has an (n − 3) denominator, and the estimators themselves are correlated, which is why covariance weighting is used. |
| Shannon entropy | `shannon_entropy` (`:587-616`): H = −Σ pᵢ log₂ pᵢ over entropy-mesh bins of the fission bank. It warns "Fission source site(s) outside of entropy box." Called once per generation (`src/simulation.cpp:678-681`). | Stored and output (`write_eigenvalue_hdf5`, `:682-683`). It never gates the start of active batches. |
| Inactive batches | `int32_t n_inactive {0}` (`src/settings.cpp:105`). | The user must choose; the default discards no batches. |
| Entropy mesh heuristic | Docstring: "OpenMC assigns a mesh such that 20 source sites per mesh cell are to be expected on average" (`openmc/settings.py:105-107`). Code: `n = ceil((self.particles / 20.0)**(1.0 / 3.0)); self.entropy_mesh.dimension = (n,)*d` (`:1797-1799`). | Correct only for d = 3. For a 2-D mesh at 10⁶ particles, n = 37 gives 1,369 bins, ≈ 730 sites per bin (derived). |
| Random-ray mode | `entropy_on = true` with FSR-based entropy; a user mesh is a fatal error (`src/settings.cpp:831-836`). | Different diagnostic object per solver mode. |

Literature:
- Brown (PHYSOR 2006, LA-UR-06-3737) proposed the source-entropy diagnostic because k can appear converged well before the spatial source is, especially in loosely coupled / high-dominance-ratio systems.
- Dumonteil et al. (2014) analyse spatial clustering of the neutron population in criticality simulations.
- Ueki (2002) studies inter-generational correlation.
- Brissenden & Garlick (1986) studied biases in k and its error.

Basis: documentation (titles/abstract-level summaries). The magnitude of variance underestimation for a given model is **not** established here; see Boundaries.

### 5. OpenMOC convergence semantics

At `mit-crpg/OpenMOC@c9ac4e1e…`:
- `_converge_thresh = 1E-5` (`src/Solver.cpp:65`); `computeEigenvalue(int max_iters=1000, residualType res_type=FISSION_SOURCE)` (`src/Solver.h:515-516`).
- Each iteration computes `dr = residual / previous_residual` (an apparent dominance ratio) and `int dk = 1e5 * (_k_eff - k_prev)` (`Solver.cpp:1642-1643`).
- It stops when `residual < _converge_thresh && std::abs(dk) < 1` (`:1680`). At `max_iters` it logs "Unable to converge the source distribution" and returns (`:1684-1685`).

A successive-iterate residual r relates to the true error e roughly as e ≈ r/(1 − DR). With DR → 1 a 10⁻⁵ residual can hide a much larger source error. Basis: source + derived.

An OpenMC-versus-OpenMOC cross-check requires multigroup cross sections condensed from OpenMC tallies (`openmc.mgxs`). Any discrepancy therefore conflates (a) MOC discretization, (b) MGXS condensation and self-shielding error, and (c) Monte Carlo statistics. Boyd et al. (2014) describe OpenMOC and its benchmark verification. Basis: documentation + derived. No such cross-check was run here.

### 6. Subcritical limits: from calculation to acceptance

NUREG/CR-6698 (U.S. NRC; manuscript completed December 2000, published January 2001):
- **Eq. (1):** USL = 1.0 + Bias − σ_Bias − Δ_SM − Δ_AOA. The bias is the difference between the average calculated k_eff for critical benchmarks and unity, and "a bias is set to zero if the calculated average k_eff is greater than one" (OCR spelling normalized).
- **Eq. (2):** k_c + 2σ_k < USL, applied to all normal and credible abnormal conditions.
- **§2.4.5:** "the minimum subcritical margin, Δ_SM, must not be less than 0.02 in k_eff" (OCR spelling normalized).
- **§2.4.6, Eqs. (35)-(36):** USL = K_L − Δ_SM − Δ_AOA, where K_L is the statistical (e.g., tolerance-limit) result, and k_eff + 2σ_k < USL.

Basis: normative (regulatory guidance text, OCR'd PDF).

Consequences that tie back to the code:
1. σ_k in Eq. (2) is whatever the code reports. In OpenMC by default that is a 1-standard-error figure computed under the independence assumption (Finding 4).
2. Unconverged sources bias k_c itself, and no σ covers that.
3. The bias term inherits every nuclear-data processing tolerance (Finding 8).

Basis: derived.

ANSI/ANS-8.1 and ANSI/ANS-8.24 (the consensus standards referenced by this practice) and IEC 60880 were **not examined**; they are paywalled.

### 7. CRAM depletion in OpenMC: algorithm, conservation, non-negativity

Algorithm (`openmc/deplete/cram.py:65-105`, verbatim core):

```python
step_dt = dt if substeps == 1 else dt / substeps
A = step_dt * csc_array(A, dtype=np.float64)
...
y = n0.copy()
for _ in range(substeps):
    for alpha, solve in zip(self.alpha, solvers):
        y += 2 * np.real(alpha * solve(y))      # solve(y) = (A − θ_k I)^{-1} y
    y *= self.alpha0
```

- Order 16 has `c16_alpha0 = 2.124853710495224e-16` (`:131`); order 48 has `c48_alpha0 = 2.258038182743983e-47` (`:199`).
- The default is `cram48` (`abc.py:567-568,643`), with `substeps` default 1 (`abc.py:644`, added in 0.16.0 per `:574-580`).
- The coefficients are Pusa's IPF form (NSE 182, 2016); substepping follows Isotalo & Pusa (NSE 183, 2016).
- Because the final `y *= alpha0` rescales by ~10⁻⁴⁷, intermediate vectors reach about 3.4–4.4×10⁴⁶ × the inventory (measured).

**Integrator post-processing** (`openmc/deplete/abc.py:758-768`):

```python
results = deplete(self._solver, self.chain, n, rates, dt, i, matrix_func, ...)
# Clip unphysical negative number densities
for r in results:
    r.clip(min=0.0, out=r)
```

**Conservation identity (derived).** For a closed system, 1ᵀA = 0, so 1ᵀ(A − θI)⁻¹ = −1ᵀ/θ. In exact arithmetic the solver therefore multiplies the total inventory by r(0), the rational function evaluated at 0. Measured r(0) − 1 is 2.2×10⁻¹⁶ (order 16) and 8.9×10⁻¹⁶ (order 48). Any larger conservation error is floating-point error in the shifted solves.

Measured scalar accuracy:
- max |r(−x) − e⁻ˣ| over 220,001 samples of x ∈ [0, 10¹²] is 1.44×10⁻¹⁵ (order 16) and 3.44×10⁻¹⁵ (order 48).
- Both maxima occur at small x, where double-precision rounding, not the approximation, dominates.
- At large x the order-16 floor is α₀ ≈ 2.1×10⁻¹⁶, against 2.3×10⁻⁴⁷ for order 48.

Basis: execution of the solver's own coefficients.

Toy-matrix results (`cram_probe.py`, `cram_random_probe.py`, `cram_diag_probe.py`; N = total initial atoms):

| Case | max rel. error (entries > 10⁻¹⁰N) | negatives | \|Σn − N\|/N | after OpenMC clip |
|---|---|---|---|---|
| 12-nuclide closed chain, λ ∈ [10⁻¹², 10⁶] s⁻¹, Δt = 1 h–30 d, all atoms in head nuclide | CRAM48 ≤ 7.9×10⁻¹⁶ (substeps = 1), ≤ 2.8×10⁻¹⁴ (substeps = 4, 16); CRAM16 ≤ 1.1×10⁻¹² | 0 | ≤ 2.8×10⁻¹⁴ | unchanged |
| Same chain, uniform start, Δt = 1 d | CRAM16 substeps = 1: **1.4×10⁻⁸** (absolute floor ≈ α₀·N); substeps = 4: 2.4×10⁻¹⁵ | 0 | ≤ 6×10⁻¹⁵ | unchanged |
| 3-cycle (eigenvalues −k(1.5 ± 0.866i)), kΔt = 1–10³ | ≤ 1.8×10⁻¹¹ (CRAM16, kΔt = 10, substeps = 1); otherwise ≤ 5.9×10⁻¹⁴ | 0 | ≤ 5.7×10⁻¹⁴ | unchanged |
| 40 random closed 25-nuclide matrices, rates 10⁻¹⁵–10⁵ s⁻¹, Δt = 10⁶ s | CRAM16 1.1×10⁻⁶, CRAM48 6.9×10⁻⁷ (entries > 10⁻⁸N) | CRAM16 in 18/40 matrices (min −4.0×10⁻¹⁷N); CRAM48 in 14/40 (min −2.8×10⁻²⁶N) | CRAM16 2.8×10⁻⁷, CRAM48 2.1×10⁻⁷ | 2.8×10⁻⁷ / 2.1×10⁻⁷ |
| Same seeds, CRAM48, rates capped at 10⁰ / 10⁻³ / 10⁻⁶ s⁻¹ | — | — | max 1.7×10⁻¹³ / 1.9×10⁻¹⁵ / 1.8×10⁻¹⁵ (median ≈ 5×10⁻¹⁶) | — |

Interpretation:
- Non-negativity: tiny negatives are routine but negligible in magnitude, and OpenMC's clip removes them.
- Conservation: the clip cannot restore conservation. The clip only adds mass; it is not where conservation is lost. Conservation error grows with the dynamic range of λΔt in the toy matrices. The worst single matrix lost about 2×10⁻⁷ of its inventory in one step.
- Whether realistic chains with very short-lived nuclides reach this regime is **not established here**.

Basis: execution (toy matrices) + source.

Cost (toy sparse matrices, Intel Xeon @ 2.60 GHz, SciPy `spsolve`/`splu`, single process). Wall time per call:

| N (nnz) | CRAM16, s = 1 | CRAM16, s = 4 | CRAM48, s = 1 | CRAM48, s = 4 |
|---|---|---|---|---|
| 500 (1,481) | 15.0 ms | 13.4 ms | 32.4 ms | 39.9 ms |
| 3,000 (8,867) | 122 ms | 123 ms | 392 ms | 477 ms |

Peak RSS was 174 MiB. Substeps reuse LU factorizations (`cram.py:94-98`), so s = 4 costs little more than s = 1. Basis: execution (toy).

Predictor–corrector schemes available in `openmc/deplete/integrators.py`:
- `PredictorIntegrator` (`:17`)
- `CECMIntegrator` (`:58`, citing Isotalo NSE 180, 2015)
- `CF4Integrator` (`:113`)
- `CELIIntegrator` (`:189`)
- `EPCRK4Integrator` (`:251`)
- `LEQIIntegrator` (`:317`)
- stochastic-implicit `SICELIIntegrator` (`:414`) and `SILEQIIntegrator` (`:479`)

Each stage calls `_timed_deplete`, so the clip applies at every stage. Basis: source.

### 8. NJOY2016 reconstruction and broadening tolerances

RECONR card 4 (`src/reconr.f90:103-118`) and defaults (`:427-430`):

```fortran
read(nsysi,*) err,tempr,errmax,errint
if (errmax.le.zero) errmax=10*err
if (errmax.lt.err) errmax=err
if (errint.le.zero) errint=err/20000
```

Acceptance test for a panel [x(i), x(i−1)] in `resxs` (`:2356-2414`):

1. If the midpoint cannot be represented with 9 significant figures (8 for 0.1 < E < 1 eV), the panel is accepted as "convergence forced by significant figures check" (`:2360-2365`).
2. The true σ at the midpoint xm is compared with linear interpolation, giving dm(j) = |σ_j(xm) − σ_lin,j|.
3. The thresholds are errn = err and errm = errmax, each divided by 5 when x(i−1) < `trange` = 0.4999 eV (`:2389-2392`, `:2270`).
4. The panel converges if dm(j) ≤ errn·σ_j for every reaction (`:2394-2397`).
5. Otherwise it is accepted if dm(j) ≤ errm·σ_j and dm(j) < 2·errint·xm/dx for every reaction. This is "convergence forced by resonance integral check" (`:2398-2414`).
6. Even a converged panel is subdivided when it lies below the top of the resolved range and is wider than 4.1× the distance back to the last accepted point. The code comment reads "don't allow big increases in the energy step, they may be misconvergences" (`:2415-2419`, `estp = 4.1`).

Consequences (derived):
- The check is a **midpoint** test only. A structure narrower than a panel that happens to be nearly linear at the midpoint is not detected by this test.
- A commented-out "temporary patch" for R-matrix-limited (LRF = 7) data states that "the initial grid points are wrong, resulting in sometimes missing part of the peak" (`:2377-2385`). The initial grid (resonance energies ± half-widths, `:979-996`) is the guard against this.
- The default errint = err/20000 allows the looser errmax = 10·err wherever a panel's resonance-integral contribution is small. A reported "0.1 % reconstruction" therefore does not bound pointwise error everywhere.

BROADR (`src/broadr.f90`):
- SIGMA1-kernel broadening, with a direct expansion at high temperature / low energy (`:28-45`).
- Thinning parameters errthn, thnmax, errmax and errint (`:69-81`) take the same meanings as in RECONR.
- The "bootstrap" option broadens each temperature from the previous one, which is faster, but "errors accumulate" (`:99-105`).
- By default thnmax = 0 broadens to the top of the resolved range, else to the start of the URR, else to min(6.5 MeV, first threshold) (`:107-120`).
- There is a cap of 160 broadenable reactions (`:126-128`).

ACER prepares continuous-energy ACE libraries on the union grid of the total cross section (`src/acer.f90:11-38`).

Basis: source.

### 9. Cross-cutting resource, comprehension and validation profile

**Performance and footprint levels** (measured here unless marked):

| Level | Point kinetics (pyrk / toy) | MC eigenvalue (OpenMC / OpenMOC) | Depletion (OpenMC CRAM) | Data processing (NJOY) |
|---|---|---|---|---|
| L1 authoring/maintenance | pyrk neutronics path is ~10 small methods. Defects found are data-table transcription errors, not solver logic. | not measured | `cram.py` is 205 lines, about 60 of logic | not measured |
| L2 build | pure Python, `pip install --no-deps` in seconds | not built | n/a (Python) | not built |
| L3 solve latency | dopri5: 280–80,000 RHS calls for 0.1–10 s transients (≤ 3.7 s wall). Stiff toy: Radau 0.4 s for 72 h versus RK45 6.2 s per 60 s. | not run | 13–477 ms per call (toy N = 500–3,000) | not run |
| L4 output quality | ≤ 6×10⁻⁷ relative error (benchmark); step-shift error up to 30 % | not run | conservation 10⁻¹⁵ to 2×10⁻⁷ (toy) | tolerances only (source) |
| L5 verification cost | exact reference: one 7×7 50-digit expm per time point (< 1 s) | entropy/k diagnostics are O(bins) per generation (source) | exact reference: mpmath expm on 25×25 matrices, seconds each | not measured |
| L6 memory | not measured | not measured | 174 MiB peak RSS (toy, N ≤ 3,000) | not measured |

**C1, human comprehensibility:**
- pyrk's time semantics (reactivity sampled at the output-grid index, one-step-early steps, operator splitting) are invisible at the input-file level. A reader of `StepReactivityInsertion(t_step=1.0 s)` would not predict a 30 % error above prompt critical.
- OpenMC's "keff ± σ" hides two independent choices: 1σ versus t-interval, and the independence assumption. Its entropy diagnostic needs user judgement.
- NJOY's "err" is one of three interacting tolerances, plus a significant-figure stop.
- CRAM's IPF form is opaque (intermediate values ~10⁴⁶). Its correctness argument is the r(0) identity plus the rational approximation error, both checkable with a few lines.

**C2, simplicity and orthogonality:**
- The safety-relevant invariants are **non-negativity** and **conservation** (depletion), **stationarity of the source** (eigenvalue), and **time placement of reactivity events** (kinetics).
- In each code examined, one mechanism stands in for an invariant it does not imply: clipping for conservation, σ-reporting for convergence, and output-grid indexing for event timing.
- A uniform remedy would treat event times as integration breakpoints and report conservation residuals alongside clipped mass. That remedy is a design suggestion, not an observed feature.

**V1–V4, validation:**
- V1, specification adequacy: the upstream CRAM unit test (`tests/unit_tests/test_deplete_cram.py`) checks two 2×2 matrices against Mathematica plus substep self-convergence. Its matrix `[[-1, 0], [-2, -3]]` has a negative off-diagonal, so it is not a transmutation matrix. No test checks non-negativity or conservation. pyrk's data tables are not checked against Σβ or ln2/T½ consistency; this report's probe found three such violations.
- V2, differential testing: the exact-expm references used here are independent differential oracles. An OpenMC-versus-OpenMOC comparison is a differential test only after separating MGXS error (Finding 5).
- V3, concurrency/crash: not examined. The OpenMC MPI reductions (`eigenvalue.cpp:57-72`) were read only.
- V4, plant falsification: the criticality-safety route is benchmark validation (NUREG/CR-6698). Kinetics codes would be compared with measured transients. Neither was performed here.

## Boundaries

- **Not examined:**
  - pyrk's thermal-hydraulics block, its temperature-feedback execution path, and its multi-point/fictitious-group mode (`n_fic`).
  - Ramp, sinusoidal and zig-zag benchmarks.
  - Feedback benchmarks with adiabatic Doppler feedback (Ganapol 2013).
- **Not examined:** any OpenMC transport run; the magnitude of inter-cycle correlation bias in OpenMC's reported σ_k for a real model; clustering in OpenMC; OpenMC's random-ray solver beyond the entropy setting; CMFD.
- **Unknown:** whether realistic OpenMC depletion chains (with their actual shortest half-lives and capture rates) reach the λΔt dynamic range where the toy matrices lost conservation at the 10⁻⁷ level. That needs the probe rerun on a real chain matrix exported from `openmc.deplete.Chain.form_matrix`.
- **Unknown:** the provenance of pyrk's `u235`/`thermal` β_j values. Its cited source does not contain them.
- **Not examined:** NJOY2016 execution. Actual point counts and errors for given `err` values, the URR treatment, and THERMR/HEATR/GROUPR were not examined.
- **Not examined:** ANSI/ANS-8.1, ANSI/ANS-8.24 and IEC 60880 text (paywalled). INSAG-7's technical body (the PDF could not be retrieved; only the IAEA abstract page was read).
- **Known not to apply:** the toy xenon model's numbers (peak at 8.3 h, worth −0.0387, oscillation) are properties of its illustrative parameters, not of any reactor or of pyrk. Do not cite them as reactor data.
- **Unsupported (by the subject):**
  - pyrk has no xenon/iodine or other fission-product-poison dynamics.
  - OpenMC does not choose inactive batches automatically.
  - OpenMOC provides no statistical uncertainty; it is deterministic.
- **Attractive but unestablished:**
  - The step-shift defect is not known to affect pyrk's published analyses; their parameters were not examined.
  - OpenMC's σ_k has not been shown to be materially biased for typical reactor problems. The code assumes independence, and the size of the effect is problem-dependent.
  - CRAM48 is not shown to be "exact" in double precision for stiff chains. Conservation error depended on λΔt range in these toy tests.

## Evidence

Observation dates: all source reads, executions and web verifications were performed on 2026-11-20 (UTC).

**Repositories (raw files fetched at the pinned revisions):**
- `pyrk/pyrk@c2bfebf90f5cd36449b6f553675763a23f53aa06`: `pyrk/neutronics.py`, `pyrk/driver.py`, `pyrk/reactivity_insertion.py`, `pyrk/timer.py`, `pyrk/data/precursors.py`, `pyrk/th_component.py`, `pyrk/utilities/ur.py`, `examples/{default,sfr}/input.py`. Tarball from codeload.github.com, SHA-256 `ecd56ca72226a769e8e213fee6d497da1a91867e77328780f81d275e27784d96`.
- `openmc-dev/openmc@4743daa7f8966096aa866d3742074452225915d9`: `src/eigenvalue.cpp`, `src/simulation.cpp`, `src/settings.cpp`, `include/openmc/constants.h`, `openmc/settings.py`, `openmc/deplete/{cram.py,abc.py,integrators.py,pool.py}`, `openmc/_sparse_compat.py`, `tests/unit_tests/test_deplete_cram.py`.
- `mit-crpg/OpenMOC@c9ac4e1ecc9c13bacb44fd470f7fce8c9355606f`: `src/Solver.cpp`, `src/Solver.h`.
- `njoy/NJOY2016@ab27c6414a0f25b173f2b637e6dc7e428fdaff00`: `src/reconr.f90`, `src/broadr.f90`, `src/acer.f90`.

**Literature (DOIs verified against Crossref metadata on the observation date):**
- G. R. Keepin, T. F. Wimett, R. K. Zeigler, Phys. Rev. 107(4):1044–1049, 1957, `10.1103/PhysRev.107.1044`.
- B. D. Ganapol, "A highly accurate algorithm for the solution of the point kinetics equations," Ann. Nucl. Energy 62:564–571, 2013, `10.1016/j.anucene.2012.06.007`.
- D. McMahon, A. Pierson, "A Taylor series solution of the reactor point kinetics equations," arXiv:1001.4100 v2 (2010). Input listing and Tables 1-2 read from the PDF.
- M. Pusa, J. Leppänen, NSE 164(2):140–150, 2010, `10.13182/NSE09-14`.
- M. Pusa, NSE 169(2):155–167, 2011, `10.13182/NSE10-81`.
- M. Pusa, "Higher-Order Chebyshev Rational Approximation Method and Application to Burnup Equations," NSE 182(3):297–318, 2016, `10.13182/NSE15-26`.
- A. Isotalo, M. Pusa, NSE 183(1):65–77, 2016, `10.13182/NSE15-67`.
- A. Isotalo, NSE 180(3):286–300, 2015, `10.13182/NSE14-92`.
- E. Dumonteil et al., "Particle clustering in Monte Carlo criticality simulations," Ann. Nucl. Energy 63:612–618, 2014, `10.1016/j.anucene.2013.09.008`.
- T. Ueki, "Intergenerational Correlation in Monte Carlo k-Eigenvalue Calculation," NSE 141:101–110, 2002, `10.13182/NSE141-101`.
- R. J. Brissenden, A. R. Garlick, "Biases in the estimation of Keff and its error by Monte Carlo methods," Ann. Nucl. Energy 13:63–83, 1986, `10.1016/0306-4549(86)90095-2`.
- P. K. Romano et al., "OpenMC: A state-of-the-art Monte Carlo code for research and development," Ann. Nucl. Energy 82:90–97, 2015, `10.1016/j.anucene.2014.07.048`.
- W. Boyd et al., "The OpenMOC method of characteristics neutral particle transport code," Ann. Nucl. Energy 68:43–52, 2014, `10.1016/j.anucene.2013.12.012`.
- D. A. Brown et al., "ENDF/B-VIII.0 …," Nucl. Data Sheets 148:1–142, 2018, `10.1016/j.nds.2018.02.001`.
- F. B. Brown, PHYSOR 2006, LA-UR-06-3737 (no DOI; title, venue and identifier confirmed via search).

**Standards and guidance:**
- NUREG/CR-6698, "Guide for Validation of Nuclear Criticality Safety Calculational Methodology" (U.S. NRC; ADAMS ML050250061). Eqs. (1), (2), (35), (36) and §2.4.5 read from the PDF text.
- IAEA INSAG-7 publication page (abstract text).
- DOE-HDBK-1019/2-93 constants via search summary (toy-model inputs only).

**Execution environment:**
- Linux x86-64, Intel Xeon @ 2.60 GHz, Python 3.13.15, NumPy 2.3.5, SciPy 1.18.1, mpmath 1.4.1, Pint 0.26.2.
- pyrk installed with `pip install --no-deps` from the pinned tarball. Version string reported: `0.3.dev0`.
- pyrk's `driver` module imports PyTables and the plotter at import time; both are stubbed because `f_n` uses neither.

Key probe logic. Script names such as `pk_probe.py` and `cram_random_probe.py` label the local probes run for this report (from `/tmp/s3_r12_64a_ws/probes/`). They are not published artifacts. The logic needed to reproduce each observation is given here and in the findings, including inputs, seeds and parameters.

```python
# exact PKE reference (pk_probe.py)
M[0,0]=(rho-beta)/Lam; M[0,j+1]=lam[j]; M[j+1,0]=b[j]/Lam; M[j+1,j+1]=-lam[j]
y0=[1]+[b[j]/(lam[j]*Lam)]; P(t)=(mp.expm(M*t)*y0)[0]          # mp.dps=50
# pyrk loop (mirrors driver.solve without TH)
n=ode(counting(driver.f_n)).set_integrator('dopri5'); n.set_initial_value(y0,0); n.set_f_params(si)
while n.successful() and n.t<tf: ti.advance_one_timestep(); n.integrate(ti.current_time().magnitude)
# CRAM closed-system check (cram_random_probe.py): A[t,i]+=r; A[i,i]-=r  (column sums 0)
y=cram.CRAM48(csc_array(A), n0, 1e6); sum_err=(y.sum()-n0.sum())/n0.sum(); ref=mp.expm(A*dt)*n0  # mp.dps=60
```

## Revalidation

Cheapest discriminating checks:

1. **pyrk step timing:** diff `pyrk/reactivity_insertion.py` (`f`), `pyrk/timer.py` (`t_idx`, `advance_one_timestep`) and `pyrk/driver.py` (`solve` loop order, `dpdt(si.timer.ts, …)`). If unchanged, the one-`dt`-early step persists. Rerun `pk_probe.py` §"Step-time sampling" and expect the ratio 1.30318 at ρ = 0.008, dt = 5 ms.
2. **pyrk data:** `grep -n '"u235"\]\["fast"\]\|"pu239"\|"sfr"\]\["fast"\]' pyrk/data/precursors.py`, and check that Σβ and ln2/T½ ≈ λ hold.
3. **OpenMC σ_k semantics:** diff `calculate_average_keff` and `openmc_get_keff` in `src/eigenvalue.cpp`, and check the defaults of `confidence_intervals` and `n_inactive` in `src/settings.cpp`.
4. **OpenMC clip and CRAM:** diff `Integrator._timed_deplete` (`openmc/deplete/abc.py`) and `IPFCramSolver.__call__` (`openmc/deplete/cram.py`). Rerun `cram_random_probe.py` (seed 20261120) and expect CRAM48 negatives in 14/40 matrices and max |Σ error| ≈ 2×10⁻⁷. To extend to a real chain, export `Chain.form_matrix(rates)` for a depletion step and apply the same closed-system check after zeroing loss-to-outside terms.
5. **OpenMOC:** check `_converge_thresh` in the `Solver` constructor and the stopping test in `computeEigenvalue`.
6. **NJOY2016:** diff the `resxs` acceptance block and the card-4 defaults in `src/reconr.f90`, and the card-3 comments in `src/broadr.f90`.
7. **USL arithmetic:** re-read NUREG/CR-6698 Eqs. (1), (2), (35), (36) and §2.4.5. Newer NRC guidance or ANSI/ANS-8.24 revisions may change practice and would need separate examination.
