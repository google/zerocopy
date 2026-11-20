# Rainflow Residue Conventions, Miner Knee Handling, Paris/NASGRO–Newman Crack-Growth Integration, J-Integral Conventions, and API 579/BS 7910 Failure Assessment Curves

## Summary

- **The rainflow *residue convention* controls the Miner damage of short histories more than the counting algorithm does.** We ran three implementations at pinned revisions on identical seeded Gaussian AR(1) histories: fatpack, pyLife, and the ASTM E1049-85 §5.4.4 reference package `rainflow`. The ratios below are relative to ASTM half-cycle residue counting, for a Basquin S–N curve with exponent `m`.
  - Closed loops only (pyLife detector output without residuals): 0.146 (m=3) and 0.0135 (m=5) at 50 samples; 0.67 and 0.52 at 1,000 samples; 0.986 and 0.962 at 100,000 samples.
  - fatpack's `find_rainflow_ranges`, which closes the residue by repeating it as full cycles: 1.84 and 1.99 at 50 samples; 1.10 and 1.28 at 200; within 1.1 % at 10,000 and 0.1 % at 100,000.
  - Closed loops plus residue reversals counted as half cycles reproduced the ASTM counts exactly in every case.
- **pyLife's `FourPointDetector` with `flush=True` returns residuals that end with the last sample duplicated** (`[…, 4, −2, −2]` for the ASTM example). Passing them to `fatpack.concatenate_reversals` raises `ValueError`. The cause is `fourpoint.py:147` appending `samples[-1:]` after a flush has already appended the last sample as a turning point (`general.py:312, 324`).
- **Knee and unit conventions dominate tail damage.** For a collective with 97 % of amplitudes below the knee, pyLife's Miner-original : Haibach : elementary damage ratio was 1 : 1.135 : 1.269. fatpack's linear and bilinear (`m2 = 2m1 − 1`) range curves reproduced pyLife's elementary and Haibach sums to all printed digits. Entering a pyLife *amplitude* knee value as a fatpack *range* parameter inflated damage 32× (= 2⁵).
- **Crack-growth integration error is dominated by step control, not by the law** (own implementation of published equations, illustrative parameters).
  - Fixed-block forward Euler in N gave +0.36 % life error at 10³-cycle blocks, +3.2 % at 10⁴ and +24.7 % at 10⁵.
  - RK4 in crack length `a` with 64 steps gave 2×10⁻⁵.
  - Life scales as Y⁻ᵐ (+5 % Y → −13.6 % life for m=3).
  - With the NASGRO normalization `((1−f)/(1−R))·ΔK`, the R<0 range convention cancels in the Paris term but not in the threshold term: with ΔK_th = 3 at R=−1, the two conventions gave lives of 2.03×10⁶ and 2.15×10⁶ cycles.
- **J-to-K conversion differs between the two fracture tools.** MOOSE's `JIntegral` converts `K = sign(J)·√(|J|·E/(1−ν²))`, which is plane strain and signed. crackpy converts `K_J = √(|J|·E)`, which is plane stress, non-negative, and includes a `/1000` unit factor. The ratio is 1/√(1−ν²) = 1.048 at ν = 0.3. crackpy's contour J uses the linear-elastic energy density `W = ½σ:ε` and aggregates contours by mean, median, and a median-absolute-deviation outlier filter with `m = 2`.
- **Two failure-assessment curves are compared, and they differ most beyond Lr = 1.** One is the legacy R6 Revision 3 Option 1 curve `(1 − 0.14Lr²)(0.3 + 0.7e^(−0.65Lr⁶))`, which secondary sources identify as the API 579-1/ASME FFS-1 Level 2 curve. The other is the BS 7910:2013 Option 1 curve. For the illustrative steel σy = 355 MPa, σu = 490 MPa, E = 207 GPa:
  - at Lr = 1.1 the curves give 0.433 and 0.332;
  - at Lr_max = 1.190 they give 0.329 and 0.215;
  - the radial reserve factor of the point (0.9, 0.6) is 1.060 and 1.052.
  - The normative texts were not examined; the curve equations come from secondary sources cited under Evidence.

## Applicability

Subjects, all pinned in `REPORT.json`:

| Subject | Revision | Role |
|---|---|---|
| `boschresearch/pylife` | `84685b82323b66b05cca530c51acbf1b7f2da895` (installed version string `2.3.1.post1.dev65+g84685b823`) | source + **execution** (pip-installed from that commit, Cython extension compiled) |
| `Gunnstein/fatpack` | `82d4aeef031f803d09edb1893a6c4587fa3adfd2` | source + **execution** (imported from source) |
| `iamlikeme/rainflow` | `5fc6822fd1c626739c6f95d9b4595ee80330b4fc` | source + execution; used as the ASTM E1049-85 §5.4.4 half-cycle reference, as the package itself claims. E1049-85(2017) is now marked historical; the active edition is E1049-85(2023) |
| `dlr-wf/crackpy` | `f5178fd4248adca457238ab55551444c1c7ae5ee` | source only |
| `idaholab/moose` | `1cb383aae1689b05b546a915340641517c43b190` | source only (`modules/solid_mechanics`) |

Relationships between the subjects:

- **fatpack, pyLife and `rainflow` are compared** as independent rainflow counters and damage summers.
- **crackpy and MOOSE are compared** as J-integral evaluators: crackpy works on DIC or FE full-field data with line integrals; MOOSE uses finite-element domain integrals.

Scope of the measured and derived material:

- **Execution inputs.** Synthetic seeded histories only:
  - the ASTM example `[−2, 1, −3, 5, −1, 3, −4, 4, −2]`;
  - AR(1) Gaussian sequences with ρ = 0.8, σ = 40 (or 25), seed 2026.
  - No measured service spectra were used.
- **Crack-growth and FAD numbers.** They come from the author's own implementation of published equations, with illustrative constants: C = 10⁻¹¹ m/cycle·(MPa√m)⁻ᵐ, m = n = 3, p = q = 0.25, Kc = 60 MPa√m, a₀ = 1 mm, a_f = 20 mm. They are not outputs of NASGRO, AFGROW, API 579 or BS 7910 software, and the constants are not material data.
- **Standards.** ASTM E1049-85, API 579-1/ASME FFS-1 and BS 7910 were **not examined directly**.
  - NUREG/CR-6983 (US NRC, 2008) states that E1049-85 contains two rainflow variants. In rainflow counting, ranges left uncounted are treated as half cycles. In simplified rainflow counting for repeating histories (Downing & Socie 1982), the history is rearranged to start at its extreme, which yields only full cycles.
  - So the half-cycle and full-cycle residue treatments compared below are *both* ASTM practices, chosen by whether the history repeats.
  - The ASTM §5.4.4 example counts come from the `rainflow` package's test file.
  - The FAD equations come from secondary literature (Evidence).

## Findings

### 1. Rainflow algorithms: shared criterion, divergent residue handling

All three counters implement the same closed-loop test, with ties counted as closed. Basis: source.

| Implementation | Closed-loop test | Residue handling | Location |
|---|---|---|---|
| fatpack `find_rainflow_cycles` | four-point: `dS2 <= dS1 and dS2 <= dS3` | returns the residue | `fatpack/rainflow.py:326` |
| fatpack `find_rainflow_ranges` | same | **residue concatenated with itself and recounted → full cycles** (repeating-history assumption, Marsh et al. 2016) | `rainflow.py:494-497` |
| pyLife `FourPointDetector` | `bc <= ab and bc <= cd` (Cython) | residuals stored in `detector.residuals`; not counted | `stress/rainflow/extension.pyx:79`; `fourpoint.py:161` |
| `rainflow.extract_cycles` (ASTM §5.4.4) | three-point with starting-point rule: a range containing the start counts as ½ and the start is discarded | remaining ranges counted as ½ cycles | `src/rainflow.py:97-111` |

ASTM example. The ASTM §5.4.4 result is `{3: ½, 4: 1½, 6: ½, 8: 1, 9: ½}`. Basis: execution.

- **pyLife** found one closed loop `(−1 → 3)`, range 4, and residuals `[−2, 1, −3, 5, −4, 4, −2, −2]`. Adding the residual reversals as half cycles reproduces the ASTM table exactly, plus one zero-range half cycle from the duplicated final sample.
- **fatpack `find_rainflow_ranges`** returned full cycles `{3, 4, 7, 9}` with `k = 10⁶`.
  - With the default `k = 64` they become `{3.094, 4.078, 7.031, 9.0}`, which is load-class quantization.
  - The range-7 cycle does not exist in the ASTM count. It arises from joining the residue with its own repetition.

### 2. Damage consequences of residue conventions and quantization

**Residue conventions.** Linear Basquin in range with no knee: `N = 2×10⁶·(100/ΔS)^m`. Each entry is the damage relative to ASTM half-cycle residue counting. Basis: execution.

| Samples | m | Closed only | Closed + ½ residue | fatpack repeated, `k = 10⁶` | fatpack repeated, default `k = 64` |
|---|---|---|---|---|---|
| 50 | 3 | 0.146 | 1.000 | 1.843 | 1.850 |
| 50 | 5 | 0.0135 | 1.000 | 1.986 | 1.987 |
| 200 | 3 | 0.441 | 1.000 | 1.101 | 1.093 |
| 200 | 5 | 0.256 | 1.000 | 1.284 | 1.274 |
| 1,000 | 5 | 0.521 | 1.000 | 1.024 | 1.020 |
| 10,000 | 5 | 0.857 | 1.000 | 1.011 | 1.015 |
| 100,000 | 3 | 0.986 | 1.000 | 1.000 | 1.001 |
| 100,000 | 5 | 0.962 | 1.000 | 1.001 | 1.003 |

Residue size: the pyLife residue had 5, 9, 17, 15 and 25 reversals at the five lengths, so it is not monotone in length. The residue always contains the largest excursion, so its share of damage rises with `m`.

Which convention is right depends on the use. Basis: derived + documentation (NUREG/CR-6983).

- Use **closed + ½ residue**, ASTM rainflow counting, for a one-off record.
- Use **repeated**, i.e. full-cycle residue as in ASTM simplified rainflow for repeating histories, when the record is one block of a repeating duty cycle.
  - fatpack reaches full cycles by concatenating the residue with itself, not by rearranging the history to start at its extreme.
  - Whether the two procedures agree for every history was not checked here.
- Never use **closed-only** for short blocks.

**Load-class quantization in fatpack.** `find_rainflow_ranges(y, k=64)` digitizes `y` into `k` classes of width `(ymax − ymin)/k`, from boundaries built with `dy = (ymax−ymin)/(2k)` (`rainflow.py:46`). On a 100,000-sample history, the damage relative to `k = 10⁶` was:

| k | m = 5 | m = 3 |
|---|---|---|
| 16 | 1.0237 | 1.0208 |
| 32 | 1.0021 | 1.0041 |
| 64 | 1.0004 | 1.0012 |
| 128 | 0.9998 | 1.0001 |

Basis: execution.

### 3. S–N knee handling and range/amplitude units

pyLife Wöhler curves are specified in **amplitude**:

- `SD` is the knee amplitude.
- The default `k_2` is `np.inf` (`materiallaws/woehlercurve.py:76`), meaning no damage below the knee.
- The three Miner variants set `k_2 = inf`, `k_2 = k_1`, or `k_2 = 2k_1 − 1` (`:184, 196, 208`).
- Damage is `cycles / N(amplitude)` (`strength/fatigue.py:116`).

fatpack endurance curves are specified in **stress range**:

- The defaults are Eurocode-style, `Nc = 2e6`, `Nd = 5e6`, `m1 = 3`, `m2 = 5` (`fatpack/endurance.py:279-282`).
- The tri-linear curve sets `N = ∞` below the cut-off `Sl` (`:401`).
- A 1-D input to `find_miner_sum` counts every range as one full cycle (`:129`); half cycles need the `(N, 2)` form.

Basis: source.

Test collective: 26,610 closed cycles from σ = 25, with `k_1 = 5`, `ND = 10⁶`, `SD = 50`; 97.2 % of amplitudes lie below `SD`. Basis: execution.

| Rule | Damage |
|---|---|
| pyLife Miner original (`k_2 = ∞`) | 2.524×10⁻³ |
| pyLife Miner Haibach (`k_2 = 9`) | 2.864×10⁻³ |
| pyLife Miner elementary (`k_2 = 5`) | 3.203×10⁻³ |
| fatpack `LinearEnduranceCurve(Sc=100 range, Nc=10⁶, m=5)` | 3.203×10⁻³ (identical to elementary) |
| fatpack `BiLinearEnduranceCurve(Sc=100, Nc=Nd=10⁶, m1=5, m2=9)` | 2.864×10⁻³ (identical to Haibach) |
| fatpack linear with the amplitude 50 entered as `Sc` | 0.1025 (= 32× elementary) |

The two independent codebases agree once units and knee conventions are aligned. The disagreement risk lies in the parameter mapping, not in the arithmetic.

### 4. Mean-stress corrections

Basis: source + execution.

- **fatpack Walker and Smith–Watson–Topper (SWT).** `(2Sm + S)^(1−γ)·S^γ`, with SWT as γ = ½. Both raise `ValueError("SWT and Walker stress correction not defined for Smax <= 0")` if **any** cycle has `Smax ≤ 0` (`stresscorrection.py:92`). A single compressive cycle therefore aborts the call for the whole array.
- **fatpack Morrow and Goodman.** Both are `S/(1 − Sm/sf)` (`:208`), with Goodman passing `su`. Measured: `Sm/su = 0.9` gives 10× and `0.998` gives 500×. The expression is singular at `Sm = su`, and its sign flips beyond that point without an error.
- **pyLife.** Provides FKM-Goodman (`meanstress.fkm_goodman(amplitude, meanstress, M, M2, R_goal)`) and five-segment Haigh transforms that map to a target `R` (`strength/meanstress.py:982, 1016`). Their behaviour was not executed here.

### 5. Crack-growth law integration

Basis: execution (own implementation of the published equations; not an upstream tool).

**Paris law, centre crack, constant amplitude.** ΔS = 100 MPa, Y = 1, analytic life `N = 881,834` cycles.

| Integrator | Relative life error |
|---|---|
| cycle-by-cycle explicit | +3×10⁻⁶ |
| forward Euler, block ΔN = 10 / 100 / 10³ / 10⁴ / 10⁵ | +3×10⁻⁵ / +3×10⁻⁴ / +3.6×10⁻³ / +3.2×10⁻² / +0.247 |
| RK4 in `a` (dN/da), 4 / 16 / 64 steps | +0.125 / +3.2×10⁻³ / +2.2×10⁻⁵ |

- **Integrate in `a`, not `N`.** `dN/da` is smooth, whereas fixed ΔN blocks overshoot because `da/dN` grows as `a^(m/2)`. Basis: derived.
- **Geometry factor.** The Feddersen finite-width factor `√sec(πa/W)` with W = 100 mm shortens life to 0.973× the value for Y = 1. A uniform +5 % on Y gives 0.8638×, equal to `1.05⁻³`.

**Newman closure and NASGRO.** The equations as implemented (Basis: documentation, secondary + the FAA report):

```text
NASGRO (FAA DOT/FAA/AR-05/15 eq. 1; first published by Forman & Mettu 1992):
  da/dN = C [((1 − f)/(1 − R)) ΔK]^n (1 − ΔKth/ΔK)^p / (1 − Kmax/Kc)^q
Newman (1984) crack-opening function, σ0 = flow stress, α = constraint factor:
  f = max(R, A0 + A1 R + A2 R² + A3 R³)            R ≥ 0
  f = A0 + A1 R                                     R < 0   (NASGRO applies it for −2 ≤ R < 0)
  A0 = (0.825 − 0.34α + 0.05α²)[cos(π Smax/(2σ0))]^(1/α),   A1 = (0.415 − 0.071α) Smax/σ0
  A3 = 2A0 + A1 − 1,   A2 = 1 − A0 − A1 − A3
```

At Smax/σ0 = 0.3, `f` gives the effective-range factor `U = (1−f)/(1−R)` below.

| R | α = 1 (plane stress) | α = 2 | α = 3 (plane strain) |
|---|---|---|---|
| −1.0 | 0.313 | 0.378 | 0.408 |
| 0.0 | 0.523 | 0.674 | 0.755 |
| 0.1 | 0.566 | 0.731 | 0.820 |
| 0.5 | 0.748 | 0.904 | 0.990 |
| 0.7 | 0.845 | 0.958 | 1.000 |

The constraint factor α is therefore a first-order input: at R = 0.1, U ranges from 0.566 to 0.820, which is 3.0× in rate for n = 3.

NASGRO lives (α = 2, ΔK_th = 0 unless stated, Smax = 100 MPa):

| Case | Life (cycles) |
|---|---|
| R = 0.1 | 2.94×10⁶ |
| R = 0.5 | 9.08×10⁶ |
| R = 0.1, ΔK_th = 3 | 3.33×10⁶ |
| R = 0.1, ΔK_th = 5 | 4.10×10⁶ |
| R = −1, full-range ΔK | 1.94×10⁶ |
| R = −1, positive-part ΔK | 1.94×10⁶ |
| R = −1, ΔK_th = 3, full-range | 2.03×10⁶ |
| R = −1, ΔK_th = 3, positive-part | 2.15×10⁶ |
| R = 0.1, Kc = 60 (vs Kc → ∞) | 2.94×10⁶ (vs 3.10×10⁶) |
| R = 0.1, Kc = 30 | 2.75×10⁶ |

`Kmax(a_f) = 25.1 MPa√m`, so the fracture asymptote `(1 − Kmax/Kc)^q` still shortens life by 5 % at Kc = 60, although failure is never reached.

**Threshold truncation in spectra.** Block of 1 cycle at ΔS = 100 plus 50 cycles at ΔS = 20. Basis: execution (own implementation).

| ΔK_th | Life | Note |
|---|---|---|
| 0 | 3.21×10⁷ | |
| 2 | 4.34×10⁷ | |
| 4 | 5.20×10⁷ | |
| 6 | no growth | even the large cycle starts below threshold at a₀ = 1 mm |

Linear summation with a threshold turns a small change in ΔK_th into an unbounded change in life. Retardation and acceleration from overloads and underloads (sequence effects) are not represented by any of these cycle-independent laws; Elber-type closure models are needed for that.

### 6. J-integral evaluation: MOOSE domain integrals vs crackpy line integrals

**MOOSE** (`modules/solid_mechanics`). Basis: source.

- **Integrand.** `JIntegral::computeQpIntegral` contracts the Eshelby tensor with the gradient of the vector q-field: `eq = Σ : ∇(q·crack_direction)` (`src/vectorpostprocessors/JIntegral.C:144`). It adds a thermal term, then divides by the mean of the forward and backward crack-front segment lengths in 3D: `return etot / q_avg_seg;` (`:167`).
- **Symmetry and K.** `finalize()` doubles J for a symmetry plane (`:229`). For `KFromJIntegral` it computes `K = sign(J)·√(|J|·E/(1−ν²))` (`:234-235`), the **plane-strain** relation, regardless of a 2D plane-stress model.
- **q-function.** The `Geometry` q-function is 1 inside `r_inner`, linear to 0 at `r_outer`, and 0 beyond (`src/auxkernels/DomainIntegralQFunction.C:75-81`). It is multiplied in 3D by a tent function along the front tangent (`:85-106`), and set to 0 on intersecting free surfaces unless the front point itself lies there (`:109-111`).
- **Rings.** These are lists `radius_inner/radius_outer` (Geometry) or `ring_first..ring_last` element layers (Topology) (`src/actions/DomainIntegralAction.C:199-220`).
- **Front direction.** Set by `CrackDirectionVector`, `CrackMouth` or `CurvedCrackFront` (`src/userobjects/CrackFrontDefinition.C:44`).

**crackpy.** Basis: source.

- **Contours.** The fracture-analysis pipeline integrates on multiple rectangular contours around the tip.
- **Energy density.** `in_plane_j_integral_terms` uses the linear-elastic energy density `strain_energy_density = 0.5 * np.einsum(...)` (`fracture_analysis/functionals/j_integral.py:41`).
- **K from J.** `K_J = np.sqrt(np.abs(j_integral) / 1000.0 * youngs_modulus)` (`:139`). The docstring cites Breitbarth et al. 2019 eq. 10 for plane stress and states the absolute value is taken.
- **Aggregation.** Contour results are reduced by `np.nanmean`, `np.nanmedian`, and `mean_wo_outliers(m=2)` (`fracture_analysis/analysis.py:433-451, 528-535`). The outlier filter rejects values whose deviation from the median exceeds 2× the median absolute deviation.

**Consequences.** Basis: derived.

- **Conversion and units.** The same J gives K values that differ by the factor `1/√(1−ν²)`: +4.8 % for MOOSE vs crackpy at ν = 0.3. crackpy's `/1000` assumes J in N/mm and E in MPa, giving K in MPa√m. MOOSE is unit-agnostic.
- **Sign.** crackpy discards the sign of J; MOOSE propagates it into K. A negative J signals a path or direction error, which only MOOSE surfaces.
- **Path independence.** Both J forms are path-independent only for hyperelastic (deformation-theory) response. With incremental plasticity, unloading, or non-proportional loading, contour values drift with radius.
  - crackpy's linear-elastic `W` makes this explicit inside the plastic zone.
  - Its MAD filter can hide a systematic radial trend as "outliers".
  - The MOOSE ring sequence should be inspected for convergence rather than averaged.

### 7. Failure Assessment Diagrams

Option-1 curves as implemented here. Basis: documentation (secondary) + execution (own implementation).

```text
R6 Rev.3 Opt.1 / API 579-1 L2:  Kr = (1 − 0.14 Lr²)(0.3 + 0.7 exp(−0.65 Lr⁶)),  Lr ≤ Lr_max
BS 7910 Option 1:  Kr = (1 + ½ Lr²)^(−½) [0.3 + 0.7 exp(−μ Lr⁶)],  Lr ≤ 1,  μ = min(0.001 E/σy, 0.6)
                   Kr = f(1) · Lr^((N−1)/(2N)),                     1 < Lr ≤ Lr_max,  N = 0.3(1 − σy/σu)
Lr_max = (σy + σu)/(2σy)
```

Attribution of these forms. Basis: documentation (secondary).

- **`(1 − 0.14Lr²)…` curve.** It is the API 579-1/ASME FFS-1 Level 2 curve (Manu et al. 2025, eq. 9) and the BS 7910:2005 "Level 2A" curve (Chen et al. 2026, eq. 1). It originates as R6 Revision 3 Option 1. R6 Revision 4 slightly modified Option 1 for consistency with Option 2 at low Lr (Sharples et al. 2003), so it should not be called simply "R6 Option 1".
- **BS 7910:2013 Option 1 μ/N form.** It is taken from non-peer-reviewed technical summaries (TWI; an NDT vendor page) and was not checked against the standard.

| Lr | R6 Rev.3 Opt.1 / API 579-1 L2 | BS 7910:2013 Opt 1 (σy 355, σu 490, E 207 GPa; μ = 0.583, N = 0.083) |
|---|---|---|
| 0.2 | 0.994 | 0.990 |
| 0.5 | 0.958 | 0.937 |
| 0.8 | 0.811 | 0.784 |
| 1.0 | 0.572 | 0.564 |
| 1.1 | 0.433 | 0.332 |
| 1.190 (= Lr_max) | 0.329 | 0.215 |

- **Where the curves diverge.** Below Lr = 1 the two curves differ by at most 0.03 here. Beyond Lr = 1, the BS 7910 branch encodes the material's low strain-hardening (small N), whereas the R6 Rev. 3 / API 579-1 Level 2 form does not. The plastic-collapse cutoff `Lr_max` is a hard vertical boundary in both.
- **Reserve factors.** The radial reserve factor for the point (Lr, Kr) = (0.9, 0.6) was 1.060 (R6 Rev. 3 / API 579-1 Level 2) and 1.052 (BS 7910:2013 Option 1).
- **Secondary stresses.** Thermal and residual stresses enter Kr through the plasticity-interaction term (ρ in R6, V in BS 7910) and not Lr. The secondary contribution is therefore not bounded by the collapse cutoff. Its formulas were not examined here.

### 8. Performance and resource footprint (L1–L6)

| Level | Measurement |
|---|---|
| L1 | not measured |
| L2 | pyLife from source: `pip install git+…@84685b82` (including prebuilt numpy/pandas/scipy/h5py binary packages and the Cython extension build) took 67.0 s wall, 342,964 kB peak RSS (pip process tree's largest process). fatpack and `rainflow` are pure Python (no build). MOOSE and crackpy: not measured. |
| L3 | not applicable |
| L4 | Counting throughput on 10⁶ AR(1) samples, best of 3, 1 thread: pyLife four-point (Cython) 0.025 s (≈ 40 Msamples/s); fatpack `find_rainflow_ranges` 1.05 s with `k = 64` and 0.89 s with `k = 10⁶` (≈ 1 Msample/s); `rainflow.extract_cycles` 0.66 s (≈ 1.5 Msamples/s). Whole residue/knee probe: 6.5 s. Crack/FAD toy: 3.2 s. MOOSE/crackpy runtime: not measured. |
| L5 | not applicable |
| L6 | Probe peak RSS: residue/knee 148,948 kB; benchmark 196,416 kB; crack/FAD toy 24,216 kB. Installed package sizes not measured. |

Host for all rows: 96-vCPU Intel Xeon 2.60 GHz VM, Python 3.13.15. Basis: execution.

### 9. Comprehensibility (C1) and simplicity / model refinement (C2)

**C1, comprehensibility.**

- **Load-bearing conventions are implicit.** A reader must hold four independent conventions to get one damage number: residue handling, range vs amplitude, knee slope, and load-class count `k`. None of them is visible in a `find_miner_sum(S)` or `damage(collective)` call.
  - fatpack's default `find_rainflow_ranges` silently adopts the repeating-history convention and 64-class quantization.
  - pyLife's detector silently omits the residue.
  - A user switching libraries changes damage by up to 2× for short blocks and 32× for a unit slip, with no warning.
- **Crack growth.** α, R-sign conventions and threshold placement are similarly invisible in a single `da/dN` call.
- **J to K.** The plane-strain vs plane-stress choice is buried in `finalize()` (MOOSE) or a helper (crackpy).

**C2, simplicity and model refinement.**

- **Residue.** The three residue behaviours are one parameter, a boundary condition on the history (`once` / `periodic` / `ignore`). Exposing that parameter explicitly, as `rainflow`'s half-cycle output effectively does, makes the "exceptions" ordinary cases. That would sit naturally in both libraries' cycle output with no change to the four-point core.
- **S–N curves.** Range vs amplitude is a unit, and units belong in types, not in parameter names. The fatpack bilinear curve with `m2 = 2m1 − 1` *is* Miner–Haibach, so two mechanisms enforce one invariant.
- **J to K.** It should take the constraint state as an explicit argument.

### 10. Validation (V1–V4)

- **V1, specification adequacy and non-vacuity.**
  - The ASTM §5.4.4 example is a minimal oracle. Only the `rainflow` package tests against it, in `tests/test_rainflow.py` `TEST_CASE_1`.
  - fatpack's docstrings reference ISO 12110-2. Its tests were not run here.
  - Per-cycle agreement across implementations (§1) is a cheap differential oracle.
  - Damage agreement after convention alignment (§3) is a non-vacuity check that the mapping, not the arithmetic, is the risk.
- **V2, differential testing.**
  - A metamorphic invariant: appending a history to itself must double damage under the periodic convention but not under closed-only.
  - The pyLife residual duplication (§Summary) was found by feeding one library's output to another.
  - MOOSE vs crackpy on the same FE field would test the K-conversion and path effects. It was **not run**.
- **V3.** Not applicable; no concurrency or hardware is involved.
- **V4, plant falsification.**
  - Miner sums, NASGRO lives and FAD margins are validated in practice against coupon and component test data and service experience. None was examined.
  - Sequence effects are a known falsifier of linear damage summation: for example, multiple-site fatigue in the 1988 Aloha Airlines B737 fuselage failure (NTSB/AAR-89/03). Basis: documentation.

## Boundaries

- **Not examined.**
  - Running MOOSE or crackpy.
  - pyLife FKM nonlinear and three-point/FKM detectors.
  - fatpack `racetrack` filtering.
  - pyLife and fatpack mean-stress transforms at scale.
  - Multiaxial counting.
  - Measured service spectra.
  - NASGRO-software coefficient sets.
  - BS 7910/API 579 plasticity-interaction (V/ρ) formulas and Level 3 options.
  - Weld residual-stress profiles.
- **Unknown.**
  - Whether pyLife's duplicated final residual under `flush=True` is intended. The docstring describes residuals as turning points not yet closed.
  - Whether ISO 12110-2 or the full ASTM E1049 text prescribes the same residue treatment as the `rainflow` package's §5.4.4 reading.
- **Known not to apply.**
  - The crack-growth and FAD numbers are properties of the illustrative constants, not of any alloy or code-certified software.
  - The residue ratios apply to the synthetic AR(1) histories.
- **Unsupported.** fatpack SWT/Walker for any cycle with `Smax ≤ 0` (raises).
- **Not established.**
  - That any one residue convention is universally conservative: closed-only is unconservative, and periodic can over-count for one-off records.
  - That FAD reserve factors computed with Option-1 curves meet any code's acceptance criteria, which carry partial safety factors not modelled here.

## Evidence

Observation date: all evidence was acquired on 2026-11-20 (UTC). The pins are `HEAD` commits on that date, except `rainflow`, whose latest commit is dated 2023-04-17.

Pinned sources (paths relative to repository root):

- `Gunnstein/fatpack` @ `82d4aeef031f803d09edb1893a6c4587fa3adfd2` (commit 2025-02-10).
  - `fatpack/rainflow.py:36-49, 138-198, 201-262, 265-333, 446-513`
  - `fatpack/endurance.py:82-134, 198-212, 279-315, 387-408`; `fatpack/stresscorrection.py:31-94, 158-208`
- `boschresearch/pylife` @ `84685b82323b66b05cca530c51acbf1b7f2da895` (commit 2026-10-28).
  - `src/pylife/stress/rainflow/fourpoint.py:142-165`; `src/pylife/stress/rainflow/extension.pyx:33-94`
  - `src/pylife/stress/rainflow/general.py:255-329`; `src/pylife/materiallaws/woehlercurve.py:74-94, 175-208, 263-316, 358-366`
  - `src/pylife/strength/fatigue.py:87-117`; `src/pylife/strength/miner.py:234-305`; `src/pylife/strength/meanstress.py:982-1016`
- `iamlikeme/rainflow` @ `5fc6822fd1c626739c6f95d9b4595ee80330b4fc`.
  - `src/rainflow.py:62-112`; `tests/test_rainflow.py:15-38`
- `dlr-wf/crackpy` @ `f5178fd4248adca457238ab55551444c1c7ae5ee` (commit 2026-09-25).
  - `crackpy/fracture_analysis/functionals/j_integral.py:8-50, 109-140`
  - `crackpy/fracture_analysis/analysis.py:339-535`; `CITATION.cff`
- `idaholab/moose` @ `1cb383aae1689b05b546a915340641517c43b190` (commit 2026-11-20).
  - `modules/solid_mechanics/src/vectorpostprocessors/JIntegral.C:124-167, 222-240`
  - `modules/solid_mechanics/src/auxkernels/DomainIntegralQFunction.C:68-134`
  - `modules/solid_mechanics/src/actions/DomainIntegralAction.C:54-58, 199-220`
  - `modules/solid_mechanics/src/userobjects/CrackFrontDefinition.C:44-56`

Literature. Each DOI was checked against publisher or index metadata on the observation date.

- Miner, "Cumulative damage in fatigue," *J. Appl. Mech.* 12(3):A159–A164, 1945, doi:10.1115/1.4009458.
- Paris & Erdogan, "A critical analysis of crack propagation laws," *J. Basic Eng.* 85(4):528–533, 1963, doi:10.1115/1.3656900.
- Rice, "A path independent integral …," *J. Appl. Mech.* 35(2):379–386, 1968, doi:10.1115/1.3601206.
- Elber, "The significance of fatigue crack closure," in *Damage Tolerance in Aircraft Structures*, ASTM STP 486, pp. 230–242, 1971, doi:10.1520/STP26680S.
- Downing & Socie, "Simple rainflow counting algorithms," *Int. J. Fatigue* 4(1):31–40, 1982, doi:10.1016/0142-1123(82)90018-4.
- Newman, "A crack opening stress equation for fatigue crack growth," *Int. J. Fract.* 24(4):R131–R135, 1984, doi:10.1007/BF00020751. The DOI was verified, but the text was not read; the closure coefficients were checked against secondary sources (FAA report below; Meyer, MSc thesis, Chalmers 2014).
- Ainsworth, "The assessment of defects in structures of strain hardening material," *Eng. Fract. Mech.* 19(4):633–642, 1984, doi:10.1016/0013-7944(84)90096-1.
- Shih, Moran, Nakamura, "Energy release rate along a three-dimensional crack front in a thermally stressed body," *Int. J. Fract.* 30(2):79–102, 1986, doi:10.1007/BF00034019. This is the domain-integral basis.
- Williams, "On the stress distribution at the base of a stationary crack," *J. Appl. Mech.* 24(1):109–114, 1957, doi:10.1115/1.4011454.
- Forman & Mettu, "Behavior of surface and corner cracks subjected to tensile and bending loads in Ti-6Al-4V alloy," in *Fracture Mechanics: Twenty-Second Symposium (Vol. I)*, ASTM STP 1131, pp. 519–546, 1992. No DOI was found; a DOI sometimes attributed to this chapter resolves to an unrelated paper.
- Forman, Shivakumar, Cardinal, Williams, McKeighan, *Fatigue Crack Growth Database for Damage Tolerance Analysis*, FAA report DOT/FAA/AR-05/15, Aug. 2005. Its eq. 1 is the NASGRO equation, with "f is Newman's crack opening function".
- Amzallag, Gerey, Robert, Bahuaud, "Standardization of the rainflow counting method for fatigue analysis," *Int. J. Fatigue* 16(4):287–293, 1994, doi:10.1016/0142-1123(94)90343-3.
- Marsh et al., "Review and application of Rainflow residue processing techniques for accurate fatigue damage estimation," *Int. J. Fatigue* 82:757–765, 2016, doi:10.1016/j.ijfatigue.2015.10.007.
- Breitbarth, Strohmann, Besel, Reh, "Determination of stress intensity factors and J integral based on digital image correlation," *Frattura ed Integrità Strutturale* 49:12–25, 2019, doi:10.3221/IGF-ESIS.49.02. This is cited in crackpy's `K_J` docstring.
- Strohmann et al., "Next generation fatigue crack growth experiments of aerospace materials," *Sci. Rep.* 14:14075, 2024, doi:10.1038/s41598-024-63915-x (crackpy `CITATION.cff`). The README instead asks for Zenodo doi:10.5281/zenodo.7319653 (v1.0.0; concept DOI 10.5281/zenodo.7319652).
- Manu et al., *Materials* 18(23):5407, 2025, doi:10.3390/ma18235407 (API 579-1 Level 2 curve, eq. 9); Chen et al., *Materials* 19(3):465, 2026, doi:10.3390/ma19030465 (BS 7910 Level 2A curve, eq. 1).
- Sharples, Ainsworth, Budden, Dowling, "Developments in UK defect assessment procedures R6 Revision 4 and BS7910," Proc. SDSMS'03, 2003. It describes the Revision 4 change to Option 1.
- US NRC, NUREG/CR-6983, 2008 (the two E1049 rainflow variants and their residue treatment).
- NTSB, Aircraft Accident Report NTSB/AAR-89/03 (Aloha Airlines Flight 243, Boeing 737-200, N73711, April 28, 1988), adopted June 14, 1989.

Standards, none examined directly:

- ASTM E1049-85 (Reapproved 2017), doi:10.1520/E1049-85R17, now historical; active E1049-85(2023), doi:10.1520/E1049-85R23.
- API 579-1/ASME FFS-1; BS 7910:2013/2019; R6 (Revisions 3 and 4).

Execution:

```bash
python3 -m venv venv && venv/bin/pip install numpy
venv/bin/pip install "git+https://github.com/boschresearch/pylife@84685b82323b66b05cca530c51acbf1b7f2da895"
# fatpack and rainflow imported from source trees checked out at the pinned commits:
PYTHONPATH=fatpack:rainflow/src venv/bin/python rainflow_probe.py
```

Probe definitions. These are self-contained; re-implement from this text.

- **History.** `x[0]=e0; x[i]=0.8·x[i−1]+0.6·e[i]` with `e ~ N(0,1)` from `numpy.random.default_rng(2026)`, scaled by σ = 40. Lengths of 50, 200, 1,000, 10,000 and 100,000 samples are drawn sequentially from the same generator.
- **ASTM reference.** `rainflow.extract_cycles(y)` gives `(range, count)`.
- **Closed-only.** `FourPointDetector().process(y, flush=True).recorder.collective`, with range `|to − from|`.
- **Closed + ½ residue.** The closed loops plus `0.5` for each `|diff(detector.residuals)|`.
- **fatpack.** `find_rainflow_ranges(y, k)` with `k` ∈ {64, 10⁶}.
- **Damage.** `Σ count / (2e6·(100/ΔS)^m)`.
- **Knee test.** σ = 25; the pyLife `pd.Series({'k_1':5,'ND':1e6,'SD':50}).fatigue.miner_*().damage(collective)` is compared with `fatpack.LinearEnduranceCurve(100)` (`Nc=1e6, m=5`) and `BiLinearEnduranceCurve(100)` (`Nc=Nd=1e6, m1=5, m2=9`).
- **pyLife residual duplication.** `FourPointDetector().process([−2,1,−3,5,−1,3,−4,4,−2], flush=True).residuals` returns `[−2,1,−3,5,−4,4,−2,−2]`. With `flush=False` it returns `[−2,1,−3,5,−4,4,−2]`. `fatpack.concatenate_reversals(r, r)` on the former raises `ValueError: Input must be reversals, end/start value of reversals1/reversals2 repeated.`

## Revalidation

- **Residue conventions.** Rerun the ASTM example through all three libraries; it takes under 1 s. If fatpack's `find_rainflow_ranges` still returns `{3,4,7,9}` full cycles and pyLife still returns one closed loop, the §2 ratios hold qualitatively. Rerun the AR(1) table to refresh the magnitudes.
- **pyLife duplication.** Check `fourpoint.py` lines 143–147 and `general.py` `_flush_new_turns`. The single-line check above suffices.
- **Knee mapping.** Check `woehlercurve.py` for the `k_2` defaults and the three `miner_*` setters, and `endurance.py` for the class defaults.
- **J-to-K conventions.**
  - `grep -n "_youngs_modulus /" modules/solid_mechanics/src/vectorpostprocessors/JIntegral.C`
  - `grep -n "np.sqrt(np.abs(j_integral)" crackpy/fracture_analysis/functionals/j_integral.py`
- **Crack-growth and FAD toy.** These are deterministic and depend only on the equations quoted in §5 and §7. If a standard's curve coefficients change, recompute the FAD table directly from the new equations.
