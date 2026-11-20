# BART Undersampled k-Space Reconstruction Stability, Pulseq/SAFE Gradient-Stimulation Prediction, and RTK/ASTRA Cone-Beam FDK Geometry Sensitivity

## Summary

- **BART `pics` normalizes the data by a data-dependent scale before applying the regularization weight, and the scale rule is discontinuous.** `pics` divides k-space by `scale = p90` if `(max − p90) < 2·(p90 − median)` else `max`, computed from the magnitude-sorted root-sum-of-squares image of a central 32³ calibration block (`src/sense/optcom.c` line 94). For degree-1-homogeneous penalties (ℓ1-wavelet, TV) the solution in data units equals the solution of the unscaled problem with `λ_eff = λ·scale`, so the effective regularization jumps when the branch flips. Measured on a 128×128, 8-coil BART phantom: a **9.6×10⁻⁸ relative k-space change** flipped the scale from 936.6 (max branch) to 402.5 (p90 branch) and changed the rescaled (`-S`) ℓ1-wavelet output by **2.74 %** (amplification ≈ 2.9×10⁵). With a fixed `-w` scale, the same pair of inputs changes the output by ≤ 7.7×10⁻⁷ relative, and for Tikhonov or unregularized CG the automatic scale is mathematically irrelevant (measured output change 2×10⁻⁶ and 4×10⁻⁶).
- With no `-r`/`-R` option, `pics` runs **unregularized SENSE by conjugate gradients for 30 iterations**; early stopping is the only regularizer. With `-r λ` and no `-R`, it adds an ℓ2 image penalty. The default IST/FISTA/primal-dual step size is 0.95, which assumes unit-normalized coil maps; `pics` only warns when the maps' maximum root-sum-of-squares is outside [0.95, 1.05].
- **The random-direction perturbation ratios measured here are not Antun-style worst-case instabilities.** For random k-space noise at an effective acceleration of 3.73, the relative-output/relative-input ratio was 1.95–2.00 (CG), 1.41–1.44 (Tikhonov), 0.41–0.43 (ℓ1-wavelet) and 0.32–0.33 (TV). A single bright pixel raised the automatic scale 3.8× and raised the ℓ1-wavelet error *outside* that pixel's 7×7 neighbourhood from 0.049 to 0.115.
- **SAFE peripheral-nerve-stimulation (PNS) prediction is a per-axis sum of three discrete first-order low-pass filters, normalized to `stim_limit`.** The `safe_pns_prediction` code discretizes the filter as `α = dt/(τ + dt)`. Pulseq's `calcPNS` combines the axes with an L2 norm and declares `ok` iff the norm stays below 1, that is below 100 % of `stim_limit`. The code reads `stim_thresh` but never uses it. `safe_gwf_to_pns` calls `safe_hw_check(hw)` and discards the result, so a hardware specification whose `a1 + a2 + a3 ≠ 1` is silently accepted. In a numpy transcription run on the repository's fictional example hardware, that discretization reads 0.6–1.0 percentage points (pp) lower at 10 µs than an exact zero-order-hold first-order filter.
- **Pulseq's `checkTiming` does not check gradient amplitude or slew rate.** Those limits are enforced per channel when gradient events are created. `testReport` also computes the rotation-invariant vector norms and only annotates them `[EXCEEDED]`. Pulseq has no SAR model: `mr.calcRfPower` returns relative Hz²·s energy and states that absolute SAR needs coil- and subject-specific scaling.
- **RTK and ASTRA both build the FBP ramp kernel in the spatial domain** (`h[0] = 1/4`, `h[odd n] = −1/(πn)²`, even taps zero) and then transform it. That avoids the zero-DC defect of a naively sampled `|f|` ramp; in a toy parallel-beam FBP, the naive ramp biased a uniform disk by −6.4 % without padding. ASTRA's CUDA FDK takes its cosine weights from the first projection only and indexes `u` from the detector-array centre; the code documents this restriction but does not enforce it for arbitrary `cone_vec` geometries. RTK weights each projection with its own offsets and tilt, and offers Ohnesorge-style mirror extension for lateral truncation.

## Applicability

Subjects, all pinned in `REPORT.json`:

| Subject | Revision | Role in this report |
|---|---|---|
| `mrirecon/bart` | `731bfd3ec4f09ffa59b497ded1274a2c0357c8af` (`bart version` → `v1.0.00-1-g731bfd3`) | source + **execution** (built from source and run) |
| `pulseq/pulseq` | `11e459d9b6b426aa6ea57a01153fb9afea332f6f` | source only (MATLAB, not executed) |
| `filip-szczepankiewicz/safe_pns_prediction` | `152ab67c086170c40c1988ebba9002e018a0652c` | source + execution of a numpy *transcription* (MATLAB not executed) |
| `RTKConsortium/RTK` | `3f6b9e185a97af546b2eb4dcd9c7bfdbc3a45c96` | source only (ITK-based C++, not built) |
| `astra-toolbox/astra-toolbox` | `627d834ce2339b505d098c205f0293a401faf6b4` | source only (CUDA FDK, not built; no GPU used) |

How the subjects relate:

- **Three independent pipelines are covered.**
  - The MRI reconstruction stage is BART.
  - The MRI exposure-prediction stage is Pulseq's `calcPNS` calling `safe_pns_prediction` functions.
  - The CT reconstruction stage is RTK and ASTRA.
- **Pulseq and SAFE are a combination.** `calcPNS.m` calls `safe_gwf_to_pns` directly, and findings about the PNS verdict concern that composition.
- **RTK and ASTRA are compared.** They are independent implementations of the same Feldkamp–Davis–Kress (FDK) algorithm.

BART execution scope:

- Build: CPU only, OpenBLAS 0.3.32 + LAPACKE 3.12.1 + FFTW 3.3.11, `PNG=0`.
- Data: 2D Cartesian data only, from BART's own analytic Shepp–Logan phantom (`bart phantom`, 128×128, 8 simulated coils).
- Sampling: Poisson-disc masks from `bart poisson` (no variable density, 20×20 fully sampled centre).
- Coil maps: ESPIRiT maps from `bart ecalib -m1` with default kernel 6³, calibration 24³, threshold 0.001 and crop 0.8.
- Threads: `OMP_NUM_THREADS=1` unless stated otherwise.
- Not covered: non-Cartesian (`-t`) and GPU behaviour; the BART learned-reconstruction tools (`nlinvnet`, `reconet`).

Scope of the toy and transcription results:

- **SAFE transcription.** It covers the model as coded at the pinned SAFE revision, with the repository's own fictional example hardware (`safe_example_hw_peripheral.m` says "not a real scanner"). It does not predict stimulation on any real MR system.
- **CT toy.** It is a 2D parallel-beam numpy FBP with analytic projections. It reuses two formulas transcribed from RTK and ASTRA; it is not RTK or ASTRA.

Scope of the standards:

- The numerical regulatory limits are taken from secondary sources, cited under Evidence.
- The text of IEC 60601-2-33 and IEC 60601-2-44 was **not examined directly**; it is paywalled.
- Findings about *code behaviour* do not depend on those values.

## Findings

### 1. BART `pics`: problem, defaults, and algorithm selection

`pics` solves a SENSE-type problem:

```text
x̂ = argmin_x  ½‖P F S x − y/s‖²  +  Σ_i λ_i R_i(T_i x)        (output = x̂, or s·x̂ with -S)
  P: sampling pattern (estimated from non-zero k-space if no -p),  F: FFT (or NUFFT with -t),
  S: coil maps,  s: data scale (automatic unless -w),  R_i: penalties from -R / -l1 / -l2 / -r
```

Basis: source.

| Behaviour | Location (bart @731bfd3e…) | Consequence |
|---|---|---|
| `int maxiter = 30;` | `src/pics.c:82` | Default iteration cap for every algorithm. |
| `if (-1. == lambda) lambda = 0.;` then, when no `-R` is given and `λ > 0`, `regs[0].xform = L2IMG` | `src/grecon/optreg.c:378-379, 388` | No `-r` means no penalty; `-r λ` alone means Tikhonov. |
| `italgo_choose`: starts at `ALGO_CG`; TV/TGV/ICTV/ICTGV/IMAGL1/IMAGL2 → `ALGO_ADMM`; any other first penalty → `ALGO_FISTA`; later non-ℓ2 penalties → ADMM | `src/grecon/italgo.c:32, 54, 59, 61` | Plain `pics` = CG with 30 iterations (early stopping is the only regularizer). |
| `step = 0.95` if unset, for IST/FISTA/PRIDU | `src/pics.c:658` | Assumes ‖PFS‖ ≤ ~1, i.e. maps with unit RSS. |
| Warning "coils are likely not normalized" if max RSS ∉ [0.95, 1.05] | `src/pics.c:653-654` | Only a warning; the run proceeds. |
| Warning "No step size specified for non-Cartesian trajectory" | `src/pics.c:634` | Non-Cartesian FISTA needs `-s` or `-e`. |
| Automatic scale: Cartesian `estimate_scaling(ksp_dims, NULL, kspace, -1)`; non-Cartesian `estimate_scaling_norm` on the adjoint image | `src/pics.c:505, 513` | The data is divided by `s` (`src/pics.c:529`); a zero scale is replaced by 1 with a warning (`:521`). |
| `-w` sets the scale explicitly; `-S` multiplies the output back by it | `src/pics.c:180-181` | Use `-w` to make λ absolute and `-S` to get data units. |

### 2. The scaling rule makes the effective ℓ1/TV weight data-dependent and discontinuous

`estimate_scaling_norm` (`src/sense/optcom.c:88-94`) sorts the magnitudes of the low-resolution image, then applies:

```c
float median = cabsf(tmpnorm[imsize / 2]) / rescale;
float p90 = cabsf(tmpnorm[(int)trunc(imsize * 0.9)]) / rescale;
float scale = ((max - p90) < 2 * (p90 - median)) ? p90 : max;
```

Here the image is the RSS combination of the central `cal_size = {32, 32, 32}` block (`:151`).

**Homogeneity argument.** Basis: derived.

- For a penalty with `R(cx) = |c| R(x)`, which covers ℓ1-wavelet and TV, `argmin_x ½‖Ax − y/s‖² + λR(x)` equals `(1/s)·argmin_z ½‖Az − y‖² + λ s R(z)`. The reconstruction in data units therefore uses `λ_eff = λ·s`.
- For a quadratic penalty, `R(cx) = c²R(x)`, the factor cancels: `s·x̂ = (AᴴA + λI)⁻¹Aᴴy` is independent of `s`.
- Unregularized CG is likewise scale-free in exact arithmetic.

Because `s` switches between two order statistics at a hypersurface in data space, `y ↦ s·x̂(y)` is discontinuous there whenever an ℓ1/TV penalty is active.

**Execution (BART at the pinned revision).** Basis: execution.

- **Input family.** A one-parameter family of k-space data was built: phantom coil images plus `c · interior-mask · true-coil-maps`, then Poisson-disc undersampling at 26.8 % sampled. Bisection on `c` found `c_lo = 2.0337552e-4` and `c_hi = 2.0337561e-4`; the relative k-space difference between the two inputs is 9.59×10⁻⁸.
- **Scale at the two inputs.** `pics -d 3` printed:
  - `Scaling: 936.629395! (max = 936.629395/p90 = 402.521820/median = 135.468063)` at `c_lo`;
  - `Scaling: 402.521851  (max = 936.629395/p90 = 402.521851/median = 135.468048)` at `c_hi`.
  - The `!` marks the max branch.

| `pics` configuration on the two inputs | Relative output change ‖x_b − x_a‖/‖x_a‖ |
|---|---|
| `-S -l1 -r 0.01` (automatic scale, data units) | **2.74×10⁻²** |
| `-S -l1 -r 0.003` | 2.37×10⁻² |
| `-S -l1 -r 0.001` | 2.26×10⁻² |
| `-l1 -r 0.01 -w 936.629395` (fixed scale) | 6.1×10⁻⁷ |
| `-l1 -r 0.01 -w 402.521851` (fixed scale) | 7.7×10⁻⁷ |
| `-S -l2 -r 0.01` (automatic scale) | 2×10⁻⁶ |
| `-S -i 30` (CG, automatic scale) | 4×10⁻⁶ |

At this operating point the two branches also produced different accuracy: magnitude NRMSE against the RSS reference was 0.0482 (max branch) and 0.0345 (p90 branch). Without `-S`, the raw output changes by 135 % because the output is in scaled units. Any downstream consumer that compares raw `pics` outputs across datasets inherits a data-dependent factor of up to max/p90.

**One bright pixel.** One pixel at 1–32× the phantom maximum was added to the coil images. Results for ℓ1-wavelet `-r 0.01`, with NRMSE computed outside a 7×7 neighbourhood of the pixel:

| Spike amplitude / phantom max | Automatic scale | NRMSE, automatic scale | NRMSE, fixed `-w 932.04` |
|---|---|---|---|
| 0 | 932.0 | 0.049 | 0.049 |
| 1 | 3554 | 0.115 | 0.053 |
| 2 | 6888 | 0.187 | 0.155 |
| 4 | 13556 | 0.300 | 0.336 |
| 8 | 26893 | 0.420 | 0.628 |
| 32 | 106911 | 0.637 | 0.850 |

The automatic scale tracks the outlier (`max` branch), multiplying `λ_eff` and over-regularizing the rest of the image at small amplitudes. At large amplitudes, the fixed scale is worse because the outlier's incoherent aliasing is under-thresholded. Neither choice is uniformly safe. Basis: execution.

### 3. Accuracy versus undersampling, and random-direction perturbation ratios

Magnitude NRMSE against the fully sampled RSS image, after least-squares scalar fitting. Single-thread wall time is in parentheses. Basis: execution.

| `poisson -y=-z` | Sampled fraction (R_eff) | CG `-i 30` | `-l2 -r 0.01` | `-l1 -r 0.01` | `-R T:3:0:0.01` |
|---|---|---|---|---|---|
| 1.2 | 0.674 (1.48) | 0.0192 (0.08 s) | 0.0198 | 0.0262 | 0.0572 |
| 1.5 | 0.458 (2.18) | 0.0275 | 0.0299 | 0.0329 | 0.0859 |
| 2 | 0.268 (3.73) | 0.0557 | 0.0776 | 0.0491 | 0.1534 |
| 2.5 | 0.182 (5.51) | 0.1036 | 0.1636 | 0.0728 | 0.2281 |
| 3 | 0.133 (7.51) | 0.1753 | 0.2464 | 0.0955 | 0.2943 |

How to read this table:

- ℓ1-wavelet overtakes CG only above R_eff ≈ 3.
- TV with λ = 0.01 is worse than CG at every acceleration on this piecewise-constant phantom.
- The fixed λ is not tuned per acceleration.
- These rankings are for this phantom and λ only.

**Perturbation ratios at R_eff = 3.73.**

- Method: complex Gaussian noise was restricted to sampled locations and scaled to ε·‖y‖ with ε ∈ {10⁻⁴, 10⁻³, 10⁻²}, 3 trials each; each perturbed input was then reconstructed.
- Measured ratio (‖Δx‖/‖x‖)/(‖Δy‖/‖y‖), min–max over the 9 runs: CG 1.95–2.00; Tikhonov 1.41–1.44; ℓ1-wavelet 0.41–0.43; TV 0.32–0.33.
- The ratios were flat in ε, so the response is effectively linear at these levels for random directions.

Basis: execution.

**Relation to Antun et al. (2020).**

- Antun et al. show that trained deep-learning reconstructions can be unstable to tiny, *adversarially chosen* perturbations, and can also degrade when sampling increases. Basis: documentation.
- The random-direction ratios above do **not** bound the worst-case (adversarial) amplification of BART's solvers, because worst-case directions were not searched. For Tikhonov solved to convergence, the worst case is the operator norm of `(AᴴA+λI)⁻¹Aᴴ` and exceeds any random-direction ratio. Basis: derived.
- The demonstrated discontinuity in §2 comes from a preprocessing heuristic, not from the convex solver. Convex ℓ1 problems with a fixed λ have solution maps that are continuous in `y`. Basis: derived.

### 4. Coil-map estimation sensitivity (ESPIRiT defaults)

`bart ecalib` defaults (`src/calib/calib.c:686-705`; `src/ecalib.c:60`):

- `kdims = {6,6,6}`, `threshold = 0.001`, `crop = 0.8`;
- calibration region `calsize = {24,24,24}`;
- `rotphase = true`.

Consequences:

- **Crop mask.** Maps are zeroed where the eigenvalue is below `crop`. The SENSE operator then has no support there, and signal outside the mask cannot be reconstructed no matter what the solver does. Basis: source + derived.
- **Thresholded, data-dependent maps.** The crop is a hard threshold on a data-derived eigenvalue map, so the support is a discontinuous function of the calibration data, like the scale rule. Basis: derived.
- `ecalib -m1` took 0.19–0.27 s and 22–23 MB peak RSS at 128², single thread. Basis: execution.

### 5. Pulseq: what is checked where

| Check | Where (pulseq @11e459d9…) | Notes |
|---|---|---|
| Event delays, durations, RF/ADC dwell on raster | `matlab/+mr/checkTiming.m` `div_check`: `abs(c − round(c)) < 1e-9` in raster units (`:112`) | Gradient raster default `10e-6` s (`opts.m:22`). |
| Block duration on `blockDurationRaster`; RF dead/ring-down; ADC dead time; frequency offsets; gradient continuity across blocks (1 Hz/m tolerance) | `@Sequence/Sequence.m` `checkTiming` (`:211-394`) | **No amplitude or slew check** in either `checkTiming`. |
| Per-channel slew/amplitude at creation | `makeArbitraryGrad.m:75-76` (`error('Slew rate violation …')`); `makeTrapezoid.m` | First/last samples are extrapolated by half a raster if not given (warning). |
| Vector-norm ("absolute") gradient/slew | `@Sequence/testReport.m:352, 357, 425` | Computed over the interpolated common time axis; only annotated `[EXCEEDED]`. |
| Defaults | `opts.m:12-13, 22, 29`: 40 mT/m, 170 T/m/s, 10 µs raster, B0 1.5 T | |
| RF power | `+mr/calcRfPower.m` | Relative energy (Hz²·s); "Absolute SAR requires further scaling by tx-coil and subject-specific factors" (`:39-41`). |

Basis: source.

**Derived consequence of per-channel limits.**

- A rotation preserves the vector norm, so a single-axis trapezoid at the limit stays within the per-channel limit after any rotation.
- Simultaneous logical-axis gradients each at the per-channel slew limit can reach √3× that value on one physical axis after rotation.
- Rotation events (`registerRotationEvent`) are checked only for being a valid quaternion (`Sequence.m:796-805`).
- The hardware's real limit may be per-axis or vector-norm; that depends on the scanner and was **not examined**.

### 6. SAFE PNS model and the Pulseq PNS verdict

**Model as coded** (`safe_pns_model.m:27-35`):

```text
α_k   = dt / (τ_k·1e-3 + dt)                           (τ in ms, dt in s)
LP(x)[1] = α x[1];   LP(x)[i] = α x[i] + (1−α) LP(x)[i−1]
stim  = ( a1·|LP_α1(dG/dt)| + a2·LP_α2(|dG/dt|) + a3·|LP_α3(dG/dt)| ) / stim_limit · g_scale · 100   [% per axis]
```

`safe_gwf_to_pns.m` takes the following steps:

- It zero-pads `4·max τ` (`:27`).
- It differentiates with `diff(gwf)/dt` (`:36`).
- It applies the model per axis with that axis's hardware block.

The SAFE abstract that this implements is Hebrank & Gebhardt (2000). Its code comment says the RC filter form was chosen because the abstract only says "lowpass with time-constant tau". Basis: source + documentation.

**Pulseq composition** (`@Sequence/calcPNS.m`). Basis: source.

1. The gradient waveforms are resampled to raster-period centres by linear interpolation (`:48, 57`).
2. They are converted from Hz/m to T/m by dividing by γ (`:85`).
3. The result is passed to `safe_gwf_to_pns`.
4. `pns_norm = vecnorm(...)` combines the axes (`:89`).
5. `ok = all(pns_norm < 1)` decides the verdict (`:90`).

`safe_plot.m:16` uses the same L2 norm.

**Silent acceptance and unused fields.** Basis: source.

- `safe_gwf_to_pns.m:34` reads `safe_hw_check(hw);`, discarding the return value.
- `safe_hw_check.m:6-7` defaults `verbose = 0`, and `:29` tests `abs(a1+a2+a3−1) > 0.001`.
- A malformed specification is therefore neither rejected nor reported.
- `stim_thresh` is loaded (`calcPNS.m:151`; `safe_hw_from_asc.m:65-67`) and required non-empty by `safe_hw_check`, but no computation uses it.
- In both example hardware files, `stim_thresh = 0.8·stim_limit`. That makes it plausible that the threshold field encodes a normal-mode-style 80 % level, but this is an **unverified interpretation**.

**Transcription probe results.** These are a numpy transcription on the fictional example hardware, not a real system. Basis: execution (toy transcription of the SAFE code, not the MATLAB code itself).

| Waveform (x axis, 32 bipolar lobes, 200 µs flat) | dt | Upstream α peak % | Exact-ZOH α peak % |
|---|---|---|---|
| 40 mT/m, 170 T/m/s | 1 µs | 97.99 | 98.05 |
| 40 mT/m, 170 T/m/s | 10 µs | 97.05 | 97.65 |
| 40 mT/m, 170 T/m/s | 20 µs | 96.45 | 97.65 |
| 20 mT/m, 200 T/m/s | 10 µs | 80.47 | 81.51 |
| 20 mT/m, 200 T/m/s | 20 µs | 79.45 | 81.51 |

Discretization:

- `dt/(τ+dt)` is the backward-Euler pole. It lags the continuous first-order response, so at a fixed waveform the predicted peak falls as `dt` grows, by up to −2.1 pp at 20 µs here.
- The x-axis `τ2 = 0.03 ms` gives `dt/τ = 0.33` at the 10 µs Pulseq raster.
- The direction of the bias is *relative to a continuous-time reading of "lowpass"*. Which discretization the vendor reference uses is **unknown**. Upstream comments state that the code was checked against a vendor simulator after the `g_scale` fix.

Axis combination (same 40 mT/m, 170 T/m/s train on x, y and z):

- per-axis peaks are 97.05 %, 169.05 % and 83.76 %;
- the L2 norm is 211.6 %, while the sum would be 348.6 % and the max-axis value 169.1 %;
- the verdict therefore depends on the combination rule chosen by the integrator.

Other probe results:

- **100 % / 80 % slew levels.** For the 40 mT/m, 200 µs-flat train at 10 µs, the slew rate at which each axis reaches 100 % is x 177.6, y 78.5 and z 216.6 T/m/s. The 80 % levels are x 129.7, y 56.4 and z 159.3 T/m/s.
- **Malformed hardware.** Setting `x.a1 = 0.8`, so that `a1+a2+a3 = 1.4`, raised the x-axis peak from 97.05 % to 166.05 % with no error.

**Mapping to IEC 60601-2-33 operating modes.** Basis: documentation (secondary) + derived.

- Secondary sources describe the standard's PNS limits as follows.
  - Normal mode is limited to **80 %** and first-level controlled mode to **100 %** of the median perception threshold (ICNIRP 2004, describing the IEC scheme).
  - Without system-specific data, the default threshold curve uses a rheobase of 20 T/s and a chronaxie of 0.36 ms (McRobbie 2012). That is `dB/dt = 20·(1 + 0.36/τ) T/s`, with τ the effective stimulus duration in ms (ICNIRP 2004). The normal-mode curve is therefore 0.8× this curve (derived).
  - The cardiac limit for whole-body gradients is `dB/dt < 20 T/s / (1 − exp(−τ_s,eff/3 ms))` (Klein et al. 2021).
- Pulseq's `ok` is relative to `stim_limit`, not to a threshold that the code identifies as a mode boundary.
- The code cannot by itself establish compliance with either mode; that requires the vendor's mapping of `stim_limit` to the standard. This is **not examined**.

### 7. SAR and B1+ duty-cycle integration

Basis: source + documentation (secondary) + derived.

- **No SAR in the subjects.** None of the pinned subjects computes SAR.
  - Pulseq provides `mr.calcRfPower`, which gives relative `∫|B1|²dt` in Hz²·s for one pulse, and `Sequence.calcRfPower` (`Sequence.m:2426`) for sequence-level mean/peak power.
  - The conversion to W/kg needs transmit-coil efficiency, reference voltage and a body or head model.
- **Secondary-source limits.** Malik et al. (2015, Table 1) give the IEC 60601-2-33 (2010 edition) limits.
  - Whole-body SAR is **2 W/kg** in normal mode and **4 W/kg** in first-level controlled mode; head SAR is **3.2 W/kg** in both.
  - Values are averaged over 6 min, and no 10 s period may exceed twice the limit.
  - Specific absorbed energy is capped at 240 W·min/kg for long examinations.
  - The fourth edition (2022) removes that energy cap (BIR 2022). Its SAR table was **not examined**.
  - ICNIRP 2004 uses different head and short-term rules, so it must not be substituted for the IEC values.
- **Duty-cycle bound.** For a periodic sequence, a mean-power bound is linear in `Σ_pulses ∫|B1|²dt / TR`. A correct pre-scan check therefore needs the full block sequence plus both averaging windows. The relative-energy primitives suffice for the first part, not the second.

### 8. Cone-beam FDK in RTK and ASTRA

**Pipeline.** `rtk::FDKConeBeamReconstructionFilter` chains three filters (`rtkFDKConeBeamReconstructionFilter.h:35-39`):

1. `FDKWeightProjectionFilter` (cosine and angular-gap weights);
2. `FFTRampImageFilter`;
3. `FDKBackProjectionImageFilter`.

ASTRA's `CUDA_FDK` runs three equivalent steps: `devFDK_preweight`, optional Parker short-scan weighting, then filter and back-projection. Basis: source.

**Ramp kernel.** Both build the band-limited ramp in the spatial domain and FFT it. Basis: source.

- RTK: `rtkFFTRampImageFilter.hxx:71, 75` set `h[0] = 1/(4·spacing)` and `h[odd] = −1/((nπ)²·spacing)`.
- ASTRA: `src/Filters.cpp:57, 63` set `data[2*i] = -1/(f*f)` with `f = πj` for odd `i`, and `data[0] = 0.25f`.

When an RTK window is selected (Hann, cosine, Hamming, Ram-Lak cut, Shepp–Logan), the first `ncut = round(n·min(1, cut))` frequency bins are weighted and the remaining bins are zeroed (`:97, 139`). With no window selected, the kernel is left unmodified. Basis: source.

| Toy result (2D parallel FBP, 367 bins, 360 views, uniform disk R = 100 px) | Centre mean (true 1.0) | NRMSE in r < 0.9R |
|---|---|---|
| Spatial-domain ramp, padded ×2 | 1.0002 | 0.0075 |
| Spatial-domain ramp, unpadded | 1.0002 | 0.0075 |
| Naive `|f|` ramp sampled on the DFT grid, unpadded | 0.936 | 0.0649 |
| Naive `|f|` ramp, padded ×2 | 0.984 | 0.0170 |

Basis: execution (toy model, not RTK/ASTRA).

**Padding.** RTK pads by `m_ZeroPadFactors = 2` and then grows the size until its greatest prime factor is ≤ 13 when FFTW is used (`rtkFFTProjectionsConvolutionImageFilter.hxx:41-48, 287-300`). Basis: source.

**Lateral truncation.** RTK's `TruncationCorrection` defaults to 0 (`.h:179`). When set, it mirror-extends `floor(TruncationCorrection·width)` bins per side (`.hxx:81`):

```text
p_ext = w_i · (2·S_edge − p[mirror])
w_i   = sin((next − i)·π/(2·next − 2))^0.75          (.hxx:239, 259, 354)
```

This cites Ohnesorge et al. (2000). Basis: source.

Transcribed into the toy with a detector covering only |s| ≤ 0.8R (NRMSE inside r < 0.75R). Basis: execution (toy).

| Extension fraction | Centre mean | NRMSE r < 0.75R |
|---|---|---|
| none | 1.068 | 0.213 |
| 0.10 | 1.017 | 0.038 |
| 0.25 | 0.974 | 0.048 |
| 0.50 | 0.941 | 0.098 |

More extension is not monotonically better in this toy; the weight profile over-corrects at large widths.

**Cosine/geometry weights.**

- **RTK** weights each projection `k` with its own geometry (`rtkFDKWeightProjectionFilter.hxx:43, 108, 113`):
  - its own source-to-detector distance, source-to-isocentre distance, tilt and `ProjectionOffsetsX/Y`;
  - and angular-gap weights from the actual source angles (`GetAngularGaps`), so irregular angular sampling is handled.
- **ASTRA** `FDK_t::prepareWeighting` reads only `angles[0]` (`cuda/3d/fdk.cu:470`), carries the comment "We don't support arbitrary cone_vec geometries here" (`:472`), and computes the in-row coordinate from the array centre: `fU = (detectorU − 0.5·iProjU + 0.5)·fDetUSize` (`:164`). Only a vertical shift `fZShift` is applied.
- **ASTRA does not enforce that restriction.** `CudaFDKAlgorithm3D.cpp:82` accepts any `CConeVecProjectionGeometry3D`.
  - A `cone_vec` geometry with a lateral detector offset or per-view drift therefore passes the configuration check.
  - It is then pre-weighted as if centred and as if every view had view 0's distances.
  - Back-projection uses the full vectors.
- The size of this effect was **not measured**; the code is CUDA-only and no GPU was used.
- ASTRA's plain `cone` geometry has no offset parameters at all: only `DistanceOriginDetector` and `DistanceOriginSource` (`src/ConeProjectionGeometry3D.cpp:86-87`).

Basis: source.

**Short scan.** ASTRA's Parker weighting assumes linearly ordered, equally spaced angles. It warns, but proceeds, when the range is below π + 2·fan angle (`fdk.cu:547-555`). Basis: source.

**Centre-of-rotation drift.** In the toy, an uncorrected lateral detector offset raised NRMSE in r < 0.9R as follows: 0.0075 (0 px), 0.0090 (0.25 px), 0.0124 (0.5 px), 0.0195 (1 px), 0.0295 (2 px), 0.0426 (4 px). The centre mean stayed within 0.5 % of truth, so the error is edge blurring and doubling rather than a bias in Hounsfield units (HU). Basis: execution (toy).

**Cone-angle incompleteness.**

- Tuy's condition requires every plane through a voxel to intersect the source trajectory. A circular orbit satisfies it only in the mid-plane, so FDK is exact only there and approximate off-plane. Basis: documentation (Tuy 1983; Feldkamp et al. 1984).
- Cone half-angle at the detector edge is `κ = atan(H_det/(2·SDD))`. For example, H = 400 mm and SDD = 1500 mm give κ = 7.6°. Basis: derived arithmetic.
- No off-plane error figure was measured here.

**HU stability under beam hardening.**

- FDK reconstructs line integrals as given. RTK includes `WaterPrecorrectionImageFilter`, a polynomial in the projection value whose header cites Kachelriess, Med. Phys. 2006; it is an empirical first-order cupping correction applied *before* FDK.
- No subject models polychromatic spectra in the FDK path.
- HU accuracy therefore depends on calibration outside these operators.

Basis: source.

### 9. Performance and resource footprint (L1–L6)

| Level | BART `pics` / `ecalib` | Pulseq + SAFE | RTK / ASTRA FDK |
|---|---|---|---|
| L1 authoring/maintenance | not measured | not measured | not measured |
| L2 toolchain build | `make -j16 bart`: 19.52 s wall, 85.1 s user, 23.2 s sys, largest single process 108,944 kB RSS (96-vCPU 2.6 GHz Xeon VM) | not measured (MATLAB; not run) | not measured (not built) |
| L3 elaboration/latency | `pics` startup is included in the L4 times below | not applicable | not measured |
| L4 execution | 128²×8 coils, 1 thread: `pics` 0.06–0.18 s per run; 256²×8 coils: CG 1.06 s, ℓ1 1.16 s, TV 1.58 s (1 thread); 1.55 / 0.54 / 0.96 s with 8 threads (single runs) | numpy transcription: whole probe 2.34 s | toy FBP probe (256², 360 views): 4.3 s total; real FDK not measured |
| L5 verification/checking | not applicable | not applicable | not applicable |
| L6 memory/size | `bart` binary 3,411,704 bytes; `pics` peak RSS 14–15 MB (128²), 33–39 MB (256²); `ecalib` 22–23 MB (128²); 256²×8-coil `.cfl` k-space file 4,194,304 bytes | transcription probe peak RSS 32,488 kB | toy probe peak RSS ≈ 52 MB |

Basis: execution, with the commands under Evidence. The VM host class is a 96-vCPU Intel Xeon at 2.60 GHz.

### 10. Comprehensibility (C1) and simplicity / model refinement (C2)

**C1, comprehensibility.**

- **BART.** The meaning of `-r λ` cannot be read from the command line. With automatic scaling it is relative to an order statistic of a low-resolution image, and which order statistic depends on a hidden branch. `-d 3` exposes it as `Scaling: …!`. A reader who only sees `pics -l1 -r 0.01` cannot predict the absolute regularization.
- **SAFE.** The model is short and locally readable: 3 filters × 3 axes, about 60 lines. Its hazards are non-local:
  - the `is_ok` result is ignored in a different file;
  - `stim_thresh` looks meaningful but is unused;
  - the combination rule lives in the caller (`calcPNS`) or the plot routine.
- **Pulseq.** "timing check passed" can be misread as "hardware-safe", although amplitude, slew and PNS are separate checks in other functions.
- **RTK.** The FDK chain is three named filters with per-projection geometry, which keeps reasoning local.
- **ASTRA FDK.** Its geometry restriction is a source comment, not an interface constraint.

**C2, simplicity and model refinement.**

- **BART.** The scale heuristic and λ are two mechanisms for one invariant: regularization strength relative to signal. A continuous scale such as a fixed percentile, or reporting λ in absolute units by default, would remove the branch discontinuity without changing solvers. The exception, "ℓ2/CG are scale-free", would then become an ordinary case of degree-k homogeneity.
- **PNS/SAFE.** Axis combination, threshold semantics and hardware validation are spread over three files. A single function returning `(per-axis %, combined %, verdict, validated hw)` would make the IEC mode a parameter rather than an implicit `< 1` test.
- **CT.** RTK and ASTRA converge on one ramp-kernel construction, an independent confirmation of that design. Their geometry models diverge:
  - RTK uses a per-view parametric geometry everywhere;
  - ASTRA uses an idealized `cone` geometry plus a general `cone_vec` geometry that the FDK weighting only partially honours.
  - A single per-view geometry type, used by both weighting and back-projection, is the minimal abstraction; the restriction would then be checkable.

### 11. Validation of implementations and proposed mechanisms (V1–V4)

- **V1, specification adequacy.**
  - BART: upstream `tests/pics.mk` defines 44 `tests/test-pics-*` targets. They reconstruct BART phantoms and assert tolerance bounds, for example `nrmse -t 0.23` against the analytic phantom.
  - Tolerance tests of this kind would not catch the discontinuity in §2. That needs a metamorphic test that perturbs the data slightly and asserts bounded output change.
  - SAFE has no tests in the repository. The `a1+a2+a3` invariant exists only in a check whose result is discarded.
  - Pulseq: its `testReport` "EXCEEDED" annotations are advisory.
- **V2, differential/metamorphic testing.**
  - RTK vs ASTRA FDK on identical geometry, including `cone_vec` with a lateral offset, is a natural differential test. It was **not run**.
  - A SAFE transcription vs MATLAB diff on shared waveforms would validate the transcription. It was **not run**; MATLAB was unavailable.
- **V3, concurrency/physical.**
  - BART multi-thread results were not compared bit-for-bit with single-thread results.
  - The 8-thread timings above are single runs.
  - Hardware gradient-amplifier or RF-power measurements are outside scope.
- **V4, plant falsification and human factors.**
  - PNS predictions require volunteer-threshold studies; none are in the subjects.
  - Reconstruction hallucination risk requires reader studies (Antun et al. discuss clinical consequences).
  - Neither was examined.

## Boundaries

- **Not examined.**
  - Non-Cartesian `pics` (NUFFT, Toeplitz, `-t`), GPU builds, and multi-map ESPIRiT.
  - BART's learned-reconstruction tools.
  - Worst-case (adversarial) perturbation search for any BART solver.
  - Running Pulseq or SAFE in MATLAB/Octave.
  - Building or running RTK or ASTRA.
  - The real-system magnitude of ASTRA's first-view weighting with offset `cone_vec` geometries.
  - Off-mid-plane FDK error.
  - Beam-hardening HU error.
  - IEC 60601-2-44 CT dose content.
- **Unknown.**
  - Which discretization a vendor PNS monitor uses, and therefore whether the measured 0.6–1.0 pp `α` bias is conservative or not relative to real hardware.
  - Whether `stim_thresh` was meant to encode the normal-mode level.
  - The vendor mapping from `stim_limit` to IEC mode limits.
- **Known not to apply.**
  - The §2 discontinuity does not affect `-l2`/CG reconstructions, nor any run with explicit `-w`.
  - The toy FBP numbers are not RTK or ASTRA properties.
  - The SAFE numbers are not properties of any real scanner; the example hardware is fictional.
- **Unsupported, per source comments.** ASTRA FDK with arbitrary `cone_vec` geometries (comment at `fdk.cu:472`), although not rejected.
- **Stronger conclusions the evidence does not support.**
  - That BART's convex solvers are "stable" in Antun's sense: only random directions were tested.
  - That learned reconstructions in BART are unstable: they were not run.
  - That any Pulseq sequence passing `calcPNS` complies with IEC 60601-2-33.
- **Normative sources.** The IEC limit values quoted here are secondary-source descriptions; the normative text was not examined.

## Evidence

Observation date: all evidence was acquired on 2026-11-20 (UTC). The pins are the GitHub `HEAD` commits on that date; the commit timestamps are listed below.

Pinned sources (paths relative to repository root):

- `mrirecon/bart` @ `731bfd3ec4f09ffa59b497ded1274a2c0357c8af` (commit 2026-03-01).
  - `src/pics.c:82, 180-181, 505, 513, 521, 529, 620, 634, 653-654, 658`
  - `src/sense/optcom.c:74-109` (`estimate_scaling_norm`), `:146-176`
  - `src/grecon/optreg.c:374-392`; `src/grecon/italgo.c:30-67`
  - `src/ecalib.c:60-95`; `src/calib/calib.c:686-705`
- `pulseq/pulseq` @ `11e459d9b6b426aa6ea57a01153fb9afea332f6f` (commit 2026-10-22).
  - `matlab/+mr/@Sequence/Sequence.m:211-394, 796-805, 2426`
  - `matlab/+mr/checkTiming.m:1-113`
  - `matlab/+mr/@Sequence/calcPNS.m:45-90, 109-180`
  - `matlab/+mr/@Sequence/testReport.m:320-430`
  - `matlab/+mr/opts.m:11-30`; `matlab/+mr/makeArbitraryGrad.m:70-79`; `matlab/+mr/calcRfPower.m:35-92`
- `filip-szczepankiewicz/safe_pns_prediction` @ `152ab67c086170c40c1988ebba9002e018a0652c` (commit 2026-09-26).
  - `safe_pns_model.m:1-79`; `safe_gwf_to_pns.m:22-48`; `safe_hw_check.m:1-36`
  - `safe_example_hw_peripheral.m`; `safe_plot.m:16`; `readme.md`
- `RTKConsortium/RTK` @ `3f6b9e185a97af546b2eb4dcd9c7bfdbc3a45c96` (commit 2026-11-20).
  - `include/rtkFDKConeBeamReconstructionFilter.h:32-60`; `include/rtkFFTRampImageFilter.hxx:47-178`
  - `include/rtkFFTProjectionsConvolutionImageFilter.{h:179, hxx:36-48, 79-82, 205-262, 285-302, 346-356}`
  - `include/rtkFDKWeightProjectionFilter.hxx:38-120`; `include/rtkWaterPrecorrectionImageFilter.h:29-36`
- `astra-toolbox/astra-toolbox` @ `627d834ce2339b505d098c205f0293a401faf6b4` (commit 2026-11-17).
  - `src/Filters.cpp:41-69, 133-150`; `cuda/3d/fdk.cu:144-189, 459-556`
  - `src/CudaFDKAlgorithm3D.cpp:79-93`; `src/ConeProjectionGeometry3D.cpp:80-92, 185-196`

Literature. Each DOI was checked against publisher or index metadata on the observation date.

- Antun, Renna, Poon, Adcock, Hansen, "On instabilities of deep learning in image reconstruction and the potential costs of AI," *PNAS* 117(48):30088–30095, 2020, doi:10.1073/pnas.1907377117.
- Lustig, Donoho, Pauly, "Sparse MRI," *Magn. Reson. Med.* 58(6):1182–1195, 2007, doi:10.1002/mrm.21391.
- Uecker et al., "ESPIRiT," *Magn. Reson. Med.* 71(3):990–1001, 2014, doi:10.1002/mrm.24751.
- Blumenthal, Luo, Schilling, Holme, Uecker, "Deep, deep learning with BART," *Magn. Reson. Med.* 89(2):678–693, 2023, doi:10.1002/mrm.29485.
- Layton et al., "Pulseq," *Magn. Reson. Med.* 77(4):1544–1552, 2017, doi:10.1002/mrm.26235.
- Hebrank & Gebhardt, "SAFE-Model," Proc. ISMRM 8 (2000), abstract 2007 (no DOI; URL in `safe_pns_model.m:12`).
- Feldkamp, Davis, Kress, *J. Opt. Soc. Am. A* 1(6):612–619, 1984, doi:10.1364/JOSAA.1.000612.
- Tuy, *SIAM J. Appl. Math.* 43(3):546–552, 1983, doi:10.1137/0143035.
- Ohnesorge et al., *Med. Phys.* 27(1):39–46, 2000, doi:10.1118/1.598855.
- Parker, "Optimal short scan convolution reconstruction for fan beam CT," *Med. Phys.* 9(2):254–257, 1982, doi:10.1118/1.595078.
- Rit et al., RTK, *J. Phys. Conf. Ser.* 489:012079, 2014, doi:10.1088/1742-6596/489/1/012079.
- van Aarle et al., *Ultramicroscopy* 157:35–47, 2015, doi:10.1016/j.ultramic.2015.05.002; and *Opt. Express* 24(22):25129–25147, 2016, doi:10.1364/OE.24.025129.
- Kachelrieß, Sourbelle, Kalender, "Empirical cupping correction: a first-order raw data precorrection for cone-beam computed tomography," *Med. Phys.* 33(5):1269–1274, 2006, doi:10.1118/1.2188076.
- Szczepankiewicz, Westin, Nilsson, "Gradient waveform design for tensor-valued encoding in diffusion MRI," *J. Neurosci. Methods* 348:109007, 2021, doi:10.1016/j.jneumeth.2020.109007 (the citation requested by the SAFE repository).
- Malik et al., "Specific absorption rate in neonates undergoing magnetic resonance procedures at 1.5 T and 3 T," *NMR Biomed.* 28(3):344–352, 2015, doi:10.1002/nbm.3256 (Table 1: IEC 60601-2-33 SAR limits).
- McRobbie, "Occupational exposure in MRI," *Br. J. Radiol.* 85(1012):293–312, 2012, doi:10.1259/bjr/30146162 (IEC default rheobase 20 T/s, chronaxie 0.36 ms).
- Klein, Davids, Schad, Wald, Guérin, "Investigating cardiac stimulation limits of MRI gradient coils …," *Magn. Reson. Med.* 85(2):1047ff., 2021, doi:10.1002/mrm.28472 (IEC cardiac limit form).
- ICNIRP, "Medical magnetic resonance (MR) procedures: protection of patients," *Health Phys.* 87(2):197–216, 2004 (80 %/100 % of median threshold; `20(1 + 0.36/τ)` T/s).
- British Institute of Radiology, "MR Safety advice" sheet 1, 2022 (fourth edition of IEC 60601-2-33 in 2022; removal of the SAE limit).

Standards: IEC 60601-2-33 (Ed. 3.0 2010 with Amd. 1 2013 and Amd. 2 2015; Ed. 4.0 2022 per BIR 2022) and IEC 60601-2-44. The normative text of neither was examined; every limit quoted above is a secondary-source description.

Execution environment:

- Host: Linux VM, 96 vCPU Intel Xeon @ 2.60 GHz, 236 GB RAM; Python 3.13.15; numpy 2.5.4; gcc (system).
- BART libraries: OpenBLAS 0.3.32 (pthread), LAPACKE 3.12.1, FFTW 3.3.11 (single precision, threads).

Commands:

```bash
git clone https://github.com/mrirecon/bart.git && cd bart && git checkout 731bfd3ec4f09ffa59b497ded1274a2c0357c8af
/usr/bin/time -v make -j16 OPENBLAS=1 PNG=0 BLAS_BASE=<dir with include/ lib/> FFTW_BASE=<same> bart
./bart version            # v1.0.00-1-g731bfd3
# probe (numpy + subprocess), single thread:
OMP_NUM_THREADS=1 python3 bart_probe.py ./bart /tmp/bart_run
# switch reproduction once ka/kb (bracketing inputs) and sens exist:
bart pics -d 3 -S -l1 -r 0.01 ka sens rSa;  bart pics -d 3 -S -l1 -r 0.01 kb sens rSb
bart nrmse rSa rSb        # 0.027404
bart nrmse ka kb          # 9.591145e-08
```

Core of the BART probe. Readers can reconstruct it from this description:

1. `bart phantom -x 128 -s 8 -k ksp`; `bart phantom -x 128 -S 8 strue`; `bart fft -i -u 3 ksp cimg`.
2. Reference = RSS of `cimg`.
3. Masks: `bart poisson -Y 128 -Z 128 -y a -z a -C 20 -s 1`, reshaped to (128,128,1,1).
4. `bart ecalib -m1`, then `bart pics` with `-i 30` | `-l2 -r 0.01` | `-l1 -r 0.01` | `-R T:3:0:0.01`.
5. Error metric: magnitude NRMSE after least-squares real scaling.
6. Switch family: `cimg + c·1[0.05<|truth|<0.5]·strue`, re-FFT (`bart fft -u 3`), mask, bisection on the `!` flag printed by `pics -d 3`.

SAFE transcription: identical equations to §6, with the fictional example hardware values `x: τ=(0.20, 0.03, 3.00) ms, a=(0.40, 0.10, 0.50), stim_limit 30, g_scale 0.35; y: τ=(1.50, 2.50, 0.15), a=(0.55, 0.15, 0.30), 15, 0.31; z: τ=(2.00, 0.12, 1.00), a=(0.42, 0.40, 0.18), 25, 0.25`. Each waveform is a trapezoid train sampled at `dt`, with padding as in `safe_gwf_to_pns`.

## Revalidation

- **BART scaling rule.** Diff `src/sense/optcom.c` `estimate_scaling_norm` and `src/pics.c` lines 499–538. If the ternary on p90/max is unchanged, the discontinuity persists for ℓ1/TV with automatic scaling. Cheapest execution check:
  1. Run `pics -d 3 -l1 -r 0.01` on any dataset, read `max/p90/median` from the `Scaling:` line, and construct data near `max − p90 = 2(p90 − median)`.
  2. Alternatively, rerun the bisection probe above. A rescaled-output change ≫ the input change at the bracket confirms the behaviour.
- **BART defaults.** `grep -n "maxiter = 30\|step = 0.95" src/pics.c`; `sed -n 30,67p src/grecon/italgo.c`.
- **SAFE.**
  - Check `safe_gwf_to_pns.m` for whether the `safe_hw_check` return value is now used.
  - Check `safe_pns_model.m` for the `alpha = dt / (tau + dt)` form.
  - Rerun the transcription against MATLAB output, which would also validate the transcription.
- **Pulseq.**
  - `grep -n "maxSlew\|maxGrad" matlab/+mr/checkTiming.m matlab/+mr/@Sequence/Sequence.m`: no hits inside `checkTiming` means the amplitude/slew gap persists.
  - `sed -n 85,90p matlab/+mr/@Sequence/calcPNS.m` shows the combination rule and verdict.
- **ASTRA.** Check `cuda/3d/fdk.cu` `prepareWeighting` for use of per-view geometry, and `src/CudaFDKAlgorithm3D.cpp` for a check that rejects non-regular `cone_vec` geometries. A GPU differential run of RTK vs ASTRA on a laterally offset `cone_vec` geometry is the decisive test; it has not been done.
- **RTK.** Check that `rtkFFTRampImageFilter.hxx` still builds the spatial kernel, and that `UpdateTruncationMirrorWeights` keeps the `^0.75` sine profile.
- **Toy numbers.** Rerun the toy FBP/SAFE scripts. They are deterministic and seedless, and need only numpy.
