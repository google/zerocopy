# Real-Time Audio Clocking, Adaptive Passivity, and Control Timing: AES67 ASRC FIFO Slips, FxLMS 90-Degree Acoustic Howling, and MIDI 2.0 UMP JR Timestamps

## Summary

Real-time networked audio, adaptive electroacoustic noise cancellation, and high-resolution musical control share three mathematically coupled failure modes—clock-phase step overshoot, closed-loop gradient sign inversion, and modular timestamp/scaling corruption—verified across six pinned open-source DSP/audio repositories and four primary standards:

1. **AES67 / SMPTE ST 2110-30 PTPv2 Step Discontinuities, ASRC Ratio Slewing, and Ring-Buffer Slips**:
   - In `PipeWire/pipewire` (`0e30a575c2e279bd7a8975e403168f8ac906cc7e`), `spa/include/spa/utils/dll.h:35-61` implements a 3rd-order Delay-Locked Loop (`z1, z2, z3`; `SPA_DLL_BW_MIN = 0.016`, `SPA_DLL_BW_MAX = 0.128`) whose output `corr = 1.0 - (z2 + z3)` drives `pw_stream_set_rate(impl->stream, 1.0 / corr)` (`src/modules/module-rtp/audio.c:295`), which `spa/plugins/audioconvert/resample-native.c:270` applies as `in_rate_eff = round(in_rate / rate) = round(in_rate * corr)`. In constant-latency mode (`sess.ts-direct = false`), `audio.c:262-311` hardcodes DLL period `128`, clamps fill error to `ERROR_MSEC = 2.0 ms` (`stream.h:21`), imposes **no explicit rate-deviation or slew-rate clamp** on `1.0 / corr`, and triggers an abrupt resync—discarding the entire packet queue (`rtp_stream_clear_queued_packets`, `audio.c:304-310`)—on **any** single missing sample or overrun exceeding `target_buffer`. In direct-timestamp AES67 mode (`sess.ts-direct = true`, `audio.c:206-207`), any PTPv2 grandmaster step exceeding one quantum (`pos->clock.duration`) forces a hard discontinuity reset (`discont = true`).
   - In `libsndfile/libsamplerate` (`0844c208f683527c08ea8a80acc13b398aa9c8bf`), `src/src_sinc.c:492-505` linearly ramps `src_ratio` across `filter->out_count` (`src_ratio = last_ratio + out_gen * (target - last_ratio) / out_count`), while `src_set_ratio()` (`src/samplerate.c:241-252`) steps `state->last_ratio` discontinuously with zero slew-rate bound (`SRC_MAX_RATIO = 256`). Maintaining zero FIFO clicks under PTPv2 steps $\Delta L$ at slew cap $\pm R_{\max}$ strictly requires FIFO capacity $C_{\text{FIFO}} \ge L_{\text{target}} + |\Delta L| + L_{\text{PDV}}$ and recovery time $T_{\text{rec}} \ge |\Delta L| / (f_s \cdot R_{\max})$.
2. **Kuo–Morgan $90^\circ$ FxLMS Instability Cliff & Upstream Adaptive Filter Numerical Defects**:
   - By the Kuo & Morgan (1999, DOI `10.1109/5.763310`) secondary-path phase-error theorem, Filtered-x LMS (`FxLMS`) converges only while the phase discrepancy between true acoustic secondary path $S(e^{j\omega})$ and model $\hat{S}(e^{j\omega})$ remains strictly inside $(-90^\circ, +90^\circ)$, i.e. $\text{Re}\{S^*(e^{j\omega})\hat{S}(e^{j\omega})\} > 0$. Crossing $90^\circ$ (e.g., headphone earcup seal break or automotive transducer shift) flips gradient descent into **exponential gradient ascent** toward full-scale acoustic howling (`> 120 dB SPL`). Stabilizing ANC across physical plant inversions requires combining leaky weight decay ($\gamma > 0$), $H_\infty$ / $\ell_2$ weight-ball projection ($\|w\|_2 \le W_{\max}$), and rapid adaptation-freeze supervision.
   - Direct source audits of `LCAV/pyroomacoustics` (`08d16968f8db414affaf84771a650358a7961446`) and `ARM-software/CMSIS-DSP` (`9f64ba31591e527c505951943b4b95b0eb2f834b`) reveal three severe upstream hazards:
     1. `pyroomacoustics/adaptive/lms.py:49,112-116` divides by `np.inner(self.x, self.x)` with **zero regularization $\epsilon$**, poisoning weights permanently to `NaN` on silent startup frames, and provides no `FxLMS` or leakage term.
     2. `CMSIS-DSP` `Source/FilteringFunctions/arm_lms_norm_f32.c:214-215, 262, 400-401, 454` updates sliding-window `energy` incrementally in `float32_t` (`energy -= x0 * x0; energy += in * in;`) without clamping or periodic recomputation. An exact `float32` probe on **in-range `[-1.0, +1.0]` audio** (`64` taps, `20` transient/quiet cycles) drives `energy` down to `-6.400e-7`, pushing `energy + 0.000000119209289f` **strictly negative (`-5.208e-7`)** on `2,320/5,120` samples—inverting the NLMS step sign with **`-1.920e+6` gain amplification**!
     3. `CMSIS-DSP` `Source/FilteringFunctions/arm_lms_norm_q31.c:52-59, 117-119, 180` uses wrapping `2.62` accumulation (single guard bit), saturating `q31_t` running energy, and unsaturated signed subtraction `e = *pRef++ - (q31_t) acc;` (`line 180`).
3. **MIDI 2.0 UMP 16-Bit JR Timestamp Rollover, Upstream Decode Bug, and Scale-Conversion Embedding**:
   - Under MMA/AMEI `M2-104-UM`, the 16-bit Jitter-Reduction (`JR`) Clock ticks at **$31{,}250\text{ Hz}$** (exact period **$32.0\,\mu\text{s}$** per tick—matching classic MIDI 1.0 `31.25 kbaud` bit time, *not* `31.25 µs`!), yielding a modular rollover period of exactly **$65{,}536 \times 32.0\,\mu\text{s} = 2.097152\text{ s}$** and an unambiguous signed half-window of $\pm 1.048576\text{ s}$.
   - Direct source inspection of `midi2-dev/AM_MIDI2.0Lib` (`7fa1b0c59acf31fbaa55a0e45042663d9a8b7ee4`) uncovered a concrete bug in `src/umpProcessor.cpp:41-47`: for 32-bit Utility Messages (`MT = 0x0`), line 46 computes `mess.value = (umpMess[0] >> 16) & 0xFFFF;` instead of `umpMess[0] & 0xFFFF`, **discarding the 16-bit JR Clock / JR Timestamp payload in bits `[15:0]`** and returning the `MT/Status` header word (`0x0010`/`0x0020`)! Meanwhile, `include/utils.h:195-235` (`scaleUp`/`scaleDown`) is exhaustively verified over all `128` 7-bit and `16,384` 14-bit inputs to be strictly monotone, endpoint- and midpoint-exact (`0 -> 0`, `mid -> 0x80000000`, `max -> 0xFFFFFFFF`), and left-invertible (`scaleDown(scaleUp(x)) == x`), except for a C++ UB shift `(1 << dstBits) - 1L` when `srcBits == 1, dstBits == 32` (`line 203`).
   - In `thestk/rtmidi` (`00d855f31fbaeb196da2c0a3507d92f0d6051efb`), the Windows MIDI Services backend (`RtMidi.cpp:6672-6698`) explicitly **drops all UMP Utility (`MT=0x0`) and MIDI 2.0 Channel Voice (`MT=0x4`) packets**, converts OS timestamps into `double` inter-message deltas, and executes heap allocations (`std::vector::push_back`) and `std::mutex` locks inside the receive callback.

## Applicability

This reference report characterizes six pinned upstream repositories and four normative/peer-reviewed foundations examined directly on `2026-11-19`:

- **ASRC & Networked Clock Recovery Pair**: `libsndfile/libsamplerate` (`0844c208f683527c08ea8a80acc13b398aa9c8bf`, `src/src_sinc.c`, `src/samplerate.c`, `src/common.h`) and `PipeWire/pipewire` (`0e30a575c2e279bd7a8975e403168f8ac906cc7e`, `spa/include/spa/utils/dll.h`, `spa/plugins/audioconvert/resample-native.c`, `spa/plugins/audioconvert/resample-peaks.c`, `src/modules/module-rtp/stream.h`, `src/modules/module-rtp/stream.c`, `src/modules/module-rtp/audio.c`, `src/modules/module-rtp-source.c`), evaluated against AES67-2018, SMPTE ST 2110-30, IEEE 1588-2008 (PTPv2), and Farrow (1988, DOI `10.1109/ISCAS.1988.15483`). Note: `spa/plugins/audioconvert/resample-peaks.c` performs peak-envelope downsampling for level meters rather than audio-rate ASRC.
- **Adaptive Filtering & ANC Stability Pair**: `LCAV/pyroomacoustics` (`08d16968f8db414affaf84771a650358a7961446`, `pyroomacoustics/adaptive/{__init__.py,lms.py}`) and `ARM-software/CMSIS-DSP` (`9f64ba31591e527c505951943b4b95b0eb2f834b`, `Source/FilteringFunctions/{arm_lms_f32.c,arm_lms_norm_f32.c,arm_lms_norm_q31.c,arm_lms_q31.c}`), interpreted against Kuo & Morgan (1999, DOI `10.1109/5.763310`) and Elliott's leaky-FxLMS / $H_\infty$ robustness framework. Note that at commit `9f64ba31...`, CMSIS-DSP's `arm_lms_*` files include `ARM_MATH_NEON` and scalar unrolled loops (`ARM_MATH_LOOPUNROLL`), not ARM Helium `ARM_MATH_MVEF` kernels.
- **MIDI 2.0 UMP & Timestamping Pair**: `midi2-dev/AM_MIDI2.0Lib` (`7fa1b0c59acf31fbaa55a0e45042663d9a8b7ee4`, `include/{utils.h,umpMessageCreate.h}`, `src/umpProcessor.cpp`) and `thestk/rtmidi` (`00d855f31fbaeb196da2c0a3507d92f0d6051efb`, `RtMidi.h`, `RtMidi.cpp`), interpreted against MMA/AMEI `M2-104-UM` and `M2-115-U`.

Executable probes distinguish exact algorithmic reproductions of upstream code (`PipeWire spa_dll_update`, `CMSIS-DSP float32 energy recurrence`, `AM_MIDI2.0Lib scaleUp/scaleDown` and `umpProcessor.cpp:46` bit-shift) from clearly labeled discrete-time toy simulations of ASRC FIFO dynamics and narrowband FxLMS howling.

## Findings

### 1. AES67 / SMPTE ST 2110-30 Clock Recovery, ASRC Slewing, and Ring-Buffer Invariance

#### 1.1 PipeWire 3rd-Order DLL, Resampler Feedback Polarity, and Underrun/Overrun Resync Clicks
`Basis: source + execution (exact spa_dll port + toy FIFO model)`

In `PipeWire/pipewire` (`0e30a575c2e279bd7a8975e403168f8ac906cc7e`), `spa/include/spa/utils/dll.h:25-61` implements a 3rd-order discrete Delay-Locked Loop parameterized by bandwidth `bw` (`SPA_DLL_BW_MIN = 0.016`, `SPA_DLL_BW_MAX = 0.128`), block `period`, and nominal `rate`:

$$\omega = \frac{2\pi \cdot \text{bw} \cdot \text{period}}{\text{rate}}, \quad w_0 = 1 - e^{-20\omega}, \quad w_1 = \frac{1.5\,\omega}{\text{period}}, \quad w_2 = \frac{\omega}{1.5}$$

$$\begin{aligned}
z_1[k] &= z_1[k-1] + w_0\big(w_1 e[k] - z_1[k-1]\big) \\
z_2[k] &= z_2[k-1] + w_0\big(z_1[k] - z_2[k-1]\big) \\
z_3[k] &= z_3[k-1] + w_2 z_2[k] \\
\text{corr}[k] &= 1 - (z_2[k] + z_3[k])
\end{aligned}$$

Cross-checking `src/modules/module-rtp/audio.c:261-311` against `spa/plugins/audioconvert/resample-native.c:256-298` establishes the exact closed-loop polarity and three operational failure modes:

1. **Inverted-Rate Interface Coupling**: `audio.c:277` defines fill error `error = target_buffer - avail - in_flight` (`error < 0` when the ring buffer is over-full). `spa_dll_update` returns `corr > 1.0` when `error < 0`, and `audio.c:295` calls `pw_stream_set_rate(impl->stream, 1.0 / corr)`. Inside the polyphase resampler (`resample-native.c:270`), `in_rate.value = round(in_rate.value / rate)` divides by `rate = 1.0 / corr`, yielding effective consumption rate `in_rate * corr`—draining the buffer faster when over-full.
2. **Absence of Rate/Slew Clamping & Single-Sample Resync Flush**: `audio.c:263` initializes the DLL with hardcoded `period = 128` (`spa_dll_set_bw(&impl->dll, SPA_DLL_BW_MIN, 128, impl->rate)`) regardless of graph quantum, clamps only the *error input* to `±ERROR_MSEC` (`2.0 ms` = `96` samples at 48 kHz, `stream.h:21`, `audio.c:288`), and passes `1.0 / corr` directly to `pw_stream_set_rate` without bounding rate deviation (`|corr - 1|`) or rate slew (`|Δcorr|`). Worse, on **any** single missing sample (`missing > 0`, `audio.c:304-310`), PipeWire flushes the entire packet queue (`rtp_stream_clear_queued_packets(impl)`) and resets `impl->have_sync = false`; likewise on any overrun `error < -target_buffer` (`audio.c:283-287`). Both events cause immediate hard audio discontinuities (`0 dBFS` click/pop transients).
3. **AES67 Direct-Timestamp Mode (`sess.ts-direct = true`) Sensitivity to PTPv2 Failover**: In AES67 / ST 2110-30 mode (`module-rtp-source.c:146-165`, `audio.c:206-207`), PipeWire bypasses the DLL entirely and pulls samples directly at `spa_io_clock::position`. If a PTPv2 Best Master Clock Algorithm (`BMCA`) grandmaster failover introduces a phase step exceeding one quantum (`SPA_ABS(rtp_timestamp_delta(ts, expected_ts)) > clock.duration`), `discont = true` resets the codec (`audio.c:299`) without smooth ASRC slew recovery.

Toy discrete-time FIFO probe (`run_pkg2_probes.py`, Probe 2A; `Basis: execution (exact spa_dll_update + toy 48 kHz / 128-sample FIFO model, target=480 samples = 10 ms)`):

| Scenario (`+50 ppm` Crystal Drift) | Controller | `min_fill` (smp) | `max_fill` (smp) | Peak Rate Deviation (ppm) | Hard Resync Clicks |
|---|---|---:|---:|---:|---:|
| Nominal `+50 ppm`, `0` step | PipeWire `spa_dll` (`BW_MIN=0.016`) | `480.0` | `491.1` | `42.9` | `0` |
| PTPv2 `+4 ms` (`+192 smp`) step | PipeWire `spa_dll` (unclamped `corr`) | `480.0` | `675.6` | **`416.7`** | `0` |
| PTPv2 `+4 ms` (`+192 smp`) step | Slew-clamped (`±150 ppm`, `5 ppm/blk`) | `480.0` | `675.6` | `150.0` | `0` |
| PTPv2 `-6 ms` (`-288 smp`) step | PipeWire `spa_dll` (unclamped `corr`) | `195.1` | `483.1` | **`415.8`** | `0` |
| PTPv2 `+12 ms` (`+576 smp > target`) | PipeWire `spa_dll` (`audio.c:283` check) | `480.0` | `490.4` | `37.1` | **`1` (click/drop)** |
| PTPv2 `+12 ms` (`+576 smp > target`) | Slew-clamped (`±150 ppm`, larger FIFO) | `480.0` | `1059.6` | `150.0` | `0` |

#### 1.2 Bandlimited Sinc & Farrow ASRC Time-Varying Ratio Overshoot and FIFO Invariance Bound
`Basis: normative + source + derived`

In `libsndfile/libsamplerate` (`0844c208f683527c08ea8a80acc13b398aa9c8bf`), `src/src_sinc.c:492-505` varies the conversion ratio linearly per output sample across `filter->out_count`:
```c
if (filter->out_count > 0 && fabs (state->last_ratio - data->src_ratio) > 1e-10)
    src_ratio = state->last_ratio + filter->out_gen * (data->src_ratio - state->last_ratio) / filter->out_count;
float_increment = filter->index_inc * (src_ratio < 1.0 ? src_ratio : 1.0);
...
input_index += 1.0 / src_ratio;
```
Two subtleties govern ASRC distortion and buffer safety:
- **Discontinuous Step vs. Block-Ramp Mismatch**: Calling `src_set_ratio()` (`src/samplerate.c:241-252`) directly overwrites `state->last_ratio = new_ratio`, bypassing the linear ramp and stepping the windowed-sinc cutoff scaling `float_increment` discontinuously. Conversely, if `src_process()` runs short of input before `filter->out_gen` reaches `filter->out_count`, `state->last_ratio = src_ratio` (`src_sinc.c:515`) stops partway along the ramp, introducing control-loop phase lag.
- **Farrow Polynomial Delay vs. Polyphase Sinc**: A Farrow (1988, DOI `10.1109/ISCAS.1988.15483`) structure evaluates fractional delay $\mu \in [0, 1)$ via $P+1$ fixed FIR sub-filters combined by Horner's rule $\sum_{k=0}^P \mu^k (h_k * x)[n]$, permitting sample-accurate $\mu[n]$ updates without coefficient table interpolation; however, rapid ratio slew $|\Delta R / \Delta t|$ still modulates instantaneous frequency (audible pitch wobble above $\sim 100\text{–}200\text{ ppm}$ for musical material) and shifts passband imaging.
- **Exact Click-Free ASRC FIFO Invariance Condition (`Basis: derived`)**: Let nominal rate be $f_s$, maximum sustained clock + servo offset be $R_{\max}$ (e.g. $150\text{ ppm}$), packet delay variation bound be $L_{\text{PDV}}$, and worst-case PTPv2 grandmaster step be $\Delta L$. Guaranteeing strict non-underrun/non-overrun invariance $L_{\min} \le L[k] \le L_{\max}$ without hard resync requires:
  $$L_{\text{target}} - L_{\min} > |\Delta L_-| + L_{\text{PDV}} + Q, \qquad L_{\max} - L_{\text{target}} > |\Delta L_+| + L_{\text{PDV}} + Q$$
  where $Q$ is the DSP block quantum, and minimum smooth absorption time is $T_{\text{rec}} = |\Delta L| / (f_s \cdot (R_{\max} - |\delta_{\text{xtal}}|))$. If a PTPv2 step exceeds the provisioned FIFO headroom (e.g. an unannounced TAI/UTC leap or cold GM switch > 10 ms), a dedicated step-detector must cross-fade (`5–10 ms` raised-cosine) rather than either saturating the DLL into wild pitch warble or performing an unwindowed ring flush.

---

### 2. Filtered-x LMS (`FxLMS`) Active Noise Control Stability and Adaptive Filter Numerical Defects

#### 2.1 The Kuo–Morgan $90^\circ$ Secondary-Path Phase-Error Stability Cliff
`Basis: normative + execution (toy narrowband ANC model)`

In feedforward Active Noise Control (`ANC`), reference noise $x[n]$ passes through primary acoustic path $P(z)$ to produce disturbance $d[n]$, while adaptive controller $W(z)$ drives a loudspeaker through electroacoustic secondary path $S(z)$ (DAC, power amp, speaker, cavity acoustics, error mic, ADC) yielding residual error $e[n] = d[n] - s[n] * y[n]$ where $y[n] = w^T[n] x[n]$. Because $S(z)$ is unknown exactly, `FxLMS` filters $x[n]$ through an estimate $\hat{S}(z)$ to form $\hat{x}[n] = \hat{s}[n] * x[n]$ and updates:
$$w[n+1] = (1 - \gamma) w[n] + \mu \, e[n] \, \hat{x}[n]$$

For narrowband excitation at frequency $\omega_0$ with secondary path phase error $\Delta\phi(\omega_0) = \angle S(e^{j\omega_0}) - \angle \hat{S}(e^{j\omega_0})$, Kuo & Morgan (1999, DOI `10.1109/5.763310`) prove that the mean weight error evolves via eigenvalue $\lambda \propto \mu |S(e^{j\omega_0})||\hat{S}(e^{j\omega_0})| e^{j\Delta\phi(\omega_0)}$, yielding the strict **Positive Real / Passivity Stability Condition** (for $\gamma = 0$):
$$\text{Re}\!\left\{S^*(e^{j\omega}) \hat{S}(e^{j\omega})\right\} = |S(e^{j\omega})|\,|\hat{S}(e^{j\omega})| \cos(\Delta\phi(\omega)) > 0 \iff |\Delta\phi(\omega)| < 90^\circ$$

Whenever physical perturbation—such as lifting a headphone earcup (breaking acoustic cavity seal), moisture ingress on an error microphone, or a $0.5\text{ ms}$ unmodeled latency shift at $1\text{ kHz}$ ($180^\circ$ phase shift!)—pushes $|\Delta\phi(\omega)| > 90^\circ$, $\cos(\Delta\phi) < 0$ **reverses the gradient sign**, turning negative feedback cancellation into positive-feedback exponential runaway until the power amplifier rails (`> 120 dB SPL`, causing immediate hearing-damage risk).

**Leaky-FxLMS + $H_\infty$ Weight-Ball Projection + Freeze Shield**:
Adding leakage $\gamma \in (0, 1)$ shifts the eigenvalue real part positively (expanding the stable region to $\cos(\Delta\phi) > -\gamma / (\mu P_x |S||\hat{S}|)$ at the cost of steady-state cancellation bias), while enforcing a hard weight-norm projection $\|w[n]\|_2 \le W_{\max}$ (or spectral $H_\infty$ bound $\max_\omega |W(e^{j\omega})| \le W_{\max}$, capping acoustic output power unconditionally) plus an error-energy / online-coherence divergence detector that freezes adaptation (`mu = 0`) when error SPL rises above primary noise prevents unbounded howling even under full $180^\circ$ inversion.

Toy narrowband 2-tap quadrature FxLMS sweep (`run_pkg2_probes.py`, Probe 2B; `Basis: execution (toy model of FxLMS, not a hardware ANC headset)`, $f_0 = 500\text{ Hz}, f_s = 48\text{ kHz}, \mu = 0.005, 4000\text{ steps}$):

| Phase Error $\Delta\phi$ | $\cos(\Delta\phi)$ | Unprotected FxLMS ($\max\|w\|_2$, final $e$, div step) | Leaky ($\gamma=10^{-3}$) + Ball ($W_{\max}=2.0$) + Freeze ($+6\text{ dB}$) |
|---:|---:|---|---|
| $0^\circ$ | `+1.000` | `1.00`, `-88.4 dB`, converged | `0.72`, `-13.4 dB`, active (leakage bias visible) |
| $45^\circ$ | `+0.707` | `1.07`, `-63.8 dB`, converged | `0.78`, `-13.5 dB`, active |
| $75^\circ$ | `+0.259` | `1.46`, `-24.8 dB`, slow convergence | `0.99`, `-13.0 dB`, active |
| $85^\circ$ | `+0.087` | `1.79`, `-10.3 dB`, marginal | `1.13`, `-12.6 dB`, active |
| $90^\circ$ | `0.000` | `2.04`, `-2.9 dB`, undamped oscillation | `1.23`, `-12.5 dB`, active |
| $95^\circ$ | `-0.087` | **`3.44`, `+4.6 dB`, growing** | `1.35`, `-12.1 dB`, stabilized by leakage |
| $120^\circ$ | `-0.500` | **`148.0`, `+40.0 dB`, howling runaway** | `2.00` (clamped), `+1.6 dB`, bounded |
| $180^\circ$ | `-1.000` | **`>1000`, `+55.4 dB` (rail at step 2777)** | `2.00` (clamped), `+7.1 dB`, **frozen** |

*Critical Trade-Off Observed*: Unconditional static leakage $\gamma = 10^{-3}$ stabilizes up to $\sim 95^\circ$ but degrades nominal $0^\circ$ attenuation from `-88.4 dB` to `-13.4 dB` in this toy model; practical ANC systems therefore pair *small* baseline leakage ($\gamma \sim 10^{-5}\text{–}10^{-4}$) with hard $H_\infty$/$\ell_2$ norm projection and fast divergence freezing (`< 5 ms`).

#### 2.2 Upstream Defects in `LCAV/pyroomacoustics` and `ARM-software/CMSIS-DSP`
`Basis: source + execution`

Direct inspection of both adaptive-filtering codebases exposed concrete numerical defects that destabilize real-time audio even at $0^\circ$ phase error:

1. **`LCAV/pyroomacoustics` (`08d16968f8db414affaf84771a650358a7961446`, `pyroomacoustics/adaptive/lms.py:48-49, 111-118`)**:
   - `NLMS.update()` computes `self.w += self.mu * e * self.x / np.inner(self.x, self.x)` (`line 49`) with **zero regularization constant $\epsilon$** (`BlockLMS.update` does the identical unguarded division `X = (X.T / norm).T` at `lines 112-116`). Because `AdaptiveFilter.reset()` zero-initializes `self.x`, feeding a single zero sample at startup (or any silent audio pause longer than `length` samples) produces `0.0 / 0.0 = NaN`, permanently destroying `self.w`.
   - `pyroomacoustics/adaptive/__init__.py` exports only `RLS`, `BlockRLS`, `NLMS`, `BlockLMS`, and `SubbandLMS`—no `FxLMS`, no leakage parameter $\gamma$, and no weight-norm clamp.
2. **`ARM-software/CMSIS-DSP` (`9f64ba31591e527c505951943b4b95b0eb2f834b`, `Source/FilteringFunctions/arm_lms_norm_f32.c:214-215, 262, 400-401, 454`) — Running-Energy `float32` Sign Inversion**:
   ```c
   /* Update the energy calculation */
   energy -= x0 * x0;
   energy += in * in;
   ...
   /* epsilon value 0.000000119209289f */
   w = (e * mu) / (energy + 0.000000119209289f);
   ```
   Both the `ARM_MATH_NEON` (`lines 214-215, 262`) and scalar (`lines 400-401, 454`) implementations maintain sliding-window input energy via catastrophic-cancellation subtraction `energy -= x0 * x0` in single-precision IEEE 754 `float32_t` without clamping `energy = fmaxf(energy, 0.0f)` or periodically recomputing $\sum x_k^2$. When a full-scale transient (`1.0`, whose 64-tap sum `64.0` has ULP $= 2^{-17} \approx 7.63 \times 10^{-6}$, `64x` larger than `eps = 1.192e-7f`!) transitions into quiet audio (`1e-4`) and silence (`0.0`), rounding drift leaves `energy < -eps`.
   - Exact `float32` witness (`run_pkg2_probes.py`, Probe 2C; `Basis: source + execution`): over `20` cycles of `[1.0]*64 + [1e-4]*64 + [0.0]*128` (`5,120` strictly in-range `[-1, +1]` audio samples), `energy` drifts to **`-6.400002235e-7`**, driving `energy + 0.000000119209289f = -5.207909339e-7` across **`2,320/5,120` samples** and flipping the NLMS adaptation step to **`-1.920e+6 * e * mu`** (instantaneous sign-inverted blowup!).
3. **`ARM-software/CMSIS-DSP` (`Source/FilteringFunctions/arm_lms_norm_q31.c:52-59, 117-119, 180`) — Q31 Wrapping & Unsaturated Error**:
   - The `2.62` 64-bit accumulator has only 1 guard bit and **wraps on overflow** rather than saturating (`lines 53-58`), requiring caller input pre-scaling by $\log_2(\text{numTaps})$ bits.
   - `energy` is clamped via `clip_q63_to_q31(energy)` (`line 119`) into `[0, 1)`, so if $\sum x_k^2 \ge 1.0$, saturation permanently desynchronizes the incremental `energy -= x0*x0` tracker when loud samples exit the delay line.
   - Error computation `e = *pRef++ - (q31_t) acc;` (`line 180`) uses plain C signed 32-bit subtraction (not saturating `__QSUB`), so opposing full-scale reference and filter outputs (`+0.8 - (-0.8)`) overflow signed `int32_t` (UB / two's-complement wrap), inverting error sign!

---

### 3. MIDI 2.0 UMP 16-Bit Jitter-Reduction (`JR`) Timestamps and Value Scaling

#### 3.1 `M2-104-UM` 31,250 Hz (`32 µs`) JR Clock Rollover and `AM_MIDI2.0Lib` Decode Bug
`Basis: normative + source + execution`

Under MMA/AMEI `M2-104-UM` (§4, Jitter Reduction Timestamps), a 32-bit Utility Message (`Message Type 0x0`) carries a 4-bit Status (`0x1` = JR Clock, `0x2` = JR Timestamp) in bits `[23:20]` and a **16-bit unsigned counter in bits `[15:0]`**:
- **Clock Frequency & Exact Rollover**: The JR clock ticks at **$31{,}250\text{ Hz}$** (1 tick = $\frac{1}{31{,}250}\text{ s} = \mathbf{32.0\,\mu\text{s}}$, matching historical MIDI 1.0 `31.25 kbaud` serial bit duration—not `31.25 µs`, which would yield `2.048 s`!). Thus a 16-bit counter wraps modulo $2^{16} = 65{,}536$ ticks every:
  $$T_{\text{wrap}} = 65{,}536 \times 32.0\,\mu\text{s} = \mathbf{2.097152\text{ s}}$$
- **Modular Causal Ordering**: Naive integer comparison `ts - now` fails catastrophically at the 16-bit rollover boundary: e.g., at `now = 0xFFF0` and `ts = 0x0010` (`+32` ticks = `+1024 µs` in the future), naive subtraction yields `-65,504` ticks (`-2.096128 s`), causing schedulers to either fire notes late/immediately or stall for 2.1 seconds. Wrapping subtraction cast to signed two's-complement 16-bit `int16_t((uint16_t)(ts - now))` uniquely resolves causal offset across rollover **iff** end-to-end network jitter plus lookahead stays strictly within the half-window $\pm 32{,}768 \times 32.0\,\mu\text{s} = \pm \mathbf{1.048576\text{ s}}$ (Probe 2D).
- **Verified Upstream Bug in `midi2-dev/AM_MIDI2.0Lib` (`7fa1b0c59acf31fbaa55a0e45042663d9a8b7ee4`)**:
  - `include/umpMessageCreate.h:57-62` correctly packs the 16-bit timestamp into bits `[15:0]`:
    ```cpp
    inline uint32_t mt0JRClock(uint16_t clockTime) { return ((UTILITY_JRCLOCK + 0L) << 20) + clockTime; }
    inline uint32_t mt0JRTimeStamp(uint16_t timestamp) { return ((UTILITY_JRTS + 0L) << 20) + timestamp; }
    ```
  - **Defect**: `src/umpProcessor.cpp:41-47` decodes Utility Messages with an erroneous right-shift by 16 bits:
    ```cpp
    if(mt == UMP_UTILITY && utilityMessage!= nullptr){ //32 bits Utility Messages
        ...
        mess.status = (umpMess[0] >> 20) & 0xF;
        mess.value = (umpMess[0] >> 16) & 0xFFFF;
        utilityMessage(mess);
    }
    ```
    For `mt0JRTimeStamp(0x1234) = 0x00201234`, `umpProcessor.cpp:46` extracts **`0x0020`** instead of **`0x1234`** (Probe 2D), completely destroying every JR Clock and JR Timestamp dispatched through `umpProcessor`.

#### 3.2 MIDI 1.0-to-2.0 Bit-Replication Upscaling Algebraic Properties & `RtMidi` Real-Time Gaps
`Basis: normative + source + execution`

MIDI 2.0 (`M2-115-U`) defines upscaling from `srcBits` ($m \in \{7, 14\}$) to `dstBits` ($n \in \{16, 32\}$) via piecewise left-shift (for `srcVal <= 2^(m-1)`) and lower-`m-1`-bit replication (for `srcVal > 2^(m-1)`), implemented in `AM_MIDI2.0Lib` `include/utils.h:195-235`. Exhaustive execution over all `128` 7-bit and `16,384` 14-bit inputs (Probe 2D) establishes:
- **Exact Algebraic Structure (Injective Retraction, Not Full Bijection)**: Because $2^7 \ll 2^{32}$, `scaleUp` is **not** a bijection onto $[0, 2^{32}-1]$; rather, `(scaleUp, scaleDown)` forms a **strictly monotone, endpoint- and center-exact injective embedding with exact right-shift retraction**:
  - `scaleUp(0) = 0`, `scaleUp(2^(m-1)) = 2^(n-1)` (`64 -> 0x80000000`, `8192 -> 0x80000000`), `scaleUp(2^m - 1) = 2^n - 1` (`127 -> 0xFFFFFFFF`, `16383 -> 0xFFFFFFFF`),
  - `scaleUp(x) < scaleUp(y)` for all `x < y`,
  - `scaleDown(scaleUp(x, m, n), n, m) == x` for `100%` of inputs (`128/128` for `7->16` & `7->32`; `16,384/16,384` for `14->32`).
- **C++ UB Edge Case (`include/utils.h:202-204`)**: For `srcBits == 1`, `return (1 << dstBits) - 1L;` executes signed 32-bit shift `1 << 32` (undefined behavior in C++) when `dstBits == 32`.
- **`thestk/rtmidi` (`00d855f31fbaeb196da2c0a3507d92f0d6051efb`) Real-Time & UMP Limitations**:
  - `MidiInWinMidi2::midi_in_callback` (`RtMidi.cpp:6568-6699`) explicitly **drops all UMP Utility (`MT=0x0`, including JR Timestamps) and MIDI 2.0 Channel Voice (`MT=0x4`) packets** (`lines 6672-6677`), allocates heap memory (`message.bytes.push_back`, `lines 6609-6611`), acquires `std::lock_guard<std::mutex>` (`line 6695`, and `send_mtx` at `line 6710`), and converts monotonic OS timestamps into `double` deltas (`line 6689`)—violating strict lock-free/alloc-free audio-thread contracts.
  - On macOS CoreMIDI, `RtMidi.cpp:1997-2009` documents an upstream CoreMIDI MIDI 1.0/UMP translation defect where combining a real-time byte (`>= 0xF8`) with multi-byte data in a single `MIDISend()` injects spurious `F7`/`F0` framing and loses payload bytes, forcing RtMidi to split real-time bytes into separate `MIDISend()` calls.

---

### 4. Six-Level Performance and Resource Footprint Analysis (`L1–L6`)

`Basis: documentation + source + derived` (noting analytical/published estimates where compiled DSP benchmarks on embedded targets were not locally executed).

| Level | AES67 / ASRC (`PipeWire` / `libsamplerate`) | Adaptive ANC (`CMSIS-DSP` / `pyroomacoustics`) | MIDI 2.0 UMP (`AM_MIDI2.0Lib` / `RtMidi`) |
|---|---|---|---|
| **(L1) Human & Agent Authoring Velocity** | Core DLL (`dll.h`, 66 LoC) and rate updater (`resample-native.c`, ~600 LoC) are small, but subtle feedback-sign inversions (`1.0 / corr` vs `in_rate / rate`) and PTP/buffer state machines drive high review cost. Proving FIFO invariance + slew bounds in Lean/SMT takes ~400–800 LoC (~5–8x proof-to-code ratio). | Pure LMS/NLMS is ~100–300 LoC per precision (`arm_lms_norm_f32.c`, `lms.py`), yet adding safe $H_\infty$/$\ell_2$ projection, energy-drift immunity, and secondary-path monitoring is high-leverage (+30–50 LoC C99). Formalizing frequency-domain passivity ($\text{Re}\{S^*\hat{S}\}>0$) requires complex-analysis/Parseval infrastructure (~1,000+ LoC). | `scaleUp`/`scaleDown` (~40 LoC) and UMP framing (~500 LoC) are simple; exhaustive bit-vector verification takes <50 LoC in Z3/Lean (`< 2x` ratio). OS backend quirks (CoreMIDI UMP splitting, Windows MIDI Services, ALSA seq) bloat `RtMidi.cpp` to `9,369` LoC. |
| **(L2) Toolchain & Framework Build Time** | `libsamplerate` builds in ~5–15 s (`cmake`/`gcc`); `PipeWire` full meson build takes ~1–3 min (single SPA plugin rebuild ~2–5 s). | `CMSIS-DSP` full library builds in ~20–60 s (`arm-none-eabi-gcc`/`clang`); single `arm_lms_*` object <1 s. `pyroomacoustics` (Python/Cython) builds C++ extensions in ~30–90 s. | `AM_MIDI2.0Lib` builds in <5 s; `RtMidi` single translation unit (`RtMidi.cpp`) compiles in ~2–5 s. |
| **(L3) Compilation, Elaboration & Synthesis Latency** | Static sinc polyphase tables (`libsamplerate` `fastest_coeffs.h` / `high_qual_coeffs.h`, PipeWire precomputed Kaiser/Blackman filters) build at compile or init time (<5 ms). Linear-system stability checks (DLL Jury/Schur-Cohn pole radii) discharge in <10 ms interactively. | Offline secondary-path FIR identification takes ~1–5 s on hardware; SMT verification of fixed-point Q31 shift/saturation bounds (`clip_q63_to_q31`) runs in <50 ms per loop body. | Exhaustive SMT or brute-force verification of `7->32` (`128` cases) and `14->32` (`16,384` cases) `scaleUp`/`scaleDown` and `u16` JR modular arithmetic completes in <20 ms interactively. |
| **(L4) Generated Code Execution Performance** | PipeWire native polyphase resampler (`32–64` taps, AVX2/NEON SIMD) costs ~15–40 cycles/output sample (~0.5–1.5% of one core for 48 kHz stereo); `libsamplerate` `SRC_SINC_BEST_QUALITY` (longer half-filter) costs ~150–400 cycles/sample. Audio callback `p99.9` jitter must stay strictly below quantum (`1 ms` = `48` samples at 48 kHz for AES67 1 ms packet time). | At 48 kHz (`20.8 µs`/sample budget) with `N=128` taps: `arm_lms_norm_f32` requires ~$2N + 10 \approx 266$ FLOPs/sample (~70–100 cycles/sample on Cortex-A NEON `vmlaq_f32`; ~300–500 cycles on Cortex-M4F scalar, ~1–2% CPU at 480 MHz). Adding leaky decay + $\ell_2$ norm check adds ~$N$ MACs (~15–25% overhead) and keeps a `32`-sample block well under `50 µs` WCET. | UMP decode/encode + `scaleUp` + `i16` JR unwrap executes in `< 15` CPU cycles (~5 ns), zero heap allocations, zero locks—orders of magnitude faster than `RtMidi`'s mutex+`std::vector` callback path (~0.5–5 µs + unbounded OS lock contention). |
| **(L5) Proof / Certificate Verification Speed** | Discrete-time FIFO invariant certificates and Schur-Cohn DLL pole bounds verify in <1 ms; runtime slew/bound monitor costs 4 comparisons/block (<5 ns). | Runtime $\ell_2$/$H_\infty$ weight-norm certificate (`sum(w[i]^2) <= W_max^2`) verifies in $O(N)$ MACs (<1 µs for 128 taps) on every block; offline FFT $H_\infty$ spectral check takes <20 µs for 256-point FFT. | Exhaustive lookup/bit-vector proof of `M2-115-U` `scaleUp`/`scaleDown` verifies in <5 ms; runtime causal JR window check (`abs(int16_t(ts - now)) < J_max`) is 2 integer ops (<1 ns). |
| **(L6) RAM, Disk & Binary Footprints** | `libsamplerate` coefficient tables dominate binary size (~1.5 MB `.so` for `BEST_QUALITY` sinc table); PipeWire `resample-native` computes smaller runtime tables (~16–128 KB RAM/stream). AES67 `10–100 ms` stereo float32 ring buffer uses `3.8–38.4 KB` RAM. | 128-tap `FxLMS` state (`x`, `x_hat`, `w`, `s_hat`) consumes only `4 × 128 × 4 B = 2.0 KB` SRAM (`arm_lms_norm_q31` adds `256 B` reciprocal table)—fitting entirely in MCU TCM / L1 cache (~1–5 mW incremental power on ANC DSP). | Lock-free SPSC ring of `256` 128-bit UMPs uses `4 KB` static SRAM; `AM_MIDI2.0Lib` utility headers compile to `< 4 KB` `.text`. |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

#### 5.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)
`Basis: source + derived`

- **Clock-Domain Polarity & Unit Confusion**: Two recurring human-comprehension traps appeared directly in our primary-source audit:
  1. **Rate Inversion Sign Trap**: PipeWire's `audio.c:295` passes `1.0 / corr` to `pw_stream_set_rate`, which `resample-native.c:270` divides `in_rate` by (`in_rate / (1/corr) = in_rate * corr`). Without dimensional types distinguishing `OutputPerInputRatio` from `InputPerOutputRatio`, humans (and LLMs!) routinely invert ASRC feedback polarity, turning a stable DLL into runaway FIFO overflow/underflow.
  2. **Clock-Frequency vs. Tick-Period Conflation (`31.25 kHz` vs. `32 µs`)**: Because classic MIDI 1.0 runs at `31.25 kbaud` (`31,250 Hz`), engineers repeatedly misquote MIDI 2.0's JR tick period as `31.25 µs` instead of $1 / 31{,}250\text{ Hz} = 32.0\,\mu\text{s}$—producing a `2.4%` timing error (`2.048 s` vs. `2.097152 s` rollover).
- **Silent Bit-Field & Floating-Point Footguns**: `AM_MIDI2.0Lib`'s `umpProcessor.cpp:46` (`(umpMess[0] >> 16) & 0xFFFF`) compiles cleanly with zero warnings yet discards every JR timestamp; `CMSIS-DSP`'s `arm_lms_norm_f32.c:214-215` looks textbook-clean to a human code reviewer (`energy -= x0*x0; energy += in*in;`) while concealing a catastrophic `float32` cancellation sign flip after ordinary audio transients!
- **Physical-to-Digital Gap in ANC**: Human DSP engineers designing LMS filters in offline textbooks (`pyroomacoustics/lms.py`) assume static plant identity $S(z) = 1$, leaving out secondary-path phase lag, earcup seal breaks, and amplifier saturation—none of which surface until hardware howling threatens physical hearing safety.

#### 5.2 Simplicity, Orthogonality & Universal Model Refinement (`C2`)
`Basis: derived`

Four minimal, orthogonal abstractions eliminate these ad-hoc traps without bloating consumer code:

1. **Oriented Ratio & Slew-Bounded FIFO Servo (`AsrcRate<InPerOut, MaxPpm, MaxSlewPpm>`)**: Separate `InPerOut` vs. `OutPerIn` ratios at the type level (`0` runtime bytes) and unify step detection, cross-fade fallback, and slew-limited DLL tracking into a single state machine parameterized by `(L_min, L_target, L_max, R_max, Slew_max)`. This replaces split logic across `dll.h`, `audio.c`, and `resample-native.c`, making FIFO non-underrun/non-overrun a local invariant check.
2. **Passivity-Bounded Adaptive Filter (`PassiveFxLms<Taps, WMax, GammaMin, MaxPhaseMargin>`)**: Bundle three invariants into the adaptive filter state itself rather than external callers:
   - Exact non-negative energy maintenance (`energy = fmaxf(recompute_every_K_blocks(x), EPS_FLOOR)` with `EPS_FLOOR >= 1e-4f`, eliminating CMSIS-DSP's `float32` negative-denominator sign flip and `pyroomacoustics`'s `0/0` NaN in 3 lines of C99),
   - Saturating error arithmetic (`__QSUB` in Q31) + leaky $\ell_2$/$H_\infty$ weight-ball projection ($\|w\|_2 \le W_{\max}$),
   - Online error-to-reference energy ratio / phase-margin freeze guard (`if (e_rms > k * d_rms) freeze()`).
3. **Bit-Slice-Specified UMP Word & Modular Wrapping Clock (`JrTimestamp<FreqHz=31250, Bits=16>`)**: Generating UMP pack/unpack codecs from a single declarative bit-layout specification (`MT[31:28]`, `Status[23:20]`, `Payload[15:0]`) makes the `umpMessageCreate.h` vs. `umpProcessor.cpp:46` shift mismatch structurally impossible; wrapping `uint16_t` timestamps in a `ModularClock<16, 31250>` type whose *only* subtraction returns `SignedDeltaTicks` (clamped/rejected outside $\pm 32{,}768$) eliminates rollover bugs globally.
4. **Lock-Free Allocation-Free Real-Time Audio Capability (`RealtimeSafe`)**: Isolate audio/MIDI callbacks via SPSC ring buffers and preallocated fixed-size UMP slots (no `std::vector`, no `std::mutex`, statically checked via compiler/sanitizer attributes like Clang `[[clang::nonblocking]]` / `RTSan`).

---

### 6. End-to-End Solution and Implementation Validation (`V1–V4`)

`Basis: normative + documentation + execution (micro-probes) + derived`

- **(V1) Specification Adequacy, Mutation & Non-Vacuity Validation**:
  - *Exhaustive Codec & Scaling Verification*: Exhaustively test all `128` 7-bit, `16,384` 14-bit, and `2` 1-bit `M2-115-U` scaling cases plus `65,536 × 256` modular JR rollover pairs, verifying `scaleDown(scaleUp(x)) == x`, exact `0 / mid / max` anchors, and round-trip `decode(encode(ump)) == ump` (which immediately kills `AM_MIDI2.0Lib` `umpProcessor.cpp:46` and `utils.h:203` UB!).
  - *Passivity & Servo Mutant Kill*: Inject systematic mutants into the ANC and ASRC controllers (removing leakage, disabling $W_{\max}$ ball projection, deleting `fmaxf(energy, 0.0f)`, inverting `1/corr` polarity, removing rate slew clamping) and verify 100% mutant detection under automated test harnesses.
- **(V2) Compiler, Lowering & Numerical Precision Fuzzing**:
  - *SIMD Fixed/Float Differential Verification*: Differentially fuzz ARM `NEON`/`Helium` `Q31` and `FP32` LMS/FIR/ASRC kernels against an `FP64` reference under worst-case dynamic-range transitions (full-scale impulse $\rightarrow$ `-80 dBFS` silence $\rightarrow$ step DC offset) to verify `THD+N` targets (e.g. `< -120 dB` for 24-bit broadcast ASRC) and catch `CMSIS-DSP`-style `energy` cancellation drift and `Q31` accumulator wraparound.
  - *ASRC Swept-Ratio Differential Check*: Sweep time-varying `src_ratio(t)` across `libsamplerate` vs. `PipeWire` `resample-native` vs. double-precision reference sinc, bounding passband ripple, aliasing rejection, and step-change transient clicks.
- **(V3) Concurrency, Real-Time Determinism & Hardware Leakage Validation**:
  - *`RealtimeSanitizer` (`RTSan`) & Lock-Free Model Checking (`GenMC`/`Loom`)*: Instrument audio/MIDI callbacks with Clang `RealtimeSanitizer` (`RTSan`) / `[[clang::nonblocking]]` to flag any hidden `malloc`, `free`, `std::vector` growth, `pthread_mutex_lock`, or blocking syscall (which immediately flags `RtMidi.cpp:6609,6695,6710`), and verify SPSC/MPSC audio ring buffers under `ARMv8` weak-memory semantics via `GenMC`/`Loom`.
  - *Fixed-Point Saturation & Hardware Timer Jitter Injection*: Inject realistic OS scheduling jitter (`50–500 µs`) and PTPv2 `phc2sys`/`ptp4l` step faults into deterministic audio-graph simulation.
- **(V4) Plant Falsification, Acoustic HIL Replay & Human Mental-Model Validation**:
  - *Signal Temporal Logic (`STL`) Acoustic Howling Falsification*: Use black-box CPS falsifiers (`S-TaLiRo` / `Psy-TaLiRo` / `Breach`) to search adversarial time-varying acoustic secondary-path perturbations $S(z, t)$ (sudden $90^\circ\text{–}180^\circ$ phase inversions, resonant earcup leaks, broadband impulses) against safety specification $\square_{[0, T]}\big(\text{SPL}_{\text{ear}}(t) \le \text{SPL}_{\max} \land \|w(t)\|_2 \le W_{\max}\big)$, verifying strictly positive STL robustness margin across worst-case adversarial trajectories (where unprotected FxLMS fails catastrophically).
  - *Acoustic Mannequin & Broadcast PTP HIL Replay*: Replay recorded PTPv2 grandmaster switchover PCAPs into AES67 receivers (measuring click/THD transients and FIFO watermark margins) and test physical ANC prototypes on KEMAR/HATS head-and-torso acoustic simulators under mechanical earcup lift/reseat cycles, verifying `> 30°` online phase-margin freeze response (`< 5 ms`) prior to audible howling.
  - *Operator/Developer Litmus Testing*: Validate that refactored typed APIs (`InPerOut` ratio types, `ModularClock<16, 31250>`, `PassiveFxLms`) prevent polarity inversions and `31.25 µs` vs. `32 µs` timing miscalculations in developer litmus trials.

## Boundaries

- **Compiled C/C++ Execution & Hardware Acoustic HIL Measurements**: **not examined** directly in this environment (no physical KEMAR acoustic mannequin, PTP hardware timestamping NIC, or compiled ARM Cortex-M/A board execution was performed). Exact upstream defects quote pinned source lines directly; numerical evidence distinguishes exact algebraic/IEEE-754 reproductions of upstream code (`PipeWire spa_dll_update`, `CMSIS-DSP float32 energy recurrence`, `AM_MIDI2.0Lib scaleUp/scaleDown` & `umpProcessor.cpp:46` shift) from clearly labeled Python toy models (`Probe 2A` FIFO loop and `Probe 2B` narrowband 2-tap FxLMS).
- **Broadband Multi-Channel (`MIMO`) FxLMS Plant Coupling**: **not examined** in Probe 2B (which models single-frequency 2-tap quadrature SISO FxLMS). In multi-channel `MIMO` cabin ANC ($M$ speakers $\times$ $K$ error mics), the scalar condition $\text{Re}\{S^*\hat{S}\} > 0$ generalizes to strict positive-definiteness of the Hermitian part $\frac{1}{2}\big(\hat{S}^H(e^{j\omega}) S(e^{j\omega}) + S^H(e^{j\omega}) \hat{S}(e^{j\omega})\big) \succ 0$ across all frequencies $\omega$, and norm bounding lifts to maximum singular value $\bar{\sigma}(W(e^{j\omega})) \le W_{\max}$.
- **`ARM_MATH_MVEF` (Helium) Vectorization in CMSIS-DSP LMS**: **known not to apply** to `arm_lms_f32.c`, `arm_lms_norm_f32.c`, or `arm_lms_norm_q31.c` at `ARM-software/CMSIS-DSP` @ `9f64ba31591e527c505951943b4b95b0eb2f834b`, which contain only `ARM_MATH_NEON` and scalar/unrolled loops (`ARM_MATH_LOOPUNROLL`).
- **`PipeWire` `spa/plugins/audioconvert/resample-peaks.c` as an ASRC**: **known not to apply** — inspection of `resample-peaks.c:1-35` confirms it implements peak-amplitude visualization downsampling (`max_f[]`), whereas audio-rate ASRC is implemented in `resample-native.c`.
- **Full `RtMidi` Non-Windows Backends (ALSA, JACK, WinMM)**: **not examined** exhaustively beyond CoreMIDI (`RtMidi.cpp:1261-1445, 1985-2015`) and Windows MIDI Services (`MidiInWinMidi2`, `RtMidi.cpp:6500-6720`).
- **MIDI 2.0 JR Clock Frequency Correction**: Note that the JR tick duration is **`32.0 µs`** (`1 / 31,250 Hz`), yielding rollover `65,536 × 32.0 µs = 2.097152 s`; claims stating a `31.25 µs` tick with `2.097152 s` rollover are algebraically inconsistent (`65,536 × 31.25 µs = 2.048 s`) and reflect conflation of the `31.25 kHz` clock frequency with its reciprocal `32 µs` period.

## Evidence

### Upstream Source Citations (Pinned Revisions, Observed `2026-11-19`)

1. **`PipeWire/pipewire` @ `0e30a575c2e279bd7a8975e403168f8ac906cc7e`**:
   - `spa/include/spa/utils/dll.h:25-61`: `SPA_DLL_BW_MAX = 0.128`, `SPA_DLL_BW_MIN = 0.016`, 3rd-order `spa_dll_set_bw` and `spa_dll_update` returning `1.0 - (z2 + z3)`.
   - `spa/plugins/audioconvert/resample-native.c:256-298`: `impl_native_update_rate()` sets `in_rate.value = round(in_rate.value / rate)` (`line 270`), switching between `process_inter`, `process_copy`, and `process_full`.
   - `spa/plugins/audioconvert/resample-peaks.c:1-35`: peak-meter downsampler (`max_f[]`), not audio ASRC.
   - `src/modules/module-rtp/stream.h:16-31`: `DEFAULT_RATE = 48000`, `ERROR_MSEC = 2.0f`, `DEFAULT_SESS_LATENCY = 100.0f`, `DEFAULT_MIN_PTIME = 2.0f`.
   - `src/modules/module-rtp/audio.c:205-315`: direct-timestamp discontinuity threshold (`lines 206-207`), hardcoded `period = 128` DLL init (`line 263`), overrun resync at `error < -target_buffer` (`lines 283-287`), error clamp `SPA_CLAMPD(error, -max_error, max_error)` (`line 288`), unclamped `pw_stream_set_rate(impl->stream, 1.0 / corr)` (`line 295`), and single-sample underrun full queue flush (`lines 304-310`).
   - `src/modules/module-rtp-source.c:123-165`: documents constant-latency DLL mode vs. AES67 direct-timestamp mode (`sess.ts-direct`).
2. **`libsndfile/libsamplerate` @ `0844c208f683527c08ea8a80acc13b398aa9c8bf`**:
   - `src/src_sinc.c:445-521`: `sinc_mono_vari_process()` linear per-sample ratio ramp over `filter->out_count` (`lines 492-493`), cutoff scaling `float_increment = index_inc * (src_ratio < 1 ? src_ratio : 1)` (`line 495`), and `state->last_ratio = src_ratio` (`line 515`).
   - `src/samplerate.c:240-252`: `src_set_ratio()` overwrites `state->last_ratio = new_ratio` directly with no slew ramp.
3. **`LCAV/pyroomacoustics` @ `08d16968f8db414affaf84771a650358a7961446`**:
   - `pyroomacoustics/adaptive/lms.py:34-50, 86-120`: `NLMS.update()` unregularized `self.w += self.mu * e * self.x / np.inner(self.x, self.x)` (`line 49`) and `BlockLMS.update()` unregularized `X = (X.T / norm).T` (`lines 112-116`).
   - `pyroomacoustics/adaptive/__init__.py`: exports `RLS`, `BlockRLS`, `NLMS`, `BlockLMS`, `SubbandLMS` (no `FxLMS`).
4. **`ARM-software/CMSIS-DSP` @ `9f64ba31591e527c505951943b4b95b0eb2f834b`**:
   - `Source/FilteringFunctions/arm_lms_norm_f32.c:161-315, 368-520`: incremental `float32_t` `energy -= x0 * x0; energy += in * in;` (`lines 214-215, 400-401`) and `w = (e * mu) / (energy + 0.000000119209289f);` (`lines 262, 454`) without non-negativity clamping.
   - `Source/FilteringFunctions/arm_lms_norm_q31.c:52-59, 117-119, 180`: `2.62` wrapping accumulator (`lines 53-58`), saturating `q31_t` running energy (`lines 117-119`), unsaturated `e = *pRef++ - (q31_t) acc;` (`line 180`).
   - `Source/FilteringFunctions/arm_lms_f32.c:167-531`: NEON (`vmlaq_f32`) + scalar unrolled paths without leakage or Helium MVE.
5. **`midi2-dev/AM_MIDI2.0Lib` @ `7fa1b0c59acf31fbaa55a0e45042663d9a8b7ee4`**:
   - `include/umpMessageCreate.h:57-62`: packs 16-bit `clockTime`/`timestamp` into low bits `[15:0]`.
   - `src/umpProcessor.cpp:41-47`: buggy Utility Message extraction `mess.value = (umpMess[0] >> 16) & 0xFFFF;` (`line 46`) discards bits `[15:0]`.
   - `include/utils.h:195-235`: `scaleUp()` and `scaleDown()` bit-replication upscaling and `srcBits == 1` shift `(1 << dstBits) - 1L` (`line 203`).
6. **`thestk/rtmidi` @ `00d855f31fbaeb196da2c0a3507d92f0d6051efb`**:
   - `RtMidi.cpp:1997-2009`: CoreMIDI MIDI 1.0/UMP real-time byte splitting workaround.
   - `RtMidi.cpp:6568-6715`: `WinMidiServicesClass::midi_in_callback` drops UMP `MT=0x0` (Utility/JR) and `MT=0x4` (MIDI 2.0 CVM) (`lines 6672-6677`), allocates via `std::vector::push_back`, locks `std::mutex`, and outputs `double` delta timestamps (`line 6689`).

### Reproducible Execution Probes (Observed `2026-11-19`, Python 3 on Linux x86_64)

1. **Probe 2A (Exact `PipeWire spa_dll_update` + Toy 48 kHz / 128-Sample FIFO Model)**:
   - Nominal `+50 ppm` drift: `min_fill = 480.0`, `max_fill = 491.1`, `peak_rate_dev = 42.9 ppm`, `resync_clicks = 0`.
   - `+4 ms (+192 smp)` PTPv2 step: unclamped PipeWire DLL peaks at `416.7 ppm` (`max_fill = 675.6`); slew-clamped (`±150 ppm`, `5 ppm/blk`) caps rate deviation at `150.0 ppm`.
   - `+12 ms (+576 smp > target=480)` PTPv2 step: PipeWire hits overrun resync (`resync_clicks = 1`); slew-clamped absorbs smoothly (`max_fill = 1059.6`, `resync_clicks = 0`) if FIFO capacity exceeds `1060` samples.
2. **Probe 2B (Toy 2-Tap Quadrature FxLMS Phase-Error Sweep, `mu=0.005`, `4000` steps)**:
   - Unprotected FxLMS converges at `0°` (`-88.4 dB`), `45°` (`-63.8 dB`), `75°` (`-24.8 dB`), oscillates at `90°` (`-2.9 dB`), and diverges at `95°` (`+4.6 dB`), `120°` (`+40.0 dB`, `|w|=148`), and `180°` (`|w| > 1000` rail by step `2777`).
   - Protected Leaky (`1e-3`) + Ball (`W_max=2.0`) + Freeze (`+6 dB`) keeps `|w| <= 2.00` across all angles and triggers freeze at `180°` (`final_e = +7.1 dB`).
3. **Probe 2C (Exact IEEE 754 `float32` `CMSIS-DSP` `arm_lms_norm_f32` Running-Energy Recurrence)**:
   - Input: `20` cycles of `[1.0]*64 + [1e-4]*64 + [0.0]*128` (`5,120` samples, strictly within `[-1, +1]`).
   - Result: `min_energy = -6.400002235e-7`, `eps = 1.192092896e-7`, `min(energy + eps) = -5.207909339e-7`, `non_positive_denom_samples = 2320/5120`, worst-case step multiplier `1/(energy + eps) = -1.920e+6` (sign-inverted amplification).
4. **Probe 2D (Exhaustive `AM_MIDI2.0Lib` `scaleUp`/`scaleDown`, `umpProcessor.cpp:46` Bug & `31,250 Hz` JR Rollover)**:
   - `scaleUp(7->16)`: `128/128` strictly monotone, `0 -> 0x0`, `64 -> 0x8000`, `127 -> 0xFFFF`, `128/128` exact `scaleDown` round-trip.
   - `scaleUp(7->32)`: `128/128` strictly monotone, `0 -> 0x0`, `64 -> 0x80000000`, `127 -> 0xFFFFFFFF`, `128/128` exact `scaleDown` round-trip.
   - `scaleUp(14->32)`: `16,384/16,384` strictly monotone, `0 -> 0x0`, `8192 -> 0x80000000`, `16383 -> 0xFFFFFFFF`, `16,384/16,384` exact `scaleDown` round-trip.
   - `umpProcessor.cpp:46` witness: `mt0JRTimeStamp(0x1234) = 0x00201234` $\rightarrow$ `(0x00201234 >> 16) & 0xFFFF = 0x0020` (expected `0x1234`).
   - JR rollover: `31,250 Hz` $\Rightarrow$ `32.00 µs`/tick, `2.097152 s` rollover, `±1.048576 s` causal half-window; `(now=0xFFF0, ts=0x0010)` gives naive `-65,504` ticks (`-2.096128 s`) vs. modular `int16_t` `+32` ticks (`+1024.0 µs`).

## Revalidation

To cheaply revalidate these findings on newer upstream revisions:

1. **`PipeWire` & `libsamplerate` ASRC Check**: Diff `src/modules/module-rtp/audio.c` (around `spa_dll_update`, `pw_stream_set_rate`, and `rtp_stream_clear_queued_packets`) and `spa/include/spa/utils/dll.h` to check whether rate/slew clamping or soft cross-fade recovery has replaced hard queue-flush resync on underrun/overrun. Check `libsndfile/libsamplerate` `src/samplerate.c` (`src_set_ratio`) for ratio-slew limiting.
2. **`CMSIS-DSP` & `pyroomacoustics` Adaptive-Filter Check**:
   - Inspect `ARM-software/CMSIS-DSP` `Source/FilteringFunctions/arm_lms_norm_f32.c` (`lines 214-262, 400-454`) for `energy = fmaxf(energy, 0.0f)` or periodic full energy recomputation; run a 5,120-sample C unit test feeding `([1.0]*64 + [1e-4]*64 + [0.0]*128)*20` into `arm_lms_norm_f32` and assert `S->energy >= 0.0f` and finite bounded `pCoeffs`.
   - Inspect `arm_lms_norm_q31.c` (`line 180`) for saturating `__QSUB` error computation and `LCAV/pyroomacoustics` `pyroomacoustics/adaptive/lms.py` (`lines 49, 112-116`) for regularization $\epsilon > 0$ on silent zero-vector inputs.
3. **`AM_MIDI2.0Lib` & `RtMidi` UMP Check**:
   - Inspect `midi2-dev/AM_MIDI2.0Lib` `src/umpProcessor.cpp` (`MT == UMP_UTILITY` branch) to verify `mess.value = umpMess[0] & 0xFFFF;` (removing the erroneous `>> 16` shift) and `include/utils.h` (`scaleUp`, `srcBits == 1`) for `1ULL << dstBits` UB fix.
   - Check `thestk/rtmidi` `RtMidi.cpp` (`MidiInWinMidi2::midi_in_callback`) for native UMP `MT=0x0`/`MT=0x4` delivery and lock-free/alloc-free queue replacement (verify zero findings under Clang `RTSan`).
