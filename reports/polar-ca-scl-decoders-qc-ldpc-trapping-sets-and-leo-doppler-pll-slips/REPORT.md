# 5G NR Polar CA-SCL Decoders, QC-LDPC Trapping-Set Error Floors, and LEO Doppler PLL Cycle Slips

## Summary

High-throughput `5G NR` (`3GPP TS 38.212`) and Low-Earth-Orbit Non-Terrestrial Network (`LEO NTN`) physical-layer receivers couple carrier synchronization with quantized `SIMD` forward error correction (`FEC`). Across `aff3ct/aff3ct`, `srsran/srsRAN_Project`, `gnuradio/gnuradio`, and `daniestevez/gr-satellites`, primary-source inspection and deterministic execution expose three coupled fixed-point and dynamical failure boundaries (`Basis: source + normative + execution + derived`):

1. **`3GPP TS 38.212` Polar `CA-SCL` `int8_t` Path-Metric Wraparound and `CRC` False-Alarm Inflation (`aff3ct` & `srsRAN`)**: In fast Successive Cancellation List (`SCL`) decoding (`aff3ct` `Decoder_polar_SCL_fast_sys.hxx:36-39, 61-69, 87-88`), normalizing `signed char` (`int8_t`) path metrics to `-128` (`norm = -128 - min`) prevents single-bit splits from overflowing `+127`, but multi-bit specialized `Repetition` (`REP`) and `Single-Parity-Check` (`SPC`, length `> 4`) leaf nodes accumulate penalties exceeding `255`, wrapping two's-complement `int8_t` (`-124 + 266 = +142 -> -114 < -110` true path) and inverting survivor selection! Furthermore, expanding list size $L$ from `1` (as in `srsRAN`'s Simplified SC `polar_decoder_impl.cpp:209-333`) to $L = 32$ inflates pure-noise `CRC` false-alarm rates (`FAR`) by $1 - (1 - 2^{-C})^{M L}$—reaching **`1.551%`** on `11`-bit `PUCCH` `CRC11` and **`2.10e-5` per `1 ms` slot (`~21` phantom grants/sec)** across `44` blind `PDCCH` candidates unless `TS 38.212` distributed `CRC24C` pruning and path-metric spread gates are enforced (`Basis: normative + source + execution`).
2. **`QC-LDPC` `AVX-512` `int8_t` `-128` `vpabsb` Asymmetry and Elementary `(a, b)` Trapping Sets (`aff3ct` vs. `srsRAN`)**: Horizontal layered Offset Min-Sum (`OMS`) `SIMD` kernels compute `v2c = var_node - c2v` followed by `abs(v2c)` and signed `min(min1, var_abs)`. In `aff3ct` (`Decoder_LDPC_BP_horizontal_layered_ONMS_inter.cpp:443-450`), unguarded `int8_t` subtraction can hit `-128` (`0x80`), where hardware `VPABSB` (`_mm512_abs_epi8(-128)`) returns `0x80`—interpreted by signed `_mm512_min_epi8` as **`-128`**, corrupting `min1 = -128` across the check row! By contrast, `srsRAN` (`ldpc_decoder_avx512.cpp:36-54, 110-124, 150`) restricts valid `int8_t` `LLR`s to symmetric `[-127, +127]` (`±LLR_INFINITY`), keeping `-128` uninhabited at the type boundary. Even with sound `[-127, +127]` variable posteriors and `6-bit` (`[-31, +31]`) extrinsic messages, elementary Richardson `(a = 5, b = 1)` trapping sets lock standard layered `OMS` into permanent `5`-bit error floors (`30/30` iterations stalled), whereas syndrome-stall bit-pinning restarts converge in **`8` iterations with `0` residual errors** (`Basis: source + execution`).
3. **`LEO` Ka-Band Doppler-Rate Quadrant Cycle Slips in 2nd-Order `Costas` Loops (`GNU Radio` & `gr-satellites`)**: `gnuradio`'s `gr::digital::costas_loop_cc_impl` (`costas_loop_cc_impl.cc:104-121`) inherits a 2nd-order `Type-II` proportional-integral `gr::blocks::control_loop` (`control_loop.cc:20-37`). Under a `Ka`-band `LEO` zenith pass (`±48 kHz` residual carrier span, $\dot{f}_D = -6.5\text{ kHz/s}$ Doppler slew) on a `32 kSym/s` narrowband `NTN`/`TT&C` QPSK bearer (`loop_bw = 0.0025 rad/sym`), the normalized angular acceleration $2\pi |\dot{f}_D| / f_s^2 = 3.99 \times 10^{-5}\text{ rad/sym}^2$ exceeds the 2nd-order pull-in torque $\beta \cdot \max|\text{PD}_4| = 1.77 \times 10^{-5}\text{ rad/sym}^2$, causing **`431` consecutive `±pi/2` quadrant cycle slips** (each inverting/swapping `I/Q` `LLR` signs into the downstream Polar/LDPC decoder), whereas a 3rd-order `Type-III` `FLL`-assisted `PLL` locks with **`0` cycle slips** and **`8e-5 rad`** steady-state phase error (`Basis: source + execution`).

---

## Applicability

This report covers the interaction of carrier phase/frequency tracking, quantized `SIMD` log-likelihood ratio (`LLR`) arithmetic, and iterative/list channel decoding across four upstream open-source SDR/5G codebases and three foundational standards/papers:

- **`aff3ct/aff3ct` (`0e8ecda8191cec97a6fe86a56de0d957b63b3b04`)**: C++11/17 multi-architecture (`MIPP` `SSE4.2`/`AVX2`/`AVX-512`/`NEON`) `FEC` library (`include/Module/Decoder/Polar/SCL/Decoder_polar_SCL_fast_sys.hxx`, `Decoder_polar_SCL_fast_CA_sys.hxx`, and `src/Module/Decoder/LDPC/BP/Horizontal_layered/ONMS/Decoder_LDPC_BP_horizontal_layered_ONMS_inter.cpp`). Findings apply when instantiating `B = int8_t, R = int8_t` (`Q8` fixed-point mode).
- **`srsran/srsRAN_Project` (`d2f4b70dda8e2c557d5b05a0ac5f92dbddda19bc`, `release_25_10`, vs. `6ee24f9501b15090b453b0112f92df64fe302c08`, `HEAD`)**: **Version Continuity Qualification**: On `2026-06-01`, `srsran/srsRAN_Project` commit `6ee24f9501b15090b453b0112f92df64fe302c08` replaced the repository source tree with an archive transition stub redirecting ongoing open-source 5G RAN development to the Linux Foundation `OCUDU` project. All source-level `srsRAN` channel-coding findings in this report apply specifically to `release_25_10` (`d2f4b70dda8e2c557d5b05a0ac5f92dbddda19bc`, `lib/phy/upper/channel_coding/polar/polar_decoder_impl.cpp` and `lib/phy/upper/channel_coding/ldpc/ldpc_decoder_avx512.cpp`) and earlier `24.x–25.x` releases sharing that `upper/channel_coding` tree; they do **not** apply to the stub tree at `6ee24f95...`.
- **`gnuradio/gnuradio` (`3d33e04a249b31ef32106d275b927a7c4cf86425`) & `daniestevez/gr-satellites` (`0ff8b614c3ed57110c3497c287bced9a01bbc238`)**: `gr::blocks::control_loop` (`gr-blocks/lib/control_loop.cc`), `gr::digital::costas_loop_cc_impl` (`gr-digital/lib/costas_loop_cc_impl.cc`), and `gr::satellites::doppler_correction_impl` (`lib/doppler_correction_impl.cc`).
- **Normative & Theoretical Baseline**: `3GPP TS 38.212` (`Release 17 / Release 18 NTN`) control-channel Polar coding (`K <= 1024`, `CRC24C`, `CRC11`, `CRC6`) and data-channel `QC-LDPC` base graphs `BG1` (`Z_c <= 384`, `22 x 68`) and `BG2` (`10 x 52`); Tal & Vardy (`DOI: 10.1109/TIT.2015.2410251`) `CA-SCL`; and Richardson (`Allerton 2003`) `(a, b)` trapping-set topology.

---

## Findings

### 1. `3GPP TS 38.212` Polar `CA-SCL`: Fixed-Point `int8_t` Metric Wraparound and `CRC` False Alarms

`Basis: normative + source + execution + derived`

#### 1.1 Fast `SCL` Specialized Subtree Pruning and `int8_t` Overflow in `aff3ct`

Tal & Vardy (`IEEE TIT 2015`) Successive Cancellation List (`SCL`) decoding maintains $L \in \{2, 4, 8, 16, 32\}$ candidate bit prefixes $\hat{\mathbf{u}}_1^i$ over a depth-$n$ ($N = 2^n$) Arikan polarization tree. At each information leaf $i \in \mathcal{A}$, every survivor path $\ell \in \{0, \dots, L-1\}$ forks into $\hat{u}_i \in \{0, 1\}$ with exact log-domain path-metric (`PM`) update:

$$\mathrm{PM}_i^{(\ell)}(\hat{u}_i) = \mathrm{PM}_{i-1}^{(\ell)} + \ln\!\left(1 + e^{-(1 - 2\hat{u}_i)\,\alpha_i^{(\ell)}}\right) \approx \mathrm{PM}_{i-1}^{(\ell)} + \begin{cases} 0, & \text{if } \hat{u}_i = \frac{1}{2}(1 - \mathrm{sgn}(\alpha_i^{(\ell)})) \\ |\alpha_i^{(\ell)}|, & \text{otherwise} \end{cases}$$

To avoid traversing all $2N - 2$ tree edges serially, Fast-SSC-List (`Fast-SSCL`) collapses constituent subtrees with structured frozen patterns into single-step macro-leaves:
- **`Rate-0` (`R0`)**: All frozen ($u = 0$), single survivor update $\Delta \mathrm{PM} = \sum_{j: \alpha_j < 0} |\alpha_j|$.
- **`Rate-1` (`R1`)**: All information bits; Chase-2 forks only the $\min(2, N_s)$ least reliable positions.
- **`Repetition` (`REP`)**: $N_s - 1$ frozen bits followed by `1` information bit (all $N_s$ coded leaves equal $\hat{u}_{N_s-1} \in \{0, 1\}$); $\Delta \mathrm{PM}(0) = \sum_{\alpha_j < 0} |\alpha_j|$, $\Delta \mathrm{PM}(1) = \sum_{\alpha_j > 0} |\alpha_j|$.
- **`Single-Parity-Check` (`SPC`)**: `1` frozen bit followed by $N_s - 1$ information bits enforcing even parity across $N_s$ leaves.

In `aff3ct` (`Decoder_polar_SCL_fast_sys.hxx:36-39, 61-69`), `R = signed char` (`int8_t`) mode clamps input channel `LLR`s via `sat_m<signed char>(m, -128, 63)` and re-centers active path metrics before splits via `normalize_scl_metrics`:

```cpp
// aff3ct include/Module/Decoder/Polar/SCL/Decoder_polar_SCL_fast_sys.hxx:61-69 (rev 0e8ecda8...)
inline void normalize_scl_metrics(std::vector<signed char>& metrics, const int L) {
    auto min = *std::min_element(metrics.begin(), metrics.begin() + L);
    const auto norm = std::numeric_limits<signed char>::min() - min; // -128 - min
    for (auto i = 0; i < L; i++)
        metrics[i] += norm;
}
```

Because `sat_m` caps a **single** `LLR` magnitude at `63` (or `128`), a single-bit split (`-128 + 63 = -65 <= 127`) cannot overflow `signed char`. However, inside a length-$N_s$ `REP` or `SPC` macro-leaf (`N_s = 8, 16, 32`), the branch penalty sums up to $N_s$ leaf magnitudes ($\le 63 N_s \gg 255$) in a single step! Indeed, `aff3ct`'s own constructor (`lines 87-88`) contains the inline warning comments:
- `new tools::Pattern_polar_rep, // /!\ perf. degradation with REP nodes in fixed-point`
- `new tools::Pattern_polar_spc(2, 2) // /!\ perf. degradation with SPC nodes length > 4 (when L is big)`

Executing `probes/verify_polar_ldpc_leo_pll.py` demonstrates the exact arithmetic Mechanism: entering a `REP-8` node with normalized `pm_init_true = -128` (`pen_true = +18`) and competitor `pm_init_wrong = -124` (`pen_wrong = 7 * 38 = +266`), unchecked `int8_t` addition wraps `-124 + 266 = +142 -> -114`, which compares **strictly smaller (better!)** than the true path's `-128 + 18 = -110`, causing `std::sort` to evict the true codeword! Switching path metrics to **min-zero-shifted `uint8_t` saturating addition (`vpaddusb`, `0` = best, `255` = saturated worst)** maps `(18, min(255, 4 + 266)) = (18, 255)`, preserving survivor order in the exact same `1`-byte lane width.

#### 1.2 `CA-SCL` List-Size vs. `CRC` False-Alarm Rate (`FAR`) and Silent Fallback Hazard

In `aff3ct`'s `Decoder_polar_SCL_fast_CA_sys::select_best_path` (`Decoder_polar_SCL_fast_CA_sys.hxx:96-110`):

```cpp
// aff3ct Decoder_polar_SCL_fast_CA_sys.hxx:102-109 (rev 0e8ecda8...)
while (i < this->n_active_paths && !crc_check(this->s[this->paths[i]], frame_id))
    i++;
this->best_path = (i == this->n_active_paths) ? this->paths[0] : this->paths[i];
fast_store = i != this->n_active_paths;
return this->n_active_paths - i;
```

Note two critical integration invariants:
1. **Unconditional `this->paths[0]` Fallback on Total `CRC` Failure (`line 106`)**: When *zero* of the $L$ survivors pass `crc_check` (`i == n_active_paths`), `select_best_path` still sets `best_path = paths[0]` and extracts its bits into the output buffer `V_K` (`SIHO` interface), returning `0` only to internal callers (`_decode`). Any caller using the `SIHO` `decode_siho` interface without re-verifying the `CRC` or status flag silently consumes an undetected corrupted control payload!
2. **Pure-Noise False-Alarm Inflation Across List Size $L$ and Blind Searches $M$**: Under pure `AWGN` (no signal transmitted on an unscheduled `PDCCH` search-space candidate or `PUCCH` slot), testing $L$ quasi-independent `SCL` survivors across $M$ blind decoding candidates with a $C$-bit `CRC` yields false-alarm probability (`probes/verify_polar_ldpc_leo_pll.py`):
   $$P_{\text{FA}}(L, C, M) = 1 - \left(1 - 2^{-C}\right)^{M \cdot L}$$
   - On `5G NR` `PUCCH` Format 2/3/4 short payloads (`12 <= A <= 19` bits, `CRC11`, $C = 11, M = 1$): `srsRAN`'s `L = 1` Simplified SC decoder (`polar_decoder_impl.cpp:209-333`) has $P_{\text{FA}} = 4.88 \times 10^{-4}$ (`0.049%`), whereas naive `CA-SCL` at $L = 32$ inflates $P_{\text{FA}}$ `31.8x` to **`1.551%`**—violating `3GPP` `< 0.1%–1%` DTX-to-ACK conformance unless gated by path-metric spread $\mathrm{PM}_{\text{winner}} - \mathrm{PM}_0 \le \tau_{\text{SNR}}$!
   - On `5G NR` `PDCCH` (`M = 44` blind candidates/slot, `CRC24C` masked by `16`-bit `RNTI`): if a receiver accidentally validates only `16` unmasked tail bits at $L = 32$, $P_{\text{FA}} = \mathbf{2.126\%}$ per slot; even with full `24`-bit `CRC24C` at $L = 8$, $P_{\text{FA}} = \mathbf{2.098 \times 10^{-5}}$ per `1 ms` slot (`~21` false downlink/uplink grants per second per UE!), explaining why `3GPP TS 38.212` §5.3.1.1 interleaves **`CRC24C` parity bits across the polar sequence** (distributed `CRC`) to prune invalid branches *mid-tree* and why production `gNB`/`UE` PHYs combine distributed `CRC` with an `SINR` / metric-ratio gate.

---

### 2. `QC-LDPC` `AVX-512` `int8_t` `-128` Sign Bug and `(a, b)` Trapping-Set Error Floors

`Basis: source + normative + execution + derived`

#### 2.1 `int8_t` `-128` (`0x80`) `VPABSB` Corruption in `aff3ct` vs. `[-127, +127]` Discipline in `srsRAN`

In `5G NR` `QC-LDPC` horizontal layered Offset Min-Sum (`OMS`), each parity-check layer $c$ subtracts the previous iteration's check-to-variable extrinsic message $E_{c \to v}^{(t-1)}$ from variable posterior $L_v$, computes row-wise first/second minimum magnitudes $(\min_1, \min_2)$ and cumulative sign XOR, applies offset $\max(0, \min_{1,2} - \beta)$, and writes back $L_v \leftarrow \mathrm{v2c}_{v \to c} + E_{c \to v}^{(t)}$.

Comparing `aff3ct` (`0e8ecda8...`) and `srsRAN` (`d2f4b70d...`) side-by-side in `8`-bit `SIMD` mode exposes a classic two's-complement hardware trap:

| Implementation Aspect | `aff3ct` (`Decoder_LDPC_BP_horizontal_layered_ONMS_inter.cpp:443-450`) | `srsRAN` (`ldpc_decoder_avx512.cpp:36-54, 110-124, 150`) |
| :--- | :--- | :--- |
| **`v2c` Subtraction** | `contributions[v] = var_nodes[H[c][v]] - branches[kr++]` (`mipp::sub<int8_t>` = wrapping **`vpsubb`**!) | `_mm512_subs_epi8(soft_epi8, c2v_epi8)` clamped to `[LLR_MIN, LLR_MAX]` + `±LLR_INFINITY` (`±127`) |
| **`-128` (`0x80`) Inhabitance** | **Inhabited**: e.g., `var_node = -90`, `branch = +38` $\implies -90 - 38 = -128$ (`0x80`) (or `-100 - 40` wraps to `+116`!) | **Strictly Uninhabited**: `LLR_NEG_INFINITY = -127` (`0x81`), `LLR_INFINITY = +127` (`0x7F`) |
| **Magnitude & Row Minimum** | `var_abs = mipp::abs(contributions[v])` (`vpabsb`) $\to$ `mipp::min(min1, var_abs)` (**signed `vpminsb`**!) | `_mm512_abs_epi8` $\to$ `_mm512_cmpgt_epi8_mask` + `_mm512_mask_blend_epi8` |
| **Behavior at `-128` (`0x80`)** | `vpabsb(0x80) = 0x80` (`+128` unsigned, **`-128` signed!**); signed `vpminsb(45, -128)` sets **`min1 = -128`**, zeroing `cste2 = max(0, -128 - offset) = 0` for the entire check row! | Impossible by representation invariant: `abs([-127, +127])` lies strictly in `[0, +127]` (`int8_t >= 0`) |

`srsRAN`'s `log_likelihood_ratio` wrapper (`srsran_ldpc_avx512.cpp:36-54, 110-124`) is a textbook example of **type-level asymmetric two's-complement elimination**: carving out `-128` (`0x80`) so the symmetric algebra `[-127, +127]` makes both negation (`-x`) and `_mm512_abs_epi8(x)` total functions into non-negative `int8_t`.

#### 2.2 Finite-Alphabet Richardson `(a, b)` Trapping-Set Stalling and Syndrome-Guided Peeling

Even when `-128` wraparound is eliminated, `QC-LDPC` codes decoded under quantized (`8`-bit `[-127, +127]` posterior, `6`-bit `[-31, +31]` extrinsic) layered `OMS` exhibit **error floors** at high `SNR` (`BLER ~ 10^-5..10^-7`) governed by Tom Richardson's (`Allerton 2003`) **elementary `(a, b)` trapping sets**: induced subgraphs of $a$ variable nodes having $b$ odd-degree check neighbors and exclusively degree-`2` internal even-degree check neighbors.

In `probes/verify_polar_ldpc_leo_pll.py`, we construct an explicit $d_v = 3$ `(a = 5, b = 1)` trapping set on variable nodes $\{0, 1, 2, 3, 4\}$ with `7` internal degree-`2` checks (`c0..c6`) and only `1` odd-degree external check `c7 = (4, 7, 8)`, where healthy external bits `{5..9}` carry strong `+60` channel `LLR`s (`bit = 0`) and only `{0..4}` suffer mild negative noise impulses (`[-12, -12, -12, -12, -16]`):
- **Standard `8b/6b` Layered `OMS` (`peel_on_stall = false`)**: Across `c0..c6`, each check has *two* negative trapping-set inputs (`-12`) and *one* positive external input (`+60`), so the extrinsic sign sent to each trapping-set variable is $(-)\times(+) = (-)$, mutually reinforcing wrong beliefs until `{0..3}` saturate at `-105..-80`! Lone unsatisfied check `c7` sends at most `+31` (`6`-bit extrinsic ceiling) to `v4`, which cannot overcome `v4`'s `-16 + 2*(-31) = -78` internal reinforcement. Decoding stalls permanently across all **`30` iterations with `5` residual bit errors** (`unsat = [c7]`, weight `b = 1`).
- **Syndrome-Stall Bit-Pinning Restart (`peel_on_stall = true`)**: Detecting that the unsatisfied syndrome weight $|S^{(t)}| = 1 \le 2$ has stalled at iteration `5`, pinning the sole negative variable `v4` inside `c7` to `+40` and resetting saturated `c2v` registers breaks the internal `2`-core reinforcement, peeling `{3, 0}` then `{2, 1}` to **exact convergence in `8` total iterations (`0` residual bit errors)**.

---

### 3. `LEO` `Ka`-Band Doppler Slew and 2nd-Order `Costas` Quadrant Cycle Slips

`Basis: source + execution + derived`

#### 3.1 `GNU Radio` `control_loop` Dynamics Under Constant Orbital Frequency Slew

A Low-Earth-Orbit (`LEO`, altitude $h \approx 550\text{ km}$, orbital velocity $v \approx 7.59\text{ km/s}$) `Ku`/`Ka`-band (`12–30 GHz`) link experiences up to $\pm 250\text{ to }\pm 750\text{ kHz}$ total Doppler shift (`±48 kHz` residual carrier window after coarse ephemeris/TLE pre-compensation) and a peak overhead zenith **Doppler rate** $\dot{f}_D \approx -f_c v^2 / (c h)$ of **`-3.2 kHz/s` to `-10.5 kHz/s`**.

In `gnuradio` (`gr-blocks/lib/control_loop.cc:20-37` and `gr-digital/lib/costas_loop_cc_impl.cc:104-121`), `costas_loop_cc_impl` drives a **2nd-order `Type-II` PI loop** (`d_freq += d_beta * err; d_phase += d_freq + d_alpha * err`) with critically damped gains (`d_damping = sqrt(2)/2`):

$$d_\alpha = \frac{4 \zeta B_n}{1 + 2\zeta B_n + B_n^2}, \qquad d_\beta = \frac{4 B_n^2}{1 + 2\zeta B_n + B_n^2}$$

Under a constant frequency ramp $f(t) = f_0 + \dot{f}_D t$ sampled at symbol rate $f_s$, the per-symbol discrete frequency increment changes by $\Delta \omega_{\text{step}} = 2\pi \dot{f}_D / f_s^2\text{ rad/sym}^2$. For `d_freq` to track $\Delta \omega_{\text{step}}$, the decision-directed `QPSK` phase detector `phase_detector_4(z) = sign(I)*Q - sign(Q)*I` (whose peak linear restoring torque inside a $\pm \pi/4$ quadrant is $\max |e_k| = \frac{1}{\sqrt{2}} \approx 0.7071$ before jumping discontinuously across decision axes!) must sustain steady-state phase stress:

$$|e_{\text{ss}}| = \frac{2\pi |\dot{f}_D|}{d_\beta \, f_s^2} \approx \frac{\pi |\dot{f}_D|}{2 B_n^2 f_s^2}$$

Whenever $|e_{\text{ss}}| \ge 1/\sqrt{2}$ (or noise + lag crosses $|\theta_e| = \pi/4$), the `QPSK` Costas detector crosses into the adjacent decision quadrant and suffers repeated **`±pi/2` cycle slips**! Each $+\pi/2$ slip maps $(I, Q) \mapsto (-Q, I)$, swapping even/odd `QPSK` bit `LLR`s and negating one stream—destroying the entire `LDPC` or `Polar` codeblock downstream even at infinite `SNR`! (Additionally, in `gr-satellites` `doppler_correction_impl.cc:166-169`, `double d_phase` is accumulated in `float64` and wrapped via `phase_wrap()`, then cast `static_cast<float>(d_phase)` into `gr_expj`; omitting `phase_wrap()` in custom `float32` NCO blocks causes catastrophic `float32` mantissa quantization after a few seconds at `> 50 kHz` offsets.)

- **Deterministic Verification (`probes/verify_polar_ldpc_leo_pll.py`)**: On a `32 kSym/s` narrowband `NTN`/`TT&C` `QPSK` bearer (`loop_bw = 0.0025 rad/sym` for low-`SNR` phase-noise rejection, $\dot{f}_D = -6,500\text{ Hz/s}$ over `6,000` symbols = `187.5 ms`), $2\pi |\dot{f}_D| / f_s^2 = 3.988 \times 10^{-5} > d_\beta / \sqrt{2} = 1.762 \times 10^{-5}$, causing `GNU Radio`'s 2nd-order `Costas` loop to suffer **`431` `±pi/2` quadrant cycle slips**! Upgrading to a **3rd-order `Type-III` loop** (`p3_fdot += gamma * err; p3_freq += p3_fdot + beta * err; p3_phase += p3_freq + alpha * err`, `bw3 = 0.030`) tracks constant $\dot{f}_D$ with **zero steady-state lag**, **`0` quadrant cycle slips**, and **`8e-5 rad` (`0.0046°`)** peak post-acquisition phase error.

---

### 4. Multi-Level Performance and Resource Footprint (`L1`–`L6`)

`Basis: source + documentation + execution + derived`

| Level | Metric / Resource Axis | `aff3ct` (`C++` `MIPP` `Polar` + `LDPC`) | `srsRAN` (`release_25_10` `AVX-512` `5G PHY`) | `GNU Radio` + `gr-satellites` (`SDR` Sync) |
| :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring & Maintenance Velocity** | LoC & SIMD/fixed-point engineering effort | `~1,600` LoC (`Polar_SCL_fast_sys.hxx`) + `~570` LoC (`LDPC_ONMS_inter.cpp`); `MIPP` intrinsics share `1` template across `AVX2`/`AVX-512`/`NEON`, but subtle `int8` overflow rules remain undocumented | `~350` LoC (`polar_decoder_impl.cpp` `L=1`) + `~270` LoC (`ldpc_decoder_avx512.cpp` + support headers); hand-tuned `_mm512_*` intrinsics require `2–4` weeks specialist effort per ISA | `~200` LoC (`costas_loop_cc_impl.cc`) + `~180` LoC (`doppler_correction_impl.cc`); rapid Python/GRC flowgraph prototyping (`< 1 day`), high risk of silent `Type-II` loop unlock on `LEO` passes |
| **`L2` Toolchain & Framework Build Time** | Cold / incremental C++ template & SIMD build | Heavy C++ template instantiation across `B, R` types (`int8, int16, float, double`): full `aff3ct` build takes `6–15 min` (`4–8 GB` peak clang/gcc RSS); single module incremental `~8–15 s` | `srsRAN` `lib/phy/upper/channel_coding` builds in `~12–25 s` (`cmake`/`ninja`, `-mavx512f -mavx512bw`); full `gNB` build `3–7 min` | `GNU Radio` core build `10–20 min`; `gr-satellites` OOT module builds in `~15–35 s` (`pybind11` wrappers dominate compile time) |
| **`L3` Codegen / Graph Table Elaboration** | Frozen-set / QC shift-table / NCO setup latency | Polar frozen-bit reliability (`5G` `N <= 1024`) + `Pattern_polar` tree parse: **`~15–60 µs`**; `LDPC` `BG1/BG2` lifting (`Z_c <= 384`): `< 100 µs` | `polar_code` `TS 38.212` rate-matching/frozen mask generation: **`< 10 µs`** (zero heap alloc, preallocated `srsran` `span`s); `LDPC` shift tables static in `.rodata` | `control_loop::update_gains` (`2` divisions): `< 20 ns`; `gr-satellites` Doppler `.txt` ephemeris load: `< 1 ms` |
| **`L4` Runtime Decoding & Sync Throughput** | Info throughput, `cycles/bit`, & `p99.9` slot latency | `Fast-CA-SCL` (`N=1024, K=512, L=8`, `int8` `AVX2`): **`~80–220 Mbps/core`** (`~15–35 µs` latency); inter-frame `AVX-512` `int8` `LDPC` (`10` iters): **`2–8 Gbps/core`** (`< 0.8 cycles/info-bit`) | `srsRAN` `L=1` `SSC` Polar (`N=512`): **`< 4 µs`**; intra-codeblock `AVX-512` `BG1` `Z_c=384` `LDPC` (`6–10` iters): **`1.2–3.5 Gbps/core`**, meeting `5G NR` `< 200 µs` `HARQ-ACK` `N1` budget | `costas_loop_cc` (`scalar` per-sample feedback dependency): **`~35–75 MSym/s/core`** (`~45–80 cycles/sym`); vectorized `gr_expj` Doppler feed-forward: **`> 250 MSym/s/core`** |
| **`L5` Syndrome / `CRC` / Lock Verification** | Parity check & lock-detector admission speed | `CRC24C` lookup/CLMUL check over $L=8$ paths: **`< 120 ns`**; `LDPC` `AVX-512` early-termination syndrome XOR check: **`< 80 ns/iter`** (`> 100 Gbps` equivalent check speed) | `srsRAN` `PCLMULQDQ` `CRC24C`/`CRC11` verification: **`< 40 ns/codeblock`** (`< 0.15 cycles/byte`); per-layer parity check embedded in `analyze_var_to_check_msgs` | Lock detector $M_2/M_4$ SNR + phase-variance monitor + differential/pilot UW check: **`O(1)` (`< 5 ns/sym`)**, `0` dynamic allocation |
| **`L6` Memory, Binary & Power Footprint** | L1d working set, state bytes, & binary size | `SCL` state (`L=32, N=1024, int8`): `l` + `s` + path trees $\approx$ **`~96 KiB`** (fits in `L2`, spills `32–48 KiB` `L1d` above `L=8`); `aff3ct` binary `~18–35 MB` | `srsRAN` `BG1` (`8448` `int8` posteriors + `~20 KB` `c2v` extrinsics): **`~28 KiB` total working set** (**100% resident in `48 KiB` `L1d` cache!**) | `control_loop` + `costas_loop_cc` state: **`< 64 bytes` per carrier** (`d_phase, d_freq, d_alpha, d_beta`); `gr-satellites` Doppler table `~16 bytes/timepoint` |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Model Refinement (`C2`)

`Basis: source + derived`

#### 5.1 (`C1`) Human Comprehensibility and Mental-Model Ergonomics

- **Invisible Two's-Complement Asymmetry in `SIMD` Templates**: C++ templates like `Decoder_polar_SCL_fast_sys<B, R>` and `Decoder_LDPC_BP_horizontal_layered_ONMS_inter<B, R>` let engineers develop and validate algorithms in `R = float` (`[-inf, +inf]`), then instantiate `R = int8_t` expecting graceful quantization noise. Humans reason in real-number identities (`|x| >= 0`, `a < b => a + c < b + c` for `c >= 0`) that **silently invert** at `int8_t = -128` (`_mm512_abs_epi8(-128) == -128 < 0`) and on multi-bit `REP`/`SPC` sums (`-124 + 266 == -114 < -110`). Because `99.9%` of high-`SNR` frames still decode, these bugs masquerade as "expected fixed-point implementation loss (`0.3–0.8 dB`)" unless caught by boundary probes or `inline` developer warnings (`Decoder_polar_SCL_fast_sys.hxx:87-88`).
- **Control-Theory Type-Order Blindspot**: SDR users wire `Costas Loop (Order=4)` (`4` = `QPSK` constellation order, **not** loop filter order!) into `LEO` satellite flowgraphs assuming `loop_bw` trades off noise vs. tracking. Without an explicit steady-state dynamic stress check ($2\pi |\dot{f}_D| / (d_\beta f_s^2) < 1/\sqrt{2}$), `±pi/2` cycle slips produce sudden `50%` bit-error bursts right at overhead pass zenith (`highest elevation / highest SNR!`), confounding operators who expect link drops at *low* elevation rather than peak zenith!

#### 5.2 (`C2`) Simplicity, Orthogonality, and Universal Model Refinement

All three cross-layer failure modes disappear when ad-hoc C++ `int8_t` casts, unchecked `paths[0]` fallbacks, and untyped loop filters are replaced by **three minimal, hardware-exact algebraic abstractions**:

1. **Symmetric Bounded `LLR` Value Type (`SymInt8[-127, +127]`) + Unsigned Saturating Tropical Semiring (`SatU8[0, 255]`)**:
   - Represent signed `LLR` beliefs strictly in the symmetric interval `[-127, +127]` (`srsRAN` discipline, `0x80` uninhabited), enforced at `sub_sat` boundaries so hardware `vpabsb` and negation are **exact involutions/norms** with zero special-case masks.
   - Represent `SCL` path metrics not as signed `[-128, +127]` numbers shifted to `-128`, but in the **unsigned saturating min-plus tropical semiring `SatU8` (`[0, 255]`, identity `0`, addition `vpaddusb`)** re-anchored to `min = 0` after every stage. Multi-bit `REP`/`SPC` penalties of `+266` saturate monotonically to `255` (`vpaddusb(4, 255) = 255 > 18`) in a **single instruction** with zero wraparound!
2. **Option-Typed Authenticated Decoder Output (`AuthenticatedCodeword<K, CrcBits, FarBound>`)**: Never allow a `CA-SCL` decoder to return an unverified `paths[0]` bit-slice on total `CRC` failure (`Decoder_polar_SCL_fast_CA_sys.hxx:106`). Return `Option<VerifiedPayload>` gated jointly by **(a)** distributed `CRC` syndrome == `0` AND **(b)** path-metric margin $\mathrm{PM}_{\text{winner}} \le \tau(L, C, M)$ bounding pure-noise false-alarm rate $P_{\text{FA}} \le \epsilon_{\text{target}}$.
3. **Kinematic-Order-Matched Carrier Tracking (`LoopType<Order>` >= `DopplerPolynomialDegree + 1`)**: Type-parameterize carrier tracking loops by the degree of orbital phase kinematics they annihilate: `Type-II` (`degree 1`, constant $\Delta f$, terrestrial) vs. `Type-III` / `ephemeris feed-forward + FLL-assisted Type-III PLL` (`degree 2`, constant $\dot{f}_D$, `LEO NTN`), paired with pilot-symbol (`3GPP DM-RS` / `CCSDS ASM`) rotational quadrant disambiguation so `±pi/2` phase ambiguity cannot silently permute `I/Q` `LLR` polarities.

---

## Boundaries

- **5G NR `HARQ` Incremental Redundancy (`IR-HARQ`) Soft-Buffer Combining — `not examined` experimentally**: In `3GPP TS 38.212` `LDPC` rate-matching (`circular buffer` `N_cb`), `Chase` / `IR-HARQ` retransmission combining adds new channel `LLR`s into persistent soft buffers; optimal bit-width scaling between `HARQ` transmissions (`int8` vs `int16` soft-buffer saturation) was not benchmarked here.
- **Ionospheric Scintillation and Multipath Delay-Doppler Coupling in `NTN` — `not examined`**: Our `LEO` synchronization probe (`verify_polar_ldpc_leo_pll.py`) models deterministic orbital Doppler rate $\dot{f}_D = -6.5\text{ kHz/s}$ on single-tap line-of-sight `QPSK`; `S`-band / `Ka`-band equatorial scintillation phase steps and `OFDM` subcarrier inter-carrier interference (`ICI`) under differential beam-edge Doppler require joint `DM-RS` time-frequency interpolation (`not examined`).
- **Post-`2026-06` `OCUDU` Repository Layout — `not examined`**: Because `srsran/srsRAN_Project` `HEAD` (`6ee24f9501b15090b453b0112f92df64fe302c08`) archived its tree in favor of `OCUDU`, post-transition changes outside `srsran/srsRAN_Project` `release_25_10` (`d2f4b70dda8e2c557d5b05a0ac5f92dbddda19bc`) were `not examined`.
- **Attractive Over-Claim Rejected**: Increasing `Type-III` PLL loop bandwidth $B_n$ arbitrarily does **not** monotonically improve `LEO` link reliability: loop thermal phase-noise variance scales linearly with $B_n$ ($\sigma_\theta^2 = \frac{B_n}{\text{SNR}_s} (1 + \frac{1}{2\,\text{SNR}_s})$ for `QPSK` squaring loss), so low-`SNR` `NTN` links (`Es/N0 < 0 dB`) **must** offload the deterministic bulk of $\dot{f}_D(t)$ (`~95%+`) onto open-loop GNSS/ephemeris `NCO` pre-compensation (`gr-satellites` `doppler_correction`) and keep the closed-loop `Type-III` `PLL` narrow (`B_n <= 0.01–0.03`) to track only residual oscillator drift and ephemeris error.

---

## Evidence

### Primary Upstream Repositories (Immutable 40-Hex Revisions, Observed `2026-11-19`)

1. **`aff3ct/aff3ct`** (`0e8ecda8191cec97a6fe86a56de0d957b63b3b04`):
   - `include/Module/Decoder/Polar/SCL/Decoder_polar_SCL_fast_sys.hxx:36-39, 61-69, 80-95`: `sat_m<signed char>(m, -128, 63)`, `normalize_scl_metrics` (`norm = -128 - min`), and explicit developer warnings on `Pattern_polar_rep` (`line 87`) and `Pattern_polar_spc` (`line 88`) fixed-point degradation.
   - `include/Module/Decoder/Polar/SCL/Decoder_polar_SCL_fast_CA_sys.hxx:96-110`: `select_best_path` sorting paths by `metrics[x] < metrics[y]`, scanning `crc_check`, and falling back to `this->paths[0]` when `i == this->n_active_paths`.
   - `src/Module/Decoder/LDPC/BP/Horizontal_layered/ONMS/Decoder_LDPC_BP_horizontal_layered_ONMS_inter.cpp:440-465`: non-saturating `contributions[v] = var_nodes[this->H[c][v]] - branches[kr++]` followed by `mipp::abs(contributions[v])` and signed `mipp::min(min1, var_abs)`.
2. **`srsran/srsRAN_Project`** (`d2f4b70dda8e2c557d5b05a0ac5f92dbddda19bc` `release_25_10`, and archive-transition `HEAD` `6ee24f9501b15090b453b0112f92df64fe302c08`):
   - `lib/phy/upper/channel_coding/polar/polar_decoder_impl.cpp:209-333` (`d2f4b70d...`): `L = 1` Simplified Successive Cancellation (`rate_0_node`, `rate_1_node`, `rate_r_node`).
   - `lib/phy/upper/channel_coding/ldpc/ldpc_decoder_avx512.cpp:36-54, 109-125, 149-156` (`d2f4b70d...`): `_mm512_subs_epi8` clamped to `[LLR_MIN, LLR_MAX]` and `±LLR_INFINITY` (`[-127, +127]`), guaranteeing `_mm512_abs_epi8` (`line 150`) never encounters `-128` (`0x80`).
3. **`gnuradio/gnuradio`** (`3d33e04a249b31ef32106d275b927a7c4cf86425`):
   - `gr-blocks/lib/control_loop.cc:20-37`: 2nd-order critically damped `d_alpha, d_beta` `Type-II` loop filter.
   - `gr-digital/lib/costas_loop_cc_impl.cc:98-130`: `phase_detector_4`, `branchless_clip(d_error, 1.0)`, `advance_loop`, `phase_wrap`.
4. **`daniestevez/gr-satellites`** (`0ff8b614c3ed57110c3497c287bced9a01bbc238`):
   - `lib/doppler_correction_impl.cc:150-175`: piecewise-linear time-frequency ephemeris interpolation, `double d_phase` accumulation + `phase_wrap()`, and `gr_expj(-static_cast<float>(d_phase))`.

### Peer-Reviewed Literature and Standards

- I. Tal and A. Vardy, *"List Decoding of Polar Codes,"* IEEE Trans. Inf. Theory, vol. 61, no. 5, pp. 2213–2226, May 2015, `DOI: 10.1109/TIT.2015.2410251` (`arXiv:1206.0050`).
- A. Cassagne et al., *"AFF3CT: A fast forward error correction toolbox!"* SoftwareX, vol. 10, 100345, 2019, `DOI: 10.1016/j.softx.2019.100345`.
- T. Richardson, *"Error Floors of LDPC Codes,"* Proc. 41st Annual Allerton Conf. on Communication, Control, and Computing, pp. 1426–1435, Oct. 2003.
- 3GPP TS 38.212, *NR; Multiplexing and channel coding*, Release 17 / Release 18 (`§5.2` LDPC coding, `§5.3.1` Polar coding and distributed `CRC24C` interleaving).

### Preserved Executable Verification Artifact (`probes/verify_polar_ldpc_leo_pll.py`)

Observed deterministic output on `2026-11-19` (`Python 3`, pure stdlib `cmath`, `math`, `json`):

```json
{
  "polar_cascl_pm_and_crc_far": {
    "rep8_i8_wrapped_pm_true_vs_wrong": [-110, -114],
    "rep8_i8_wrong_path_beats_true": true,
    "rep8_u8_sat_pm_true_vs_wrong": [18, 255],
    "far_pucch_crc11_L1_vs_L32": [0.000488, 0.015507],
    "far_pdcch_44cand_L32_eff16": 0.02126,
    "far_pdcch_44cand_L8_crc24c_per_slot": 2.098e-05
  },
  "ldpc_i8_abs_and_trapping_set": {
    "avx512_vpabsb_neg128_corrupted_min": -128,
    "avx512_sym127_safe_min": 45,
    "standard_8b6b_oms_converged": false,
    "standard_8b6b_oms_residual_bit_errors": 5,
    "syndrome_peeled_oms_converged": true,
    "syndrome_peeled_oms_iterations": 8,
    "syndrome_peeled_oms_residual_bit_errors": 0
  },
  "leo_doppler_costas_slips": {
    "costas_2nd_order_quadrant_slips": 431,
    "pll_3rd_order_quadrant_slips": 0,
    "pll_3rd_order_max_steady_err_rad": 8e-05
  }
}
```

---

## Revalidation

1. **Run the Preserved Deterministic Micro-Probe (`< 0.1 s`, zero third-party packages)**:
   ```bash
   python3 -B reports/polar-ca-scl-decoders-qc-ldpc-trapping-sets-and-leo-doppler-pll-slips/probes/verify_polar_ldpc_leo_pll.py
   ```
   Confirm `exit 0` and check that `rep8_i8_wrong_path_beats_true == true`, `avx512_vpabsb_neg128_corrupted_min == -128`, `standard_8b6b_oms_converged == false` (`5` errors) vs. `syndrome_peeled_oms_converged == true` (`8` iterations, `0` errors), and `costas_2nd_order_quadrant_slips == 431` vs. `pll_3rd_order_quadrant_slips == 0`.
2. **Check Upstream `aff3ct` Fixed-Point Path-Metric and `LDPC` `ONMS` Guards**:
   Diff `include/Module/Decoder/Polar/SCL/Decoder_polar_SCL_fast_sys.hxx` (`normalize_scl_metrics`, lines `61-90`), `Decoder_polar_SCL_fast_CA_sys.hxx` (`select_best_path`, lines `96-110`), and `src/Module/Decoder/LDPC/BP/Horizontal_layered/ONMS/Decoder_LDPC_BP_horizontal_layered_ONMS_inter.cpp` (`lines 440-465`) to check whether `signed char` arithmetic has been replaced with saturating `subs` / `vpaddusb` and whether `select_best_path` still defaults `best_path` to `paths[0]` when all `CRC`s fail.
3. **Check Upstream `GNU Radio` `control_loop` Order and `gr-satellites` NCO Wrapping**:
   Diff `gr-blocks/lib/control_loop.cc` (`update_gains`, `advance_loop`) and `gr-digital/lib/costas_loop_cc_impl.cc` in `gnuradio/gnuradio` to check whether an optional 3rd-order `Type-III` frequency-rate integrator (`d_fdot`) or `FLL` band-edge assist has been added to `control_loop`.
