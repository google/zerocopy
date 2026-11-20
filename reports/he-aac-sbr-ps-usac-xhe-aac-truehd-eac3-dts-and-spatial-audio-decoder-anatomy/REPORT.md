# HE-AAC SBR/PS, USAC/xHE-AAC, Dolby E-AC-3 and TrueHD/MLP, DTS/DCA, and IAMF Spatial Audio Decoder Anatomy

## Summary

Beyond baseline MDCT/LPC stereo codecs (AAC-LC, MP3, Opus, FLAC, and baseline 5.1 AC-3), broadcast, Blu-ray, cinema, and streaming media rely on six parametric bandwidth-extension, speech/transform-hybrid, lossless-matrixed, and immersive spatial audio architectures: **HE-AAC v1 Spectral Band Replication (SBR)**, **HE-AAC v2 Parametric Stereo (PS)**, **ISO/IEC 23003-3 USAC / xHE-AAC**, **Dolby Enhanced AC-3 (E-AC-3)**, **Dolby TrueHD / Meridian Lossless Packing (MLP)**, and **DTS Coherent Acoustics (`Core`, `XXCH`/`X96`, lossless `XLL`, low-bitrate `LBR`)** alongside **AOMedia IAMF**. Direct source inspection of `FFmpeg/FFmpeg` at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, contrasted against `ittiam-systems/libxaac` (`2fbadd57bca46693b7a077bcf1513131106d960c`), `mstorsjo/fdk-aac` (`ec82feb39662ac77e24ee9b324d5962e91bc79c5`), and `AOMediaCodec/iamf-tools` (`7a52020dec74976394a730455a473e2933350b4d`), establishes five load-bearing facts for a formally verified clean-room Rust implementation:

1. **HE-AAC SBR/PS fixed-point dynamic-range fragility and zero fixed-point SIMD (`aacsbr*`, `sbrdsp*`, `aacpsdsp*`):** FFmpeg compiles SBR and PS twice (`USE_FIXED = 0` `float` vs `USE_FIXED = 1` 32-bit `int`/`SoftFloat`), gating **all** SIMD dispatch (`x86`, `aarch64`, `arm`, `riscv`) behind `#if !USE_FIXED` (`sbrdsp_template.c:98`, `aacpsdsp_template.c:224`). In `sbrdsp_fixed.c:226-240`, `sbr_hf_gen_c` accumulates second-order complex LPC products in `int64_t` and truncates `(int)((accu + 0x10000000) >> 29)` without saturation, overflowing signed 32-bit range whenever $|X_{\text{low}}| > \text{0x0fff0000}$ ($0.125\times \text{INT32\_MAX}$) as $|\alpha_{0,1}| \to 4.0$, while `sbr_sum64x5_c` (`sbrdsp_template.c:31`) sums five signed `int` QMF polyphase taps without unsigned or 64-bit widening prior to the `±(1<<24)` clamp at `aacsbr_template.c:1422-1434`.
2. **Incomplete native USAC / xHE-AAC in upstream FFmpeg (`libavcodec/aac/aacdec_usac.c` vs `libxaac`):** At `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, FFmpeg implements only the **Frequency-Domain (`CORE_MODE_FD = 0`)** path of USAC (`aacdec_ac.c` 16-bit context-adaptive arithmetic coder, complex stereo prediction, and baseline 2:1/4:1 SBR), returning **`AVERROR_PATCHWELCOME` on every `CORE_MODE_LPD = 1` (ACELP and TCX) frame** (`aacdec_usac.c:1788-1794`), returning `AVERROR_PATCHWELCOME` on time-warped MDCT (`line 1833`), leaving harmonic eSBR and PVC unimplemented (`aacsbr_template.c:1259, 1295`), and duplicating mono downmix onto channel 1 in place of MPS212 stereo synthesis (`aacdec_usac.c:1905-1908`). Full ISO/IEC 23003-3 conformance requires clean-room implementation of ACELP algebraic vector quantization (`AVQ`), LPC-weighted TCX MDCT (`256`/`512`/`1024`), Forward Aliasing Cancellation (`FAC`) transition synthesis, harmonic DFT eSBR, and MPS212 decorrelation/upmix as realized in `libxaac`.
3. **TrueHD / MLP bit-exact lossless invariants, asymmetric flush bug, and zero 64-bit ARM/RISC-V SIMD (`mlpdec.c`, `mlpdsp.c`):** Lossless reconstruction chains block-adaptive FIR+IIR prediction (`mlp_filter_channel`) with cascaded in-place channel rematrixing (`ff_mlp_rematrix_channel` using deterministic LFSR noise channels) verified per restart interval against an 8-bit XOR-folded `lossless_check` nibble (`mlpdec.c:602-609`). Upstream `mlpdec` has **no `aarch64` NEON or `riscv64` RVV assembly** (`mlpdsp.c:133-137` dispatches only `x86` and 32-bit `arm`), discards the 4th Dolby Atmos object-audio substream (`m->max_decoded_substream = FFMIN(m->num_substreams - 1, 2)`, `mlpdec.c:417`), has zero signed-shift headroom past 8 channels in `mlpdsp.c:118` (`(sample & 0xffffff) << mat_ch` reaches bit 30 at `mat_ch == 7`), and contains an asymmetric loop bound in `mlp_decode_flush` (`mlpdec.c:1420`, resetting `substr <= m->max_decoded_substream` rather than `< MAX_SUBSTREAMS`), leaving stale `lossless_check_data` across stream layout upshifts after `avcodec_flush_buffers`.
4. **E-AC-3 and DTS multi-profile layering (`eac3dec.c`, `dcadec.c`, `dca_core.c`, `dca_xll.c`, `dca_lbr.c`):** E-AC-3 extends AC-3 with 6-block 1536-point Adaptive Hybrid Transform (AHT) DCT-II pre-filtering, Spectral Extension (SPX wrap-point notch filtering + noise/tonal blending, `eac3dec.c:56-140`), Enhanced Coupling, and dependent substreams up to 15.1 channels. DTS (`dcadec.c:232-310`) layers backward-compatible 32-subband ADPCM/QMF `Core` (`dca_core.c`) with Extension Substreams (`EXSS`) carrying either **XLL** bit-exact lossless multi-band adaptive LPC + Rice/Hybrid-Rice coding (`dca_xll.c:491-610`) or standalone **LBR (DTS Express)** sinusoidal + IMDCT low-bitrate coding (`dca_lbr.c:1689-1735`).
5. **IAMF container-vs-renderer boundary (`libavformat/iamf*` vs `iamf-tools`):** FFmpeg implements AOMedia IAMF OBU parsing, muxing, and `AVStreamGroup` metadata export (`AudioElement`, `MixPresentation`, animated gain/demixing/recon-gain parameter blocks over Opus, AAC-LC, FLAC, and PCM codec substreams, `libavformat/iamf_parse.c:36-115`, `libavutil/iamf.h`), but performs **no scene-based Ambisonics-to-loudspeaker, channel-to-binaural HRTF, or recon-gain DSP rendering**—which lives in `AOMediaCodec/iamf-tools` (`iamf/cli/renderer/`).

## Applicability

This report characterizes:

- **`FFmpeg/FFmpeg` at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`:** `libavcodec/{aacsbr*,sbrdsp*,aacps*,aac/aacdec_usac*,aac/aacdec_ac*,aac/aacdec_lpd*,ac3dec*,eac3dec*,ac3dsp*,mlp*,dcadec.c,dca_core*,dca_exss*,dca_xll*,dca_lbr*,dcadsp*,synth_filter*}`, architecture SIMD backends (`libavcodec/{x86,aarch64,arm,riscv,mips}/`), and IAMF modules (`libavformat/iamf*`, `libavutil/iamf*`).
- **Reference codec and renderer repositories:**
  - `ittiam-systems/libxaac` at `2fbadd57bca46693b7a077bcf1513131106d960c` (complete ISO/IEC 23003-3 USAC/xHE-AAC decoder including LPD ACELP/TCX/FAC, eSBR DFT harmonic transposer, and MPS212).
  - `mstorsjo/fdk-aac` at `ec82feb39662ac77e24ee9b324d5962e91bc79c5` (Fraunhofer fixed-point HE-AAC v1/v2 and xHE-AAC decoder/encoder).
  - `AOMediaCodec/iamf-tools` at `7a52020dec74976394a730455a473e2933350b4d` (reference IAMF v1.1.0 OBU processor and layout/binaural renderer).
- **Normative specifications:** ISO/IEC 14496-3:2019 (§4.6.18 SBR, §8.6.4 PS), ISO/IEC 23003-3:2020 (USAC), ATSC A/52:2018 / ETSI TS 102 366 V1.4.1 (AC-3 / E-AC-3), ETSI TS 102 114 V1.6.1 (DTS Core/XXCH/X96/XLL/LBR), and AOMedia IAMF v1.1.0.

Baseline AAC-LC spectral decoding, MP3, Opus (`SILK`+`CELT`), FLAC, baseline AC-3 256/512-point IMDCT, and `libswresample` are covered in companion corpus packages `aac-mp3-opus-flac-ac3-audio-codecs-imdct-and-swresample-swscale-kernels` and `webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows`.

## Findings

### 1. Cross-Codec DSP and SIMD ISA Coverage Matrix

`Basis: source`

Across all 50 architecture-specific files in `libavcodec/{x86,aarch64,arm,riscv,mips}/` touching parametric, surround, and lossless audio DSP at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, SIMD acceleration is distributed as follows:

| DSP Table / Subsystem | Precision | `x86_64` (`libavcodec/x86/`) | `aarch64` (`libavcodec/aarch64/`) | `riscv64` (`libavcodec/riscv/`) | `armv7` / `mips` | Key Hot Kernels |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`SBRDSPContext`** (`sbrdsp`) | `f32` (`!USE_FIXED`) | `sbrdsp.asm` (SSE/SSE2/SSE3/AVX) | `sbrdsp_neon.S` | `sbrdsp_rvv.S` | `arm/sbrdsp_neon.S` | `sum64x5`, `qmf_{pre,post}_shuffle`, `qmf_deint_bfly`, `autocorrelate`, `hf_gen`, `hf_g_filt`, `hf_apply_noise[0..3]` |
| **`SBRDSPContext`** (`sbrdsp_fixed`) | `i32` + `SoftFloat` | **None** | **None** | **None** | **None** | Scalar C only (`#if !USE_FIXED` at `sbrdsp_template.c:98`) |
| **`PSDSPContext`** (`aacpsdsp`) | `f32` (`!USE_FIXED`) | `aacpsdsp.asm` (SSE/SSE3/FMA3) | `aacpsdsp_neon.S` | `aacpsdsp_rvv.S` | `arm/aacpsdsp_neon.S` | `add_squares`, `mul_pair_single`, `hybrid_analysis`, `decorrelate`, `stereo_interpolate[0..1]` |
| **`AACArith` / USAC LPD** | `u16` / `f32` | **None** (uses `av_tx` for FD MDCT) | **None** | **None** | **None** | `ff_aac_ac_decode` (`aacdec_ac.c`); LPD unimplemented (`AVERROR_PATCHWELCOME`) |
| **`AC3DSPContext`** (`ac3dsp`) | `f32` & `i32` | `ac3dsp.asm`, `ac3dsp_downmix.asm` | `ac3dsp_neon.S` | `ac3dsp_rvb.S`, `ac3dsp_rvv.S`, `ac3dsp_rvvb.S` | `arm/ac3dsp*.S`, `mips/ac3dsp_mips.c` | `ac3_exponent_min`, `float_to_fixed24`, `bap` bit allocation, `downmix` |
| **`MLPDSPContext`** (`mlpdsp`) | `i32` / `i64` lossless | `mlpdsp.asm` (SSE4/AVX2) | **None** | **None** | `arm/mlpdsp_armv{5te,6}.S` | `mlp_filter_channel` (FIR+IIR), `mlp_rematrix_channel`, `mlp_pack_output` |
| **`DCADSPContext` + `SynthFilter`** | `f32` & `i32` (XLL) | `dcadsp.asm`, `synth_filter.asm` | `dcadsp_neon.S`, `synth_filter_neon.S` | **None** | `arm/synth_filter_{neon,vfp}.S` | `decode_hf`, `decode_joint`, `lfe_fir`, `qmf_32_subbands`, `lbr_bank`, `decor` |

Two immediate performance findings stand out for clean-room engineering:
1. **TrueHD / MLP on `aarch64` (Apple Silicon, ARMv8/v9 servers, Android TV) and `riscv64` runs 100% scalar C** in upstream FFmpeg (`mlpdsp.c:133-137`), even though `mlp_rematrix_channel` (`mlpdsp.c:74-89`) is a dense cross-channel dot product over `blockpos` samples and `mlp_pack_output` (`mlpdsp.c:113-124`) is a tight interleave+XOR-checksum loop trivially vectorizable in NEON/RVV (`mlp_filter_channel` remains sample-serial due to 1-sample IIR feedback `result - accum`, though inner tap dot products over `firorder <= 8, iirorder <= 4` fit in a single 128-bit register!).
2. **Fixed-point HE-AAC (`aac_fixed`) has zero SIMD across all architectures** (`sbrdsp_template.c:98`, `aacpsdsp_template.c:224`), whereas `mstorsjo/fdk-aac` (`ec82feb39662ac77e24ee9b324d5962e91bc79c5`) uses fixed-point arithmetic exclusively with dedicated ARM/x86 intrinsics. On every target with hardware `f32` SIMD (`x86_64` SSE2/AVX2, `aarch64` NEON, `riscv64` RVV `Zve32f`, `wasm32` SIMD128), floating-point SBR/PS (`f32`) is strictly faster and dramatically simpler to prove overflow-free than FFmpeg's dual `INTFLOAT` macro-templated fixed-point path.

---

### 2. HE-AAC v1 Spectral Band Replication (`aacsbr*`, `sbrdsp*`)

`Basis: normative + source + execution + derived`

Under ISO/IEC 14496-3:2019 §4.6.18, SBR reconstructs high-frequency spectrum (`kx .. kx + m`) from a half-rate (2:1) or quarter-rate (4:1 in ELD/USAC) core AAC-LC stream inside the **64-band Complex Quadrature Mirror Filterbank (QMF)** domain:

1. **32-band Analysis QMF (`sbr_qmf_analysis`, `libavcodec/aacsbr_template.c:1405-1440`):**
   Processes 32 core time-domain samples per time slot (`numTimeSlots = 16` for 1024/2048 frames -> `32` QMF slots per frame) through a 320-tap prototype window, folding 5 blocks of 64 samples via `sbrdsp->sum64x5(z)` (`sbrdsp_template.c:27-34`), shuffling (`qmf_pre_shuffle`), executing a 64-point `av_tx` MDCT (`mdct_fn`), and post-shuffling (`qmf_post_shuffle`) into complex subbands `W[buf_idx][t][0..31][re,im]`.
2. **High-Frequency Generation (`hf_gen`, `sbrdsp_fixed.c:207-241` / float equivalent):**
   Computes lag-0, lag-1, and lag-2 complex autocorrelations $\phi(i, j)$ over $38$ QMF time slots (`t_HFGen = 8` lookback + `32` active slots, `sbr_autocorrelate_c` at `sbrdsp_fixed.c:145-205`), solves the $2 \times 2$ Yule-Walker linear system with determinant guard $d = \phi(1,1)\phi(2,2) - \frac{1}{1+\varepsilon}|\phi(1,2)|^2$ and magnitude bound $\|\alpha_0\|, \|\alpha_1\| < 4$, chirps by bandwidth-expansion factor `bw` ($\alpha_0' = \alpha_0 \cdot \text{bw}$, $\alpha_1' = \alpha_1 \cdot \text{bw}^2$), and synthesizes patched upper QMF bands `k in kx .. kx + m - 1` via 2nd-order complex auto-regression:
   $$X_{\text{high}}[k, t] = X_{\text{low}}[p(k), t] + \alpha_0' X_{\text{low}}[p(k), t-1] + \alpha_1' X_{\text{low}}[p(k), t-2]$$
3. **Envelope Adjustment, Sinusoidal/Noise Injection, and 64-band Synthesis QMF (`sbr_hf_assemble` + `sbr_qmf_synthesis`, `aacsbr_template.c:1447-1498`):**
   Scales `X_high` by dequantized spectral-envelope gains `g_filt` (`sbr_hf_g_filt`), injects deterministic Q31 complex table noise `ff_sbr_noise_table` (`512` entries + `8` wrap entries for branchless SIMD vector reads, `sbrdsp_template.c:111-260`) plus optional missing-harmonic sinusoids `s_m` rotated by phase $j^{(t + \phi_k) \bmod 4}$ (`sbr_hf_apply_noise_0..3`, `sbrdsp_template.c:50-78`), and synthesizes 64 time samples per slot via two 64-point MDCTs (`mdct_buf[0..1]`), butterfly deinterleaving (`qmf_deint_bfly`), and a 10-stage 640-tap polyphase window accumulation (`dsp->vector_fmul` + 9 `vector_fmul_add` calls over a `1280`-element ring `v0`, `aacsbr_template.c:1485-1495`; `div = 1` runs 32-band downsampled synthesis).

**Fixed-point overflow hazards verified by source and execution (`Basis: source + execution`):**
- **Unclamped `sbr_sum64x5_c` signed addition (`sbrdsp_template.c:27-34`) and `qmf_{pre,post}_shuffle` negation (`sbrdsp_fixed.c:98, 107`):** `sbr_sum64x5_c` adds five `int32_t` polyphase terms in signed `int` **before** `aacsbr_template.c:1422-1434` clamps `z[64..127]` to `±(1 << 24)`. Furthermore, while `sbr_neg_odd_64_c` (`sbrdsp_fixed.c:89`) uses `-(unsigned)x[i]` to avoid `-INT32_MIN` UB, `sbr_qmf_pre_shuffle_c` (`line 98`) and `sbr_qmf_post_shuffle_c` (`line 107`) still execute raw `-z[...]`.
- **Narrow Q29 headroom in `sbr_hf_gen_c` (`sbrdsp_fixed.c:207-241`):** `alpha[0..3]` stores $\alpha_1 \cdot \text{bw}^2$ and $\alpha_0 \cdot \text{bw}$ in signed **Q29** (so maximal magnitude $< 4.0$ maps to `0x7fffffff`). Executing `sbr_hf_gen_c`'s exact accumulator (`PROBE3_SBR_HFGEN` in `run_probes.c`) confirms that `(int)((accu + 0x10000000) >> 29)` avoids 32-bit signed wraparound across valid $|\alpha_{0,1}| < 4.0$ **if and only if $|X_{\text{low}}| \le \text{0x0fff0000}$** ($2^{-3} \cdot \text{INT32\_MAX}$, i.e., $0.5$ in Q29). Upstream avoids wraparound on normal streams only because `aacsbr_template.c:1423-1433` hard-clamps analysis MDCT inputs to `±(1 << 24)` (`0x01000000`), leaving ~4 bits of margin across the 64-point MDCT—an implicit cross-function invariant nowhere enforced by C types.

---

### 3. HE-AAC v2 Parametric Stereo (`aacps.c`, `aacpsdsp_template.c`)

`Basis: normative + source`

ISO/IEC 14496-3:2019 §8.6.4 synthesizes stereo `(L, R)` from a mono SBR QMF subband signal `S[64][32]` using compact spatial side information (`1`–`3` kbps):

1. **Sub-subband Hybrid Filterbank (`ps_hybrid_analysis_c`, `libavcodec/aacpsdsp_template.c:46-102`):**
   Because uniform 64-band QMF resolution ($\approx 375\text{ Hz}$ at $48\text{ kHz}$) is too coarse for low-frequency human auditory critical bands, PS splits the lowest 3 or 5 QMF bands via linear-phase 13-tap complex FIR filters (`in[0..12]` folded symmetrically into `inre0/1`, `inim0/1` around center tap `in[6]`, `aacpsdsp_template.c:53-77`), producing `71` (20-band stereo mode) or `91` (34-band stereo mode) hybrid subbands.
2. **All-Pass Reverberant Decorrelation (`ps_decorrelate_c`, `aacpsdsp_template.c:104-144`):**
   Synthesizes an orthogonal diffuse signal $D[k, n]$ from $S[k, n]$ via phase rotation $\phi_{\text{fract}}[k]$ followed by a **3-stage (`PS_AP_LINKS = 3`) Schroeder fractional-delay complex all-pass cascade** with decay-sloped gains $a_m \cdot g_{\text{decay}}[k]$ ($a = \{0.651439, 0.564718, 0.489542\}$ in Q31, delays $3, 4, 5$ QMF slots) and transient ducking multiplier `transient_gain[n]` (preventing pre-/post-echo smearing on percussive attacks). Notice that `ps_decorrelate_c` carries a loop-carried recurrence along `ap_delay[m][n+2-m] -> ap_delay[m][n+5]` with minimum lag `3` slots (`m = 2`: reads `n`, writes `n + 5`), permitting 3-to-4-slot SIMD vectorization along time or embarrassingly parallel SIMD across hybrid subbands `k`.
3. **2x2 Complex Up-Mixing Matrix Interpolation (`ps_stereo_interpolate_{,ipdopd}_c`, `aacpsdsp_template.c:146-211`):**
   Maps **IID** (Inter-channel Intensity Difference) and **ICC** (Inter-channel Coherence) into corner matrix $H = \begin{pmatrix} h_{11} & h_{21} \\ h_{12} & h_{22} \end{pmatrix}$—plus complex phase rotations `(h0*, h1*)` when **IPD/OPD** (Inter-channel / Overall Phase Difference) is active—and linearly steps `h += h_step` per QMF slot to prevent zipper noise. Note lines `154-157, 166-169, 185-188`: FFmpeg explicitly types `hs*` as `UINTFLOAT` (`unsigned int` in `USE_FIXED`) to suppress UBSan traps when linear fixed-point stepping slightly overshoots or wraps at envelope boundaries.

---

### 4. ISO/IEC 23003-3 USAC / xHE-AAC: Native FFmpeg Gap vs `libxaac` Anatomy

`Basis: normative + source`

ISO/IEC 23003-3 (USAC / xHE-AAC) unifies transform audio coding and speech CELP coding within a single bitstream capable of switching **frame-by-frame** (`core_mode` 1-bit flag per channel, `aacdec_usac.c:1771`) between Frequency Domain (`FD`, `core_mode == 0`) and Linear Prediction Domain (`LPD`, `core_mode == 1`).

#### 4.1 What Upstream FFmpeg (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) Actually Implements
Direct audit of `libavcodec/aac/{aacdec_usac.c,aacdec_ac.c,aacdec_lpd.c,aacdec_usac_mps212.c}` and `libavcodec/aacsbr_template.c` reveals that native FFmpeg USAC is a **partial `CORE_MODE_FD`-only decoder**:

- **Implemented in FFmpeg:**
  - **16-bit Tuple Context-Adaptive Arithmetic Coder (`aacdec_ac.c:25-205`, `aacdec_ac.h:27-39`):** Resamples previous-frame context map `state->last[513]` across window-length transitions (`1024 <-> 128` via `ratio = last_len / (float)N`, `aacdec_ac.c:31-46`), hashes 4-neighborhood context `c` via binary search over `ff_aac_ac_hash_m` (`ff_aac_ac_get_pk`, `lines 73-89`), and decodes 2-tuple spectral symbols over CDF tables of exact lengths `{2, 4, 17, 27}` using branch-unrolled binary search (`ff_aac_ac_decode`, `lines 110-168`). Note `AACArithState.last` has length `512 + 1 = 513` (`aacdec_ac.h:28`), safely accommodating `state->last[i + 1]` up to `N = 1024` (`i <= 511` 2-tuples; if `N = 2048` core frames were ever passed without `/2` tuple halving beyond `i = 511`, `i + 1` would require `1025` entries, so `i < 512` is a mandatory proof invariant!).
  - **Complex Stereo Prediction (`apply_complex_stereo`, `aacdec_usac.c:1380-1485`):** Estimates quadrature (imaginary MDCT) spectrum `dmix_im` from real MDCT spectrum `re` via a 7-tap real-to-imaginary FIR filter (`lines 1388-1433`) and predicts side/mid bands via `c2[z] - alpha_re * c1[z] - alpha_im * dm_im[z]`.
  - **Audio Pre-Roll (`parse_audio_preroll`, `aacdec_usac.c:1913-2010`):** Parses ISO/IEC 23003-3 `AudioPreRoll()` extension payloads for seamless bitrate-adaptive DASH/HLS stream switching (`indep_flag == 1`).
- **Unimplemented / Stubbed in FFmpeg (`Basis: source`):**
  1. **`CORE_MODE_LPD` (`aacdec_usac.c:1788-1794`, `aacdec_lpd.c:1-138`):** Calls stub `ff_aac_ldp_parse_channel_stream` (which `skip_bits(gb, 4*n)` over algebraic codebook base indices at `aacdec_lpd.c:84`!) and unconditionally returns **`AVERROR_PATCHWELCOME`** (`"AAC USAC LPD is not implemented"`). Consequently, **any xHE-AAC speech or mixed speech/music stream that exercises LPD (nearly all low-bitrate `< 32 kbps` xHE-AAC streams!) fails to decode in native FFmpeg** unless built against external `libfdk-aac` (`mstorsjo/fdk-aac`).
  2. **Forward Aliasing Cancellation (`FAC`) synthesis (`aacdec_usac.c:1869-1877`):** `ff_aac_parse_fac_data` consumes the FAC bitstream bits so `FD` frames with `fac_data_present == 1` do not desynchronize the bitreader, but **discards `ue->fac`** because `LPD -> FD` transitions cannot occur while `LPD` is rejected.
  3. **Time-Warped MDCT (`aacdec_usac.c:1827-1835`):** Returns `AVERROR_PATCHWELCOME` when `tw_data_present == 1`.
  4. **MPS212 Stereo Upmix (`aacdec_usac.c:1891-1909`):** Parses MPS212 bitstream syntax (`parse_mps212`), then executes `memcpy(che->ch[1].output, che->ch[0].output, ...)` with comment `/* The MPS212 upmix is not implemented, output the downmix on both channels */`—collapsing stereo `stereo_config_index in {1, 2}` xHE-AAC streams to dual-mono!
  5. **Enhanced SBR (`eSBR`) Harmonic Patching and Predictive Vector Coding (`PVC`) (`aacsbr_template.c:1259, 1295, 1314, 1346`):** Left as `/* if (harmonicSBR) ... */` and `/* if (bs_pvc) ... */` comments.

#### 4.2 Complete Clean-Room USAC Specification Anatomy (Grounded in ISO/IEC 23003-3 & `libxaac`)
Cross-referencing ISO/IEC 23003-3:2020 and `ittiam-systems/libxaac` (`2fbadd57bca46693b7a077bcf1513131106d960c`, `decoder/ixheaacd_{acelp_decode,tcx_fwd_alcnx,fwd_alias_cnx,avq_dec,lpc,esbr_polyphase,mps_dec}.c`) defines the exact missing clean-room modules:
1. **LPD Superframe Mode Tree (`lpd_mode in 0..25`):** Partitions a `1024`-sample (`768`-sample in 3:4 mode) superframe into four `256`-sample (`192`-sample) quarters covered either by four `ACELP` frames (`lpd_mode == 0`), combinations of `ACELP` and `256`-/`512`-sample **TCX-20 / TCX-40**, or a single `1024`-sample **TCX-80** (`lpd_mode == 25`), parameterized by quantized Immittance Spectral Frequency (**ISF/ISP**) vectors converted to 16th-order LPC polynomial $A(z)$ (`ixheaacd_lpc.c`).
2. **ACELP & AVQ (`ixheaacd_acelp_decode.c`, `ixheaacd_avq_dec.c`):** Each ACELP frame comprises 4 subframes of 64 samples: fractional pitch-lag adaptive codebook interpolation (`ixheaacd_interpol_filt`), pulse-position algebraic innovation codebook + pitch sharpening (`ixheaacd_acelp_pitch_sharpening`), synthesis through $1/A(z)$, and bass post-filtering (`bpf_control_info`). TCX-20/40/80 and FAC decode spectral/correction vectors via **Algebraic Vector Quantization (AVQ)** over Gosset lattice $RE_8$ Voronoi codebooks (`parse_qn` + base codebook index $I$ + Voronoi extension vector $\mathbf{k}_v$ in `ixheaacd_avq_dec.c`), shape noise in the LPC-weighted MDCT domain, and apply inverse MDCT + $1/A(z)$ synthesis (`ixheaacd_tcx_fwd_alcnx.c`).
3. **Forward Aliasing Cancellation (`FAC`, `ixheaacd_fwd_alias_cnx.c`):** Because an `FD` or `TCX` MDCT frame carries time-domain aliasing in its overlap regions whereas `ACELP` produces non-aliased time-domain LPC samples, switching `FD/TCX <-> ACELP` without correction causes audible clicks. FAC transmits a `64`- or `128`-point AVQ-quantized MDCT correction signal (`fac_len = core_frame_len / 8` or `/ 16`), passes it through inverse DCT-IV and weighted LPC synthesis filter $1/A_{\gamma}(z)$ (`ixheaacd_weighted_synthesis_filter`), and adds it across the transition boundary to cancel the missing MDCT overlap-add alias term exactly!
4. **Harmonic eSBR (`ixheaacd_esbr_polyphase.c`) and MPS212 (`ixheaacd_mps_*.c`):** Harmonic eSBR replaces QMF copy-up patching (which shifts harmonic spacing rather than multiplying fundamental frequencies, causing metallic inharmonicity on low-bitrate tonal instruments) with phase-vocoder **DFT/oversampled-QMF frequency stretching ($T = 2, 3, 4$)** (`ixheaacd_complex_anal_filt`), while MPS212 runs a 71-band hybrid QMF stereo decorrelator + CLD/ICC/IPD M1/M2 matrix upmixer analogous to HE-AAC v2 PS.

---

### 5. Dolby AC-3 / E-AC-3, TrueHD / MLP, DTS (`Core`/`XLL`/`LBR`), and IAMF

#### 5.1 Dolby Enhanced AC-3 (`libavcodec/eac3dec.c`, ATSC A/52:2018 Annex E)
`Basis: normative + source`

While baseline AC-3 (`ac3dec.c`) uses 6 audio blocks of 256 MDCT bins per 1536-sample frame with 5-bit differential exponents and masked-threshold Bit Allocation Pointers (`BAp`), E-AC-3 (`eac3dec.c:48-550`) introduces four clean-room-relevant extensions:
- **Adaptive Hybrid Transform (`AHT`) & Gain Adaptive Quantization (`GAQ`, `eac3dec.c:49-54`):** On stationary tonal signals where all 6 blocks share exponents, AHT applies a secondary **6-point Type-II DCT** across the 6 blocks of each frequency bin (yielding $6 \times 256 = 1536$-sample frequency resolution) quantized with VQ or non-uniform `EAC3_GAQ_{12,14,124}` mantissa codes.
- **Spectral Extension (`SPX`, `ff_eac3_apply_spectral_extension`, `eac3dec.c:56-160`):** Copies baseband MDCT coefficients `[spx_dst_start_freq .. spx_src_start_freq)` cyclically into high-frequency SPX bands, applies a 5-tap notch filter `ff_eac3_spx_atten_tab` across wrap discontinuities (`lines 112-126`) to suppress harmonic comb artifacts, and blends scaled tonal copies (`sscale`) with RMS-matched PRNG noise (`nscale`, `lines 131-155`). Note `eac3dec.c:30-38` documents that Reduced Sample Rates and Transient Pre-noise Processing (`TPNP`) remain unimplemented in FFmpeg.
- **Dependent Substreams:** Combines an independent 5.1 substream (`strmtyp == 0`) with up to 8 dependent substreams (`strmtyp == 1`, `chanmap` custom speaker bitmask) to deliver 7.1, 9.1, or 15.1 channel beds while maintaining legacy 5.1 S/PDIF core extraction (`libavcodec/bsf/eac3_core.c`).

#### 5.2 Dolby TrueHD / Meridian Lossless Packing (`libavcodec/mlpdec.c`, `mlpdsp.c`)
`Basis: source + derived`

TrueHD and MLP (`mlpdec.c:410-1478`, `mlpdsp.c:27-138`, `mlp.h:33-95`) achieve **bit-exact 16/20/24-bit up-to-192 kHz lossless compression** alongside hierarchical downmix scalability (`Substream 0`: 2ch Lt/Rt or stereo; `Substream 1`: 5.1; `Substream 2`: 7.1; `Substream 3`: Dolby Atmos object audio):

1. **Two-stage bit-exact integer inverse filter + cascaded rematrixing (`mlpdsp.c:27-90`):**
   - Each channel first reconstructs samples through an up-to-8-tap FIR + up-to-4-tap IIR predictor (`mlp_filter_channel`, `mlpdsp.c:27-58`):
     $$\text{accum} = \left(\sum_{k=0}^{N_{\text{FIR}}-1} y[n-1-k] f_k + \sum_{m=0}^{N_{\text{IIR}}-1} e[n-1-m] g_m\right) \gg \text{shift}, \quad y[n] = (\text{accum} + r[n]) \mathbin{\&} \text{mask}, \quad e[n] = y[n] - \text{accum}$$
     Note the feedback term stored into `iirbuf` (`line 53`) is **`result - accum`** (which differs from `residual` whenever `(accum + residual) & mask` zeros quantized LSBs via `MSB_MASK(quant_step_size)`!). Any bit discrepancy in signed arithmetic right-shift `>> filter_shift` or `mask` causes exponential IIR divergence and immediate lossless check failure.
   - Next, `output_data` (`mlpdec.c:1127-1150`) generates deterministic LFSR noise channels (`generate_2_noise_channels` for MLP `0x31ea` sync; `fill_noise_buffer` via 256-entry `noise_table` for TrueHD `0x31eb` sync, `mlpdec.c:1070-1103`) and applies `num_primitive_matrices` **sequential in-place rank-1 shear updates** (`ff_mlp_rematrix_channel`, `mlpdsp.c:60-90`), overwriting `samples[dest_ch] = ((accum >> 14) & mask) + bypassed_lsbs` so subsequent matrices read already-updated `dest_ch` values (triangular lifting factorization over $\mathbb{Z}$—**strictly sequential across `mat`, parallel across `i in 0..blockpos`!**).
2. **Multi-layer integrity verification (`mlpdec.c:600-610, 1280-1286, 1365-1378`, `mlpdsp.c:118`):**
   Every access unit checks a 4-bit header nibble parity (`!= 0xF` rejects packet, `line 1283`), optional per-substream 8-bit parity (`^ parity == 0xa9`) + 8-bit CRC checksum (`ff_mlp_checksum8`, `lines 1371-1377`), and per-restart-interval **decoded-PCM `lossless_check`** (`mlpdsp.c:118` accumulates `lossless_check_data ^= (sample & 0xffffff) << mat_ch`, folded by `xor_32_to_8` and compared against the next restart header's 8-bit `lossless_check` at `mlpdec.c:602-609`).
   - **Zero signed-shift headroom past 8 channels (`mlpdsp.c:118`):** In C, `(sample & 0xffffff)` has type `int` (`int32_t`). At `MAX_MATRIX_CHANNEL_TRUEHD = 7` (`mlp.h:34`, 8-channel 7.1), bit 23 shifted left by `7` reaches bit 30 (`0x7fffff80`), leaving **0 bits of signed `int32_t` headroom** before sign-bit overflow UB at `mat_ch == 8`. Supporting TrueHD's 4th Atmos substream (`substr == 3`, up to 16 channels, currently discarded by `m->max_decoded_substream = FFMIN(m->num_substreams - 1, 2)` at `mlpdec.c:417`) requires widening `lossless_check_data` or shifting unsigned `uint32_t` modulo $2^{32}$ per specification.
3. **`avcodec_flush_buffers` (`mlp_decode_flush`) reset invariant and bug (`mlpdec.c:1415-1426`):**
   On seek/flush, `mlp_decode_flush` sets `m->params_valid = 0` (forcing `read_access_unit` at `line 1217` to drop non-key packets until a `0xf8726fb` major sync unit arrives, where `read_major_sync` at `lines 433-434` resets `restart_seen = 0` for all `MAX_SUBSTREAMS = 4`). However, `mlp_decode_flush` loops `for (int substr = 0; substr <= m->max_decoded_substream; substr++)` rather than `substr < MAX_SUBSTREAMS`! If a decoder previously decoded substream 2, downshifted `max_decoded_substream` to `0`, flushed via `avcodec_flush_buffers`, and resumed on a 7.1 major sync (`max_decoded_substream == 2`), `substream[2].lossless_check_data` retains its stale pre-downshift value (`!= 0xffffffff`), causing a spurious `"Lossless check failed"` warning on the post-flush restart header (`mlpdec.c:602-608`). In clean-room Rust, `flush()` must reset the entire `[SubStream; MAX_SUBSTREAMS]` array (`restart_seen = false`, `lossless_check_data = None`, zeroed `FilterParams::state`).

#### 5.3 DTS / DCA (`Core`, `XXCH`/`X96`, `XLL` Lossless, and `LBR`)
`Basis: normative + source`

ETSI TS 102 114 V1.6.1 and `libavcodec/{dcadec.c,dca_core.c,dca_exss.c,dca_xll.c,dca_lbr.c}` implement a modular core-plus-extension architecture:
- **Bitstream normalization (`dcadec.c:233-249`):** Raw DTS packets appear in 4 wire representations (16-bit big-endian, 16-bit little-endian, and 14-bit packed big-/little-endian S/PDIF words); `avpriv_dca_convert_bitstream` normalizes into 16-bit BE prior to parsing.
- **Core + XXCH / X96 (`dca_core.c`):** 32-band ADPCM + Huffman/block-code subband coder synthesized via a 512-tap (or 1024-tap perfect-reconstruction) 32-subband cosine-modulated QMF bank (`synth_filter` + `dcadsp->qmf_32_subbands`), extended to >5.1 channels by `XXCH` and to 96 kHz (64 subbands) by `X96`.
- **XLL (DTS-HD Master Audio Lossless, `dca_xll.c:490-610`):** Organizes channels into hierarchical `ChannelSet`s across 1 or 2 frequency bands (up to 192 kHz via decimator history `deci_history`, `lines 606-610`), coding adaptive 16th-order fixed-point LPC residuals (`part_a` unpredicted warmup + `part_b` predicted segment) with **Linear, Rice, or Hybrid-Rice** entropy coding (`nisosamples` isolated outlier locations flagged in `part_b[loc] = -1` and coded with fixed `bitalloc_hybrid_linear` bits while remaining residuals use Rice parameter `bitalloc_part_b`, `lines 570-595`), followed by pairwise lossless channel decorrelation and band-assembly QMF. When `XLL` is active without residual core override, it yields bit-exact integer PCM; when core-embedded residual coding is used, core QMF output must be bit-exact in fixed-point (`USE_FIXED`) to preserve losslessness!
- **LBR / DTS Express (`dca_lbr.c:1650-1745`):** Standalone ultra-low-bitrate extension substream (used for Blu-ray secondary PiP commentary and streaming) combining a subband filterbank (`dcadsp->lbr_bank`), parametric multi-group **tonal sinusoid synthesis** (`base_func_synth` / `synth_tones` with 22-subframe tonal-vs-residual phase alignment, `lines 1689-1700`), and forward/inverse MDCT overlap-add (`lines 1720-1727`).

#### 5.4 AOMedia IAMF: Demuxer/Model vs Spatial Renderer (`libavformat/iamf*` vs `iamf-tools`)
`Basis: normative + source`

AOMedia IAMF v1.1.0 decouples **codec compression** (exclusively reusing **Opus, AAC-LC, FLAC, and LPCM**—explicitly forbidding HE-AAC SBR/PS or xHE-AAC inside IAMF `CodecConfig` OBUs; note `aac_decoder_config` at `libavformat/iamf_parse.c:67-76` enforces `audio_roll_distance < 0` and MPEG-4 `object_type_id == 0x40`) from **immersive scene & presentation metadata**:
- **FFmpeg's IAMF scope (`libavformat/iamf_parse.c`, `iamf_reader.c`, `iamf_writer.c`, `libavutil/iamf.h`):** Parses standalone `.iamf` OBU streams and ISOBMFF `iacb`/`iamf` tracks into `AVStreamGroup` (`AV_STREAM_GROUP_PARAMS_IAMF_AUDIO_ELEMENT` for Scalable Channel Layout or First-/Higher-Order Ambisonics `FOA`/`HOA`, and `AV_STREAM_GROUP_PARAMS_IAMF_MIX_PRESENTATION` carrying ITU-R BS.1770-4 loudness annotations plus sample-accurate animated `AV_IAMF_PARAMETER_DEFINITION_{MIX_GAIN,DEMIXING,RECON_GAIN}` subblocks).
- **Missing rendering DSP (`AOMediaCodec/iamf-tools` at `7a52020dec74976394a730455a473e2933350b4d`, `iamf/cli/renderer/`):** FFmpeg emits raw substream `AVPacket`s per underlying codec track without rendering `MixPresentation`s. A complete clean-room spatial audio engine requires adding the three stateless/block-stateful IAMF rendering kernels implemented in `iamf-tools`: (1) scalable channel demixing (`S7 -> S5 -> S3 -> S2` via parameterized $\alpha, \beta, \gamma, \delta, w$ matrices + per-band `ReconGain` compensation for lossy Opus/AAC substream differences), (2) Ambisonics-to-loudspeaker projection matrices (`audio_element_renderer_ambisonics_to_channel.cc`), and (3) ITU-R BS.2051 / binaural HRTF FIR convolution (`af_afir` / partitioned RDFT!).

## Boundaries

- **Dolby Atmos object-audio (`OAMD` / `JOC`) and DTS:X (`UHQ` / `MDA`) proprietary renderers (`unsupported` in upstream FFmpeg / `not examined`):** Neither TrueHD 4th-substream Atmos Evolution (`mlpdec.c:417`), E-AC-3 Joint Object Coding (`JOC`) 3D object rendering, nor DTS:X object metadata inside `EXSS` has an open normative specification or upstream FFmpeg decoder implementation; FFmpeg decodes only the 5.1/7.1 channel bed.
- **MPEG-H 3D Audio (ISO/IEC 23008-3) (`unsupported` in native FFmpeg):** FFmpeg contains `libavformat` `mha1`/`mhm1` MP4 sample-entry demuxing only, without a native MPEG-H 3D Audio `libavcodec` decoder.
- **Hardware execution benchmarks across ARM64/RISC-V (`not examined` by execution):** Execution probes in this report ran on `x86_64` Linux; the `aarch64` and `riscv64` SIMD gaps (`mlpdsp`, `sbrdsp_fixed`, `dcadsp` on RVV) are established directly from upstream `Makefile` and `*_init.c` dispatch source (`Basis: source`).

## Evidence

### Primary Repository Sources Inspected

1. **`FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`):**
   - `libavcodec/aacsbr_template.c:1180-1545`, `libavcodec/sbrdsp_template.c:27-260`, `libavcodec/sbrdsp_fixed.c:33-250` — 32/64-band QMF analysis/synthesis, `USE_FIXED` `±(1<<24)` clamp (`lines 1422-1434`), `#if !USE_FIXED` SIMD guard (`sbrdsp_template.c:98`), `sbr_sum64x5_c` signed sum (`line 31`), `sbr_qmf_{pre,post}_shuffle_c` signed negation (`sbrdsp_fixed.c:98, 107`), and `sbr_hf_gen_c` Q29 truncation (`sbrdsp_fixed.c:207-241`).
   - `libavcodec/aacpsdsp_template.c:29-235` — 13-tap hybrid QMF filterbank, 3-link all-pass `ps_decorrelate_c`, `ps_stereo_interpolate_{,ipdopd}_c` `UINTFLOAT` stepping, and `#if !USE_FIXED` SIMD guard (`line 224`).
   - `libavcodec/aac/aacdec_usac.c:1380-1920`, `libavcodec/aac/aacdec_ac.c:25-170`, `libavcodec/aac/aacdec_ac.h:27-53`, `libavcodec/aac/aacdec_lpd.c:25-138` — 16-bit tuple arithmetic coder (`last[513]`), 7-tap real-to-imaginary complex stereo filter, `AVERROR_PATCHWELCOME` on `CORE_MODE_LPD` (`aacdec_usac.c:1788-1794`) and `tw_mdct` (`line 1833`), and unimplemented MPS212 upmix (`lines 1905-1908`).
   - `libavcodec/eac3dec.c:30-160` — SPX band copy, wrap-point 5-tap notch filter, and tonal/noise blend scaling.
   - `libavcodec/mlp.h:33-95`, `libavcodec/mlpdec.c:410-625, 1040-1478`, `libavcodec/mlpdsp.c:27-138` — 3-substream cap (`mlpdec.c:417`), FIR/IIR lossless predictor (`result - accum`), sequential lifting rematrixing, `lossless_check_data` shift bound (`mlpdsp.c:118`), `mlp_decode_flush` `substr <= m->max_decoded_substream` loop defect (`mlpdec.c:1420`), and `x86`/`arm`-only SIMD dispatch (`mlpdsp.c:133-137`).
   - `libavcodec/dcadec.c:162-290`, `libavcodec/dca_xll.c:490-610`, `libavcodec/dca_lbr.c:1650-1745` — 14/16-bit BE/LE sync conversion, `Core`+`EXSS` dispatch, `XLL` Linear/Rice/Hybrid-Rice isolated-sample coding, and `LBR` 5-group sinusoidal + IMDCT synthesis.
   - `libavformat/iamf_parse.c:36-115` & `libavutil/iamf.h:60-180` — IAMF `Opus`/`AAC-LC`/`FLAC`/`PCM` `CodecConfig` validation and `AVIAMFParamDefinition` structures.
   - `libavcodec/{x86,aarch64,arm,riscv,mips}/*` — Complete 50-file SIMD inventory for `sbrdsp`, `aacpsdsp`, `ac3dsp`, `mlpdsp`, `dcadsp`, and `synth_filter`.
2. **External Repositories Inspected:**
   - `ittiam-systems/libxaac` (`2fbadd57bca46693b7a077bcf1513131106d960c`) — `decoder/ixheaacd_{acelp_decode,tcx_fwd_alcnx,fwd_alias_cnx,avq_dec,lpc,esbr_polyphase,mps_dec}.c` (`armv7`, `armv8`, `x86`, `x86_64`).
   - `mstorsjo/fdk-aac` (`ec82feb39662ac77e24ee9b324d5962e91bc79c5`) — Fixed-point HE-AAC v1/v2 and xHE-AAC reference baseline.
   - `AOMediaCodec/iamf-tools` (`7a52020dec74976394a730455a473e2933350b4d`) — `iamf/cli/renderer/audio_element_renderer_{ambisonics_to_channel,channel_to_channel}.cc` and `gains/`.

### Executed Micro-Probe (`2026-11-20`, Linux `7.1.6` `x86_64`, Intel Xeon @ 2.20 GHz, GCC `15.2.0 -O2`)

- **Fixed-point SBR `sbr_hf_gen_c` headroom probe (`PROBE3_SBR_HFGEN` in `run_probes.c`):** Evaluated `sbrdsp_fixed.c:226-232` (`accu = X_low[i][0] * 0x20000000 + ...; (accu + 0x10000000) >> 29`) at boundary covariance gain `|alpha| = 0x7fffffff` ($4.0$ in Q29), confirming exact `int32_t` representability holds up to `max_safe_xlow = 0x0fff0000` (`0.4999` of Q29 unit = `0.1250` of `INT32_MAX`) and wraps signed `int32_t` above `0x10000000`.

## Revalidation

To cheaply revalidate whether upstream FFmpeg has closed any of the documented feature or safety gaps on a newer revision:

1. **Check USAC LPD, time-warping, MPS212, and eSBR completion:**
   ```bash
   grep -n 'PATCHWELCOME\|MPS212 upmix' libavcodec/aac/aacdec_usac.c libavcodec/aac/aacdec_lpd.c
   grep -n 'harmonicSBR\|bs_pvc' libavcodec/aacsbr_template.c
   ```
2. **Check `mlpdsp` AArch64/RISC-V SIMD, Atmos 4th substream, and `mlp_decode_flush`:**
   ```bash
   ls libavcodec/aarch64/*mlp* libavcodec/riscv/*mlp* 2>/dev/null
   grep -n 'max_decoded_substream\|lossless_check_data' libavcodec/mlpdec.c libavcodec/mlpdsp.c
   ```
3. **Check `USE_FIXED` SBR/PS SIMD guards and `sbr_hf_gen_c` saturation:**
   ```bash
   grep -n 'USE_FIXED' libavcodec/sbrdsp_template.c libavcodec/aacpsdsp_template.c
   sed -n '225,242p' libavcodec/sbrdsp_fixed.c
   ```
