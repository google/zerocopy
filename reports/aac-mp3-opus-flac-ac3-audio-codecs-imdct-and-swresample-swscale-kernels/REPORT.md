# FFmpeg Audio Codecs, `libavutil/tx` FFT/IMDCT Kernels, `libswresample`, and `libswscale`: Architecture, Cross-ISA Numerics, and Bounds Verification

## Summary

At commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, `FFmpeg/FFmpeg` implements `226` audio `AVCodecID` formats (`libavcodec/codec_id.h:332-569`, registering `216` first-party audio/PCM/DPCM/ADPCM decoders in `libavcodec/allcodecs.c:425-721`), backed by three shared numerical engines: `libavutil/tx` (`11` source/assembly files, `303 KB`, providing unified FFT/MDCT/IMDCT/RDFT/DCT transforms), `libswresample` (`51` files, `372 KB`, providing polyphase FIR resampling, dithering, and `41`-channel rematrixing), and `libswscale` (`169` files, `3.45 MB`, providing colorspace conversion, HDR tone/gamut mapping, and 2D spatial scaling).

Primary-source inspection and standalone C execution probes establish four load-bearing architectural and verification findings:

1. **Asymmetric SIMD coverage and non-associative FMA drift in `libavutil/tx`:** AAC (`1024`/`128`/`960`/`768`/`96`), Opus CELT (`120`/`240`/`480`/`960`), Vorbis (`32..4096`), and AC-3/E-AC-3 (`128`/`256`) converge on `av_tx_init` (`libavutil/tx.h:202`), whereas MP3 (`mpegaudiodec_template.c`) retains a dedicated `32`-band polyphase synthesis filterbank (`dct32` + `imdct36`) and FLAC (`flacdec.c`) uses exact integer LPC. Within `libavutil/tx`, hand-written SIMD exists **exclusively** for `AV_TX_FLOAT_*` on `x86` (`SSE2`–`AVX2`/`FMA3`, `libavutil/x86/tx_float_init.c`) and `aarch64` (`NEON`, `libavutil/aarch64/tx_float_init.c`), including a Chinese Remainder Theorem $15 \times 2^k$ Prime-Factor Algorithm (`fft_pfa_15xM`) tailored to Opus CELT and USAC frame sizes. Neither `AV_TX_INT32_MDCT` (used by `aac_fixed` and `ac3_fixed`) nor `riscv64` RVV has any `libavutil/tx` SIMD codelets. Executed binary32 IMDCT probes confirm hardware `fmaf` (`FMA3`/`NEON`) differs from unfused `mul + add` (`SSE3`/`AVX`/scalar) on `79.7%`–`89.4%` of output samples (`max_diff <= 4.17e-7`), while both—and cross-ISA-deterministic Q31 `AV_TX_INT32_MDCT` (`RMS <= 5.30e-6`)—stay well inside ISO/IEC 11172-4's full-compliance RMS tolerance ($2^{-15}/\sqrt{12} \approx 8.810 \times 10^{-6}$).
2. **Cross-library layering and accumulator-width hazards in audio decoders:** FFmpeg's native Opus decoder (`libavcodec/opus/dec.c:49, 72-81, 117`) embeds `libswresample` (`SwrContext`) with silence-primed filter lengths `{8, 16, 16, 16, 16}` to upsample SILK (`8/12/16 kHz`) to `48 kHz` instead of RFC 6716 §4.2.7.9's normative fixed-point ARMA/FIR resampler, trading bit-exact `libopus` parity for code reuse under psychoacoustic conformance. For lossless 32-bit FLAC (RFC 9639), stereo side-channel decorrelation ($L - R$) produces `33`-bit signed values (`[-2^{32}, 2^{32}-1]`), forcing `flacdsp.c:87-100` to maintain a third `int64_t` LPC tier (`flac_lpc_33_c`) using explicit `(uint64_t)` casts to prevent C signed 64-bit overflow undefined behavior on malformed autoregressive feedback streams.
3. **Gibbs $\ell_1$ filter overshoot in `libswresample` fixed-point accumulators:** Although `build_filter` (`libswresample/resample.c:96-115`) normalizes polyphase tap sums to unity DC gain ($\sum_k h_{0,k} = 1$, leaving minor polyphase DC ripple on rows `ph > 0` and clipping the `S16P` unity tap `32768 -> 32767`), negative sinc sidelobes push the worst-row $\ell_1$ norm $\|h_p\|_1 = \sum_k |h_{p,k}|$ to `1.9810` (`32`-tap Kaiser $\beta=9$) and `2.2563` (`64`-tap Kaiser $\beta=9$, `48 -> 44.1 kHz`). Executed adversarial $\pm 32767/-32768$ probes confirm a single `int32_t` Q15 accumulator reaches `2,422,697,878 > INT32_MAX`, overflowing signed 32-bit C arithmetic; `resample_template.c:113-126, 170` avoids UB only by splitting even/odd tap accumulators (`even_acc = 1,210,243,037`) summed in `int64_t` and widening `resample_linear` to `uint64_t` (`FELEM2U`).
4. **Dual-generation `libswscale` transition (`SWS_BACKEND_LEGACY` JIT vs. `SwsGraph`/`SwsOp`):** Upstream `libswscale` currently straddles two architectures: the legacy `SwsInternal` pipeline (`swscale.c`, `swscale_unscaled.c`, `utils.c:1725-1753`, which still allocates `PROT_WRITE -> PROT_EXEC` runtime-patched x86 MMXEXT code via `ff_sws_jit_alloc` / `ff_sws_jit_protect` in `jit.c:40-60`), and the modern `SwsGraph` pipeline (`graph.h`, `ops.h`, `ops_optimizer.c`, `uops.h`, `cms.h`, `lut3d.h`), which decomposes pixel format, range, matrix, transfer-function, and ITU-R BT.2100 HDR tone/gamut mapping into an `18`-op typed IR (`SWS_OP_READ..SWS_OP_LUT_3D`) with exact `AVRational64` algebraic optimization and composable `x86`/`aarch64`/`SPIR-V` micro-op backends.

## Applicability

This report characterizes `FFmpeg/FFmpeg` at commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` across `libavcodec/` (audio decoders and `*dsp` modules), `libavutil/tx*`, `libswresample/`, and `libswscale/`, interpreted against ISO/IEC 14496-3:2019 & ISO/IEC 23003-3:2020 (AAC / HE-AAC / USAC), ISO/IEC 11172-3:1993 & 11172-4:1995 (MPEG-1 Audio & conformance), IETF RFC 6716 & RFC 8251 (Opus), IETF RFC 9639 (FLAC), ATSC A/52:2018 (AC-3 / E-AC-3), and ITU-R BT.709-6 / BT.2020-2 / BT.2100-2 (SDR/WCG/HDR colorimetry).

Scope and relationship to sibling `reference-corpus/1` packages:

- **Cross-references without duplication:** Standalone `libopus` fixed-point SILK/CELT hybrid behavior, WebRTC NetEq jitter buffering, and standalone `libFLAC` LPC overflow mechanics are established in `webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows` (summarized inline where contrasted with FFmpeg's floating-point `libavcodec/opus/` and `lpc33` implementation). Formal IEEE-754 floating-point verification techniques—dyadic interval enclosures, Gappa roundoff certificates, and NaN payload refinement—are established in `ieee754-softfloat-dyadic-interval-gappa-certificates-and-nan-choice-refinement`, and SIMD tree-reduction reassociation certificates are covered in `ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`. Tetrahedral ICC 3D LUT interpolation geometry in `lcms2` is analyzed in `libwebp-huffman-tables-dav1d-rans-cdfs-and-lcms2-icc-tetrahedral-luts`.
- **Execution environment:** Standalone C numerical probes (`probe_audio_sws.c`) were compiled and executed on Linux `x86_64` with `gcc (Debian 15.2.0-14) 15.2.0` (`-O2 -mfma -lm`) under IEEE-754 round-to-nearest-even (`FE_TONEAREST`).

## Findings

### 1. Audio Decoder Taxonomy and Transform/Predictor Substrates in `libavcodec`

`Basis: normative + source + derived`

Across `libavcodec/allcodecs.c:425-721` and `libavcodec/Makefile`, FFmpeg's `216` first-party audio decoders partition into `106` transform/speech/lossless decoders, `37` PCM decoders (`62` total PCM `FFCodec` rules in `pcm.c`), `9` DPCM decoders, and `64` ADPCM decoders (`adpcm.c`). The seven flagship first-party families exhibit distinct algorithmic and numerical contracts:

| Codec Family (`libavcodec` Paths) | Normative Standard | Dual Fixed/Float? | Primary Synthesis Transform / Predictor | Frame / Window Geometry & Key Auxiliary DSP |
| :--- | :--- | :--- | :--- | :--- |
| **AAC / HE-AAC / USAC** (`aac/aacdec*.c`) | ISO/IEC 14496-3, ISO/IEC 23003-3 | **Yes:** `aac` (`FLTP`) vs. `aac_fixed` (`S32P`, `USE_FIXED=1`) | `libavutil/tx` `AV_TX_{FLOAT,INT32}_MDCT` (+ forward `1024` LTP MDCT, `aacdec.c:1276-1293`) | `1024`/`128` (LC), `960`/`120`, `768`/`96` (USAC), `512`/`480` (ELD); KBD ($\alpha=4,6$) & sine windows; `sbrdsp` (64-band QMF), `aacpsdsp`, `aacdec_lpd.c` (ACELP/TCX) |
| **MP3 / MPEG-1/2 Audio** (`mpegaudiodec_*.c`) | ISO/IEC 11172-3, ISO/IEC 13818-3 | **Yes:** `mp3float` (`FLTP`) vs. `mp3` (`S16P`/`S32P`) | Dedicated `MPADSPContext`: `imdct36_blocks_*` + `dct32` + `synth_filter_*` (`mpegaudiodec_template.c:75-97`) | `576` samples/granule (`32` subbands $\times$ `18` time slots; `3x6` short blocks); `512`-byte `BACKSTEP_SIZE` bit reservoir (`last_buf[1048]`, `line 54-56`) |
| **Opus** (`opus/dec.c`, `celt.c`, `silk.c`, `pvq.c`, `rc.c`) | IETF RFC 6716, RFC 8251 | **Float-only** (`FLTP`) in native `ff_opus_decoder` | Hybrid: `SilkContext` (`8/12/16 kHz` ARMA LP) + `CeltFrame` `AV_TX_FLOAT_MDCT` (`dec_celt.c:569`) | CELT `15 << (i+3)` = `{120, 240, 480, 960}` samples (`2.5..20 ms` @ `48 kHz`); embeds `SwrContext` (`dec.c:49, 117`) for SILK->`48 kHz` upsampling; `OpusDSP` postfilter |
| **Vorbis** (`vorbisdec.c`, `vorbisdsp.c`) | Xiph Vorbis I Spec | **Float-only** (`FLTP`) | `libavutil/tx` `AV_TX_FLOAT_MDCT` (`vorbisdec.c:1031-1036`) | Two power-of-two window sizes $2^{6..13}$ (`64..8192`, half-lengths `32..4096`); Floor 0 (LSP) / Floor 1, Residue 0/1/2 VQ, `vorbis_inverse_coupling` |
| **FLAC** (`flacdec.c`, `flacdsp.c`) | IETF RFC 9639 | **Bit-exact integer** (`S16`/`S32`, planar/packed) | Fixed polynomial (`order 0..4`) + autoregressive `FLACDSPContext::lpc{16,32,33}` (`order 1..32`) | Block sizes `16..65535`; Rice/Rice2 residual partitions; `33`-bit `int64_t` side-channel path (`flac_lpc_33_c`, `flacdsp.c:87-100`) for `32`-bit Mid/Left/Right-Side |
| **AC-3 / E-AC-3** (`ac3dec*.c`, `eac3dec.c`, `ac3dsp.c`) | ATSC A/52:2018 | **Yes:** `ac3` (`FLTP`) vs. `ac3_fixed` (`S32P`) | `libavutil/tx` `AV_TX_{FLOAT,INT32}_MDCT` (`ac3dec.c:114-117`) | `6` audio blocks/frame $\times$ `256` new samples (`512`-sample $\alpha=5$ KBD window; `2 x 128` short transforms); parametric exponent/bap bit allocation; `AC3DSPContext` |
| **PCM / Law** (`pcm.c`, `pcm_tablegen.h`) | ITU-T G.711, AES3, Blu-ray/DVD LPCM | **Bit-exact** integer/float | Stateless byte-swap, sign-extension, `256`-entry A-law/$\mu$-law LUTs, `20`/`24`-bit nibble unpacking | `AV_SAMPLE_FMT_{U8,S16,S32,S64,FLT,DBL}{,P}`; `BswapDSPContext` / vector shuffles |

#### Key Codec-Specific Architectural Seams and Hazards

1. **AAC Dual-Precision Template Split (`libavcodec/aac/aacdec_fixed.c:32-105`, `aacdec_float.c`):** FFmpeg compiles the shared `aacdec_dsp_template.c` and `aacdec_proc_template.c` twice: once with `USE_FIXED=0` (`float`, `AVFloatDSPContext`) and once with `USE_FIXED=1` (`int32_t` Q30/Q31, `AVFixedDSPContext`, `AV_SAMPLE_FMT_S32P`). Notably, USAC (`xHE-AAC`, `aacdec_usac.c`, `77.2 KB`) and MPEG Surround 2-1-2 (`aacdec_usac_mps212.c`) are wired into the floating-point pipeline and introduce non-power-of-two `768`- and `96`-sample transforms (`aacdec_fixed.c:50-51` reserves KBD buffers, while active USAC LPD/arithmetic decoding operates in float). Dequantization $x_i = \operatorname{sgn}(q_i) |q_i|^{4/3} \cdot 2^{\text{sf}/4}$ relies on precomputed `cbrt_tab` lookup tables (`ff_cbrt_tableinit_fixed`) bounded to `|q_i| <= 8191` by the AAC Huffman codebook maximum.
2. **MP3 Bit-Reservoir Backstep (`libavcodec/mpegaudiodec_template.c:54-95`):** Because ISO/IEC 11172-3 Layer III `main_data_begin` (`9` bits, `0..511` bytes) points *backward* into ancillary bytes of preceding frames, `MPADecodeContext` maintains `uint8_t last_buf[LAST_BUF_SIZE]` (`2 * 512 + 24 = 1048` bytes). Splicing `main_data_begin` bytes from `last_buf` with the new frame's payload before initializing `s->gb` is a classic stateful boundary hazard: if `last_buf_size < main_data_begin` (after stream seek or packet loss), the decoder must discard the granule cleanly rather than underflowing `last_buf`.
3. **Opus Bidirectional Range Coder and Embedded `SwrContext` (`libavcodec/opus/rc.c`, `dec.c:49-160`):**
   - Unlike FFV1's unidirectional `RangeCoder`, Opus's `OpusRangeCoder` (`opus/rc.h`) reads range-coded symbols forward from `buf[0]` (MSB-first) while simultaneously reading raw uniform bits *backward* from `buf[len - 1]` (LSB-first) toward the middle of the same packet slice. Termination/overread occurs smoothly when total forward + backward bits exceed `8 * len`, returning deterministic zero bits without out-of-bounds reads—a clean bidirectional cursor invariant (`fwd_ptr <= rev_ptr`) ideal for slice-safe Rust encoding.
   - As analyzed in `webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows`, standalone `libopus` upsamples `8/12/16 kHz` SILK speech frames to `48 kHz` for hybrid CELT overlap-add using RFC 6716 §4.2.7.9's dedicated fixed-point IIR+FIR resampler. By contrast, FFmpeg's `libavcodec/opus/dec.c:49, 72-81, 117` instantiates a general `libswresample` `SwrContext *swr` with bandwidth-indexed `silk_resample_filter_size = {8, 16, 16, 16, 16}` and feeds `silk_resample_delay = {4, 8, 11, 11, 11}` zero samples at stream start so `swr` introduces zero lookahead holdback. A clean-room rewrite must explicitly choose between (a) implementing RFC 6716 §4.2.7.9's self-contained ~150-line resampler (eliminating the `libavcodec -> libswresample` cyclic/upward dependency and matching `libopus` closely) or (b) matching FFmpeg's `SwrContext` coefficients if FATE float-epsilon parity against `ff_opus_decoder` is required.
4. **FLAC 33-Bit Side-Channel Widening (`libavcodec/flacdsp.c:45-112`, `flacdsp_lpc_template.c:31-40`):** Under RFC 9639, FLAC supports `4..32` bits per sample. When a `32`-bit stereo block uses Mid-Side, Left-Side, or Right-Side interchannel decorrelation, the difference channel $S = L - R$ spans `[-2^{32}, 2^{32}-1]`, requiring **33 signed bits**. FFmpeg therefore dispatches across three distinct LPC decoder tiers:
   - `flac_lpc_16_c` (`bps <= 16`, `int32_t` accumulator using `(SUINT)` unsigned multiplication `s0 += c * d` at `flacdsp.c:51-69` to avoid signed 32-bit overflow UB on corrupted residuals);
   - `flac_lpc_32_c` (`17 <= coding_bps <= 32`, `int64_t sum` accumulating up to `32` products of `15`-bit `coeffs[j]` and `32`-bit `decoded[j]`, bounded on valid streams by $32 \times 2^{14} \times 2^{31} = 2^{50} \ll 2^{63}-1$, `flacdsp.c:73-85`);
   - `flac_lpc_33_c` (`coding_bps == 33`, `int64_t *decoded` buffer, `flacdsp.c:87-99`), which computes `sum += (int64_t)coeffs[j] * (uint64_t)decoded[j]` and `decoded[j] = (uint64_t)residual[i] + (uint64_t)(sum >> qlevel)` so that even if a corrupted bitstream drives `decoded[j]` past `33` bits via unstable IIR feedback, C signed `int64_t` overflow UB cannot occur.

---

### 2. `libavutil/tx` FFT / MDCT / IMDCT Architecture and Cross-ISA Determinism

`Basis: source + execution + derived`

#### 2.1 Codelet Decomposition and Prime-Factor `15 x 2^k` Lowering

`libavutil/tx.h:39-134` and `libavutil/tx_priv.h:71-225` implement a FFTW-style runtime planner (`av_tx_init`, `tx.c:903`) over static `FFTXCodelet` descriptors parameterized across three scalar rings (`TX_FLOAT`, `TX_DOUBLE`, `TX_INT32`).

- **Half-length IMDCT reduction:** Unless `AV_TX_FULL_IMDCT` is passed, an inverse MDCT of `len` frequency bins (`window = 2 * len` time samples) outputs only the `len` non-redundant folded samples (`tx.h:64-67, 170-175`), executing pre-twiddle rotation of `len` reals into `len / 2` complex numbers (`ff_tx_mdct_gen_exp_float`), an in-place `len / 2` complex FFT subtransform (`ff_tx_init_subtx`, `x86/tx_float_init.c:153`, `aarch64/tx_float_init.c:148`), and post-twiddle rotation.
- **Split-radix and Good-Thomas PFA (`15 x M`):** Power-of-two lengths use split-radix parity bit-reversal (`ff_tx_gen_split_radix_parity_revtab`) down to base codelets `fft2`, `fft4`, `fft8`, `fft16`, and `fft32`. Crucially, Opus CELT (`len = 120, 240, 480, 960` $\implies$ complex FFT `len/2 = 60, 120, 240, 480 = 15 * 2^{2..5}`) and USAC/AAC (`len = 960, 768, 120, 96`) require non-power-of-two factor `3` and `5` transforms. Because $\gcd(3, 5) = 1$ and $\gcd(15, 2^k) = 1$, `x86/tx_float_init.c:172-230` and `aarch64/tx_float_init.c:88-123` construct a **Good-Thomas Prime-Factor Algorithm (`fft_pfa_15xM`)** via `ff_tx_gen_compound_mapping` and `TX_EMBED_INPUT_PFA_MAP(s->map, len, 3, 5)`. Unlike Cooley-Tukey mixed-radix FFT, Good-Thomas PFA requires **zero inter-stage twiddle multiplications** between the `M` inlined `15`-point transforms and the `15` calls to the $2^k$ split-radix subtransform, embedding the entire Chinese Remainder Theorem index bijection into `s->map[]` (`FF_TX_PRESHUFFLE`).
- **ABI divergence between `x86_64` and `aarch64` assembly:** On `x86_64`, `fft_pfa_15xM_avx2` and `mdct_inv_avx2` set `FF_TX_ASM_CALL` (`x86/tx_float_init.c:151, 186`), invoking `_asm`-suffixed subtransforms (`fft16_asm_fma3`, `fft_sr_asm_avx2`) under a custom non-System-V/non-Win64 register-preservation convention inside `tx_float.asm`. On `aarch64`, `aarch64/tx_float_init.c:89-90, 126-127` explicitly notes that standard AAPCS64 register conventions suffice (`blr` without `FF_TX_ASM_CALL`).
- **Complete SIMD coverage inventory at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`:** Inspecting the entire `libavutil/` directory tree confirms `tx` SIMD codelets exist **only** in `libavutil/x86/tx_float.asm` (`SSE2`, `SSE3`, `AVX`, `FMA3`, `AVX2`) and `libavutil/aarch64/tx_float_neon.S` (`NEON`). There are **zero** `AVX-512` codelets, **zero** `riscv64` RVV `tx` files (whereas `libavutil/riscv/` already implements `float_dsp_rvv.S` and `fixed_dsp_rvv.S`), and **zero** SIMD codelets on any architecture for `TX_INT32` (`AV_TX_INT32_MDCT` runs scalar `int64_t` `CMUL` in `tx_priv.h:115-124`, using unsigned `(unsigned)` casts in `BF` and `FOLD` at `lines 140-146` to avoid signed `int32_t` overflow UB).

#### 2.2 Fixed-Point vs. IEEE-754 Floating-Point Conformance and FMA Drift

As established in `ieee754-softfloat-dyadic-interval-gappa-certificates-and-nan-choice-refinement` and `ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`, IEEE-754 binary32 floating-point transforms fail cross-ISA bit-exactness whenever:
1. Target `A` (`x86_64` `FMA3`/`AVX2` `vfmadd*` or `aarch64` NEON `fmla`) evaluates complex butterflies with single-rounding fused multiply-add $\operatorname{rn}(a \cdot b + c)$ while target `B` (`x86_64` `SSE3`/`AVX` or scalar C with `-ffp-contract=off`) evaluates $\operatorname{rn}(\operatorname{rn}(a \cdot b) + c)$; or
2. SIMD lane blocking changes addition association trees compared to scalar split-radix butterflies.

**Empirical execution audit (`Basis: execution`):** Executing `probe_audio_sws.c` on `x86_64` across `N = 256` (AC-3 long block), `N = 960` (Opus CELT `20 ms` block), and `N = 1024` (AAC-LC long block) compares binary32 `noFMA`, binary32 hardware `fmaf`, and FFmpeg's exact Q31 `TX_INT32` rounding (`((int64_t)x * m + 0x40000000LL) >> 31`, `tx_priv.h:59, 120`) against a 64-bit `double` reference IMDCT, evaluated against ISO/IEC 11172-4's high-accuracy decoder conformance limit $\text{RMS}_{\text{error}} < 2^{-15}/\sqrt{12} \approx 8.809666 \times 10^{-6}$:

| Transform Size `N` (Codec Role) | `RMS(noFMA)` vs. `f64` | `RMS(FMA)` vs. `f64` | `RMS(Q31 int32)` vs. `f64` | ISO/IEC 11172-4 Full Limit | `FMA != noFMA` Sample Mismatch Rate (`max_diff`) |
| :--- | :---: | :---: | :---: | :---: | :--- |
| **`N = 256`** (AC-3 long block) | `9.074e-08` | `9.304e-08` | `6.819e-07` | `8.810e-06` | **`204 / 256` (`79.7%`)**, `max_diff = 2.384e-07` |
| **`N = 960`** (Opus CELT 20 ms) | `2.156e-07` | `2.029e-07` | `4.771e-06` | `8.810e-06` | **`858 / 960` (`89.4%`)**, `max_diff = 3.576e-07` |
| **`N = 1024`** (AAC-LC long block) | `2.257e-07` | `2.294e-07` | `5.304e-06` | `8.810e-06` | **`884 / 1024` (`86.3%`)**, `max_diff = 4.172e-07` |

**Verification synthesis (`Basis: derived`):** Over `80%` of floating-point IMDCT output samples differ at the binary32 ULP level between FMA and non-FMA targets (`~2..7` ULPs at unit full-scale, $\approx 4 \times 10^{-7}$, roughly `40x` smaller than a single `16`-bit PCM LSB $2^{-15} \approx 3.05 \times 10^{-5}$). Consequently, **verification of `AV_TX_FLOAT_MDCT` SIMD kernels against scalar float reference code CANNOT be phrased as bitwise equality (`a.to_bits() == b.to_bits()`)**; it must be proved as a **bounded dyadic/real-valued error-enclosure refinement** $|\hat{y}_n - y^{\mathbb{R}}_n| \le \varepsilon_N \ll 2^{-15}/\sqrt{12}$ (following the Gappa / interval methodology in `ieee754-softfloat-dyadic-interval-gappa-certificates-and-nan-choice-refinement`, supplemented by finite-input preconditions excluding `NaN`/`Inf` propagation from corrupted scale factors). Conversely, `AV_TX_INT32_MDCT` is **100% bit-exact across every ISA** and readymade for `AVX2`/`NEON`/`RVV` `vpmulhrsw`/`vqrdmulh`/`vwmul` vectorization with exact equivalence proofs.

---

### 3. `libswresample`: Polyphase FIR Overshoot, Dithering, and `41`-Channel Rematrixing

`Basis: source + execution + derived`

`libswresample` (`swresample.c`, `resample.c`, `resample_template.c`, `dither.c`, `rematrix.c`, `audioconvert.c`, plus optional `soxr_resample.c`) executes planar-internal conversion (`s16p`, `s32p`, `fltp`, `dblp`) across three DSP stages:

1. **Polyphase FIR Resampler (`resample.c:41-310`, `resample_template.c:30-219`):**
   - Builds a `(phase_count + 1) x filter_alloc` table (`filter_alloc = FFALIGN(filter_length, 8)`, `resample.c:244-255`, duplicating phase `0` shifted by `1` sample into row `phase_count` so `resample_linear` at `resample_template.c:175` can read `filter[i + c->filter_alloc]` in-bounds without wrapping branches).
   - Supports three window families (`resample.c:74-90`): Keys cubic (`d = -0.5`), 4-term Blackman-Nuttall, and Kaiser ($I_0(\beta\sqrt{1 - w^2})$), plus optional exact rational reduction (`exact_rational`, `lines 197-205`) when `out_rate / gcd(out_rate, in_rate) <= phase_count`.
   - **Boundary reflection & negative phase initialization:** `resample_init` initializes `c->index = -phase_count * ((c->filter_length - 1) / 2)` (`resample.c:268`). Before `resample_common` indexes `filter_bank + filter_alloc * index` (which requires `index >= 0`), `invert_initial_buffer` (`resample.c:457-502`) mirrors the first `filter_length` samples symmetrically into `in_buffer` while advancing `c->index += c->phase_count` until `c->index >= 0`, and `resample_flush` (`lines 437-454`) mirrors `(FFMIN(in_buffer_count, filter_length) + 1) / 2` trailing samples at stream EOF.
   - **Two subtle normalization artifacts (`resample.c:96-108`):** First, `if (!ph) norm += y;` computes `norm` exclusively on polyphase row `0` and divides all rows `ph > 0` by that constant `norm`, creating small polyphase DC gain ripple when `tap_count` is small. Second, in `AV_SAMPLE_FMT_S16P` (`scale = 32768`), when `factor == 1.0` and `ph == 0`, the center tap `32768` clips via `av_clip_int16(32768) -> 32767`, attenuating unity passthrough by `1 / 32768` (`-0.00026 dB`).
   - **Gibbs $\ell_1$ filter overshoot & signed accumulator overflow (`Basis: source + execution`):** Windowed sinc lowpass filters satisfy $\sum_k h_{p,k} \approx 1$, but negative sidelobes imply $\|h_p\|_1 = \sum_k |h_{p,k}| > 1$. Executing `probe_audio_sws.c` on `build_filter`'s exact equations for `48000 -> 44100 Hz` (`cutoff = 0.97`, `phase_count = 1024`) yields:

| Window Type | Base `filter_size` -> Actual `tap_count` | Max Row $\|h_p\|_1$ | Split Even / Odd $\|h_p\|_1$ | Adversarial `S16P` Single `int32_t` Sum (`INT32_MAX = 2,147,483,647`) | Split Even Tap `int32_t` Sum (`resample_template.c:117`) |
| :--- | :---: | :---: | :---: | :--- | :---: |
| **Cubic (`d = -0.5`)** | `16 -> 18` | `1.0050` | `0.4881` / `0.5307` | `1,079,099,310` (`50.2%` of `INT32_MAX`) | `524,059,061` |
| **Blackman-Nuttall** | `32 -> 36` | `1.9316` | `0.9652` / `1.2628` | `2,074,084,448` (`96.6%` of `INT32_MAX`) | `1,036,345,915` |
| **Kaiser ($\beta = 9$)** | `32 -> 36` | `1.9810` | `0.9897` / `1.2908` | `2,127,069,495` (`99.05%` of `INT32_MAX`) | `1,062,658,216` |
| **Kaiser ($\beta = 9$)** | `64 -> 72` | `2.2563` | `1.1271` / `1.4361` | **`2,422,697,878` (OVERFLOWS `INT32_MAX`)** | `1,210,243,037` |

   This quantitatively explains why `resample_template.c:113-126` splits `S16P` accumulation across `val` (even taps) and `val2` (odd taps) before widening to `int64_t` (`val + (FELEML)val2`), and why `resample_linear` (`line 28, 170`) uses unsigned `FELEM2U` (`uint32_t` for `S16`, `uint64_t` for `S32`)—and also proves that even the split `int32_t` odd accumulator in `resample_common` would overflow `INT32_MAX` if an extreme caller configuration pushed odd-tap $\|h_{\text{odd}}\|_1 \ge 2.0$ (`filter_size >= ~512`), whereas unconditionally accumulating `S16P` in `i64` (and `S32P` in `i128` or Q28 `i64`) eliminates the overflow boundary for all tap counts up to `INT32_MAX / 256` (`resample.c:235`).
2. **Dithering and Psychoacoustic Noise Shaping (`dither.c:27-125`, `noise_shaping_data.c`):** Generates deterministic LCG white noise (`seed = seed * 1664525 + 1013904223`, `dither.c:38`) shaped as rectangular PDF, triangular TPDF (`v1 - v2`), high-pass TPDF `(-tmp[i] + 2*tmp[i+1] - tmp[i+2]) / sqrt(6)` (`TMP_EXTRA = 2` tail allocation at `dither.c:29-30`), or sample-rate-matched IIR error-feedback noise shaping (`Lipshitz`, `F-weighted`, `modified-E-weighted`, `improved-E-weighted`, `Shibata`, `low/high Shibata`, matched within $\pm 5\%$ of `s->out_sample_rate` at `dither.c:118`).
3. **Channel Rematrixing (`rematrix.c:26-120`):** Supports up to `NUM_NAMED_CHANNELS = 41` spatial speakers (`FRONT_LEFT..BOTTOM_FRONT_RIGHT` including `22.2` surround) plus `AV_CHANNEL_ORDER_CUSTOM` maps, specializing inner loops across `S16` (with and without `TEMPLATE_CLIP`), `S32`, `FLT`, and `DBL` (`rematrix_template.c`).

---

### 4. `libswscale`: Dual-Generation Architecture, `SwsOp` IR, HDR CMS, and Buffer Bounds

`Basis: source + derived`

Inspection of `libswscale/` (`169` files, `3,454,403` bytes; `aarch64=24`, `x86=23`, `loongarch=17`, `ppc=10`, `arm=9`, `riscv=8`, `vulkan=5`) at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` reveals a pivotal architectural bifurcation controlled by `SwsBackend` (`swscale.h:110-129`, `utils.c:60-66`):

#### 4.1 Legacy `SWS_BACKEND_LEGACY` (`swscale.c`, `swscale_unscaled.c`, `utils.c`)

- **Unscaled fast paths (`swscale_unscaled.c:40-2743`):** Bypasses separable scaling when `(srcW, srcH) == (dstW, dstH)`, dispatching planar copies (`ff_copyPlane`), endian/bit-depth shifts with `8x8` ordered Bayer `dithers[8][8][8]` (`lines 40-113`), packed RGB shuffles (`rgb2rgb.c`), and fixed-matrix `yuv2rgb.c` converters.
- **Separable 14-bit fixed-point scaling (`hscale.c`, `vscale.c`, `utils.c:1757-1775`):** Precomputes horizontal and vertical `(filterPos, filter)` tables normalized to `1 << 14 = 16,384` (`utils.c:1765`) for `FAST_BILINEAR`, `BILINEAR`, `BICUBIC`, `X`, `POINT`, `AREA`, `BICUBLIN`, `GAUSS`, `SINC`, `LANCZOS`, and `SPLINE` (`swscale.h:95-108`), aligned to `filterAlign` (`4` on x86/NEON, `8` on AltiVec/LSX/LASX, `utils.c:1757-1761`). Like `libswresample`, bicubic/Lanczos/spline/sinc kernels have negative lobes whose `int16_t` weights sum in magnitude above `16,384`, requiring saturating unsigned pixel clips (`av_clip_uint8` / `av_clip_uintp2`) after vertical accumulation.
- **Runtime W^X JIT hazard in `SWS_FAST_BILINEAR` (`utils.c:1723-1754`, `jit.c:40-60`):** When `HAVE_MMXEXT_INLINE` and `SWS_FAST_BILINEAR` are active, `libswscale` calls `ff_sws_jit_alloc` (`mmap` with `PROT_READ | PROT_WRITE`), emits self-modified/specialized horizontal x86 machine code into `lumMmxextFilterCode` and `chrMmxextFilterCode` (`ff_init_hscaler_mmxext`), and transitions permissions via `ff_sws_jit_protect` (`mprotect(..., PROT_READ | PROT_EXEC)`). In hardened W^X environments (SELinux `execmem` denial, iOS, seccomp-bpf filters blocking `PROT_EXEC`, or verified Rust binaries forbidding runtime code synthesis), `mprotect` fails (`utils.c:1750-1752`) and aborts context initialization unless `SWS_FAST_BILINEAR` MMXEXT JIT is disabled.
- **Horizontal scaler tail-read hazard:** Legacy SIMD horizontal scalers load `4`–`16` source pixels starting at `filterPos[x]`, which near `x = dstW - 1` can read past `srcW * bpp` within the final row; callers supplying tightly packed unpadded image rows (rather than `AVFrame` buffers with `AV_INPUT_BUFFER_PADDING_SIZE` or aligned `linesize` slack) risk end-of-plane read faults on the bottom scanline unless the final pixels are peeled into a scalar tail loop.

#### 4.2 Modern `SwsGraph` + `SwsOp` Compiler + ITU-R BT.2100 HDR CMS (`graph.h`, `ops.h`, `uops.h`, `cms.h`)

The modern `SwsGraph` architecture (`graph.h:85-183`, copyright 2024–2025) replaces $O(F^2)$ format-pair C functions with a principled **three-tier image-processing compiler**:

1. **Multi-pass `SwsGraph` (`graph.h:85-182`):** Decomposes end-to-end conversion into slice-threaded `SwsPass` stages (`slice_h` granularity over `AVSliceThread`), tracking zero-copy `plane_copy[4]` pass-through planes (`graph.h:77, 151`) and optional `SwsLut3D` state (`line 171`).
2. **18-Operation Typed `SwsOp` IR & Exact `AVRational64` Optimizer (`ops.h:36-160`, `ops_optimizer.c`):** Represents any pixel format / colorspace / scaling pipeline as a sequence of `18` orthogonal ops: `SWS_OP_READ`, `WRITE`, `SWAP_BYTES`, `SWIZZLE`, `UNPACK`, `PACK`, `LSHIFT`, `RSHIFT`, `CLEAR`, `CONVERT`, `MIN`, `MAX`, `SCALE`, `LINEAR` (`4x5` affine matrix for YCbCr/RGB/LMS/ICtCp), `DITHER`, `FILTER_H`, `FILTER_V`, and `LUT_3D`. Constants, clamp bounds (`SwsClampOp`), and affine matrices are represented in exact `AVRational64` arithmetic so `ops_optimizer.c` (`1,250+` lines) algebraically fuses adjacent shifts, swizzles, scale factors, and linear matrices and tracks exact integer-valued component masks (`SWS_COMP_EXACT`, eliding redundant `SWS_OP_DITHER` at `ops_optimizer.c:626`) before lowering.
3. **4-Type `SwsPixel` `uops` Backend (`uops.h:40-90`, `x86/ops.c`, `aarch64/ops.c`):** Lowers optimized `SwsOpList` chains onto four canonical register lane types (`SWS_PIXEL_U8`, `U16`, `U32`, `F32`) dispatched via chained function pointers (`SWS_BACKEND_C`, `MEMCPY`, `X86`, `AARCH64`, or `SPIRV` Vulkan compute)—with **zero runtime machine-code generation (`mmap`/`mprotect`)**.
4. **ITU-R BT.2100 HDR Color Management (`cms.h:32-104`, `lut3d.h`, `csputils.h`):** Supports ITU-R BT.709, BT.2020, and BT.2100 PQ (SMPTE ST 2084) / HLG (ARIB STD-B67) transfer curves, gamut mapping, and static/dynamic perceptual tone mapping in IPT opponent space (`ff_sws_color_map_generate_static`, `ff_sws_color_map_generate_dynamic`, and `15`-bit `PT` chroma scaling `(1 << 15) - k + (PT * k >> 15)` in `ff_sws_tone_map_generate`, `cms.h:78-103`) evaluated via tetrahedral 3D LUT interpolation (`SWS_OP_LUT_3D`).

---

### 5. Verification Priority Stack and Clean-Rewrite Blueprint

`Basis: derived`

1. **Priority 1 — UB-freedom:**
   - Adopt `libswscale`'s `SwsGraph` / `SwsOp` algebraic architecture directly as the sole clean-room scaling/colorspace design, **eliminating `SWS_FAST_BILINEAR` runtime `mmap`/`mprotect` JIT (`jit.c`) completely** in favor of AOT SIMD vector kernels (`AVX2`/`AVX-512`, `NEON`, `RVV`) with safe scalar tail-pixel peeling on horizontal gather boundaries (eliminating bottom-row `filterPos` overreads on unpadded caller slices, including negative bottom-up `linesize` strides).
   - Express `AVFrame` planar (`ch[c][i]`) vs. packed (`data[i * ch + c]`) audio/video layouts as safe slice-per-plane views validated once at entry (`linesize.unsigned_abs() >= min_row_bytes`, non-aliasing `&mut [T]` output planes vs. `&[T]` input planes).
2. **Priority 2 — Panic-freedom:**
   - Widen `libswresample` fixed-point FIR inner products unconditionally (`S16P` single accumulator in `i64`; `S32P` Q30 accumulator in `i128`, eliminating the `int32_t` / `int64_t` Gibbs $\ell_1$ overflow cliff on steep Kaiser filters).
   - Retain FLAC's 3-tier bit-width discipline (`i32` for $\le 16$-bit, `i64` for $17..32$-bit, and `i64`/`i128` wrapping accumulation for `33`-bit Mid/Left/Right-Side `32`-bit stereo blocks) and enforce explicit `last_buf_size >= main_data_begin` bounds in MP3 bit-reservoir splicing.
3. **Priority 3 — Behavioral & SIMD-vs-scalar equivalence:**
   - **Integer/lossless pipelines (FLAC, PCM, `AV_TX_INT32_MDCT`, `S16P`/`S32P` resampler, exact integer `SwsOp` chains):** Prove **exact bitwise equivalence** between `x86_64`/`aarch64`/`riscv64` SIMD kernels and scalar Rust reference kernels. Adding missing `AVX2`/`NEON`/`RVV` SIMD for `AV_TX_INT32_MDCT` (`vpmulhrsw`/`vqrdmulh`) provides deterministic high-throughput fixed-point AAC/AC-3 decoding across all ISAs.
   - **Floating-point pipelines (`AV_TX_FLOAT_MDCT`, MP3 float, Opus CELT, Vorbis, `F32` `SwsOp` / `FLTP` resampler):** Separate (a) **same-FMA-contract SIMD-vs-scalar equivalence** (where scalar reference uses explicit `f32::mul_add` matching `FMA3`/`NEON`/`RVV` `vfmadd` and identical lane-blocked butterfly association trees, restoring bit-exactness across modern FMA-capable ISAs!) from (b) **cross-FMA / upstream FFmpeg differential FATE equivalence** verified within $\varepsilon_{\text{RMS}} \le 10^{-6}$ and $\varepsilon_{\max} \le 2 \times 10^{-5}$.
4. **Priority 4 — Full functional specification conformance:**
   - Certify floating-point and Q31 IMDCT/filterbank roundoff envelopes against ISO/IEC 11172-4 ($\text{RMS} < 2^{-15}/\sqrt{12}$), ISO/IEC 14496-4, ATSC A/52, and RFC 6716/8251 `opus_compare` thresholds; certify FLAC bit-exactness against RFC 9639 test vectors (including `32`-bit stereo `33`-bit LPC edge cases); and validate `SwsOp` `AVRational64` optimizer rewrite rules via mechanized algebraic equivalence over `{U8, U16, U32, F32}` semantics.

## Boundaries

- **Psychoacoustic audio encoders (`not examined` in depth):** `aacenc` (`libavcodec/aacenc*.c`), `opus/enc.c` (`enc_psy.c`), `flacenc.c`, `ac3enc.c`, and external `libmp3lame`/`libopus`/`libfdk-aac` wrappers involve rate-distortion loops, perceptual masking models, and non-normative heuristics outside this decoder, transform, resampler, and scaler kernel scope.
- **`SwsBackend` default activation status at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`known not to apply` by default without `SWS_UNSTABLE`):** Inspection of `libswscale/swscale.h:112-126` and `libswscale/utils.c:60-66` shows `SWS_BACKEND_STABLE` still aliases `SWS_BACKEND_LEGACY`, while `SWS_BACKEND_{C,MEMCPY,X86,AARCH64,SPIRV}` are gated under `SWS_BACKEND_UNSTABLE` while upstream completes format/filter parity.
- **External `libsoxr` resampler (`not examined` internally):** `libswresample/soxr_resample.c` is a thin optional FFI wrapper around external `libsoxr` FFT/polyphase resampling and is distinct from `libswresample`'s native `swri_resampler` (`resample.c`).
- **Vulkan `SWS_BACKEND_SPIRV` GPU execution (`not examined` via execution):** While `libswscale/vulkan/` (`5` files) and `SWS_BACKEND_SPIRV` (`swscale.h:120`) were identified in the source tree, Vulkan shader compilation and GPU numerical conformance were not executed in this capsule environment.

## Evidence

### Primary Repository Source Citations (`FFmpeg/FFmpeg` @ `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`)

- **Audio codec implementations and DSP interfaces:**
  - `libavcodec/codec_id.h:331-569` (`226` audio `AVCodecID` entries starting at `0x10000`); `libavcodec/allcodecs.c:425-721` (`216` first-party audio/PCM/DPCM/ADPCM decoders).
  - `libavcodec/aac/aacdec.c:1270-1300`, `libavcodec/aac/aacdec_fixed.c:32-105`, `libavcodec/aac/aacdec_float.c`, `libavcodec/aac/aacdec_usac.c`, `libavcodec/sbrdsp.h`, `libavcodec/aacpsdsp.h`.
  - `libavcodec/mpegaudiodec_template.c:54-190`, `libavcodec/mpegaudiodsp.h` (`BACKSTEP_SIZE = 512`, `GranuleDef`, `MPADecodeContext`, `synth_buf`, `imdct36`).
  - `libavcodec/opus/dec.c:49, 62-160`, `libavcodec/opus/dec_celt.c:569`, `libavcodec/opus/pvq.c`, `libavcodec/opus/rc.c`, `libavcodec/opus/silk.c` (`SwrContext *swr` SILK upsampler, `15 << (i+3)` CELT `AV_TX_FLOAT_MDCT`).
  - `libavcodec/vorbisdec.c:1030-1040`, `libavcodec/vorbisdsp.h`.
  - `libavcodec/flacdsp.c:45-120`, `libavcodec/flacdsp_lpc_template.c:31-141` (`flac_lpc_16_c`, `flac_lpc_32_c`, `flac_lpc_33_c`, `flac_wasted_33_c`).
  - `libavcodec/ac3dec.c:114-120`, `libavcodec/ac3dec_fixed.c`, `libavcodec/ac3dec_float.c`, `libavcodec/eac3dec.c`, `libavcodec/ac3dsp.h`, `libavcodec/pcm.c`.
- **`libavutil/tx` transform subsystem:**
  - `libavutil/tx.h:39-205`, `libavutil/tx_priv.h:28-220`, `libavutil/tx.c:903`, `libavutil/tx_template.c`, `libavutil/tx_int32.c`.
  - `libavutil/x86/tx_float_init.c:27-265` (`fft2..fft32`, `fft_sr`, `fft15`, `fft_pfa_15xM_avx2`, `mdct_inv_avx2`, `FF_TX_ASM_CALL`).
  - `libavutil/aarch64/tx_float_init.c:25-200` (`NEON` codelets, `fft15_permute_map`, `fft_pfa_init`, `mdct_inv_init` without `FF_TX_ASM_CALL`).
- **`libswresample` and `libswscale` subsystems:**
  - `libswresample/resample.c:41-513`, `libswresample/resample_template.c:28-219`, `libswresample/dither.c:27-125`, `libswresample/rematrix.c:26-120`.
  - `libswscale/swscale.h:100-165`, `libswscale/graph.h:39-190`, `libswscale/ops.h:36-160`, `libswscale/ops.c:74-93`, `libswscale/ops_optimizer.c:339-1250`, `libswscale/uops.h:40-120`, `libswscale/cms.h:32-105`, `libswscale/jit.c:38-100`, `libswscale/utils.c:60-66, 1710-1770`, `libswscale/swscale_unscaled.c:40-130`.

### Reproducible Execution Evidence (IMDCT FMA/Q31 Drift & `libswresample` $\ell_1$ Overflow Probe)

Observed on `2026-11-20` on Linux `x86_64` with `gcc (Debian 15.2.0-14) 15.2.0` (`gcc -O2 -mfma probe_audio_sws.c -lm`). The standalone probe evaluates (1) `N = 256, 960, 1024` IMDCT in binary32 `noFMA` (`volatile float` product preventing contraction), binary32 `fmaf`, and Q31 `((int64_t)x * c + 0x40000000LL) >> 31` (`libavutil/tx_priv.h:59`) against 64-bit `double`, and (2) `libswresample/resample.c:41-115` `build_filter` (`48000 -> 44100 Hz`, `cutoff = 0.97`, `phase_count = 1024`) worst-row $\ell_1$ norms and adversarial $\pm 32767/-32768$ `S16P` accumulator peaks:

```text
ISO/IEC 11172-4 full-compliance RMS limit: 8.809666e-06
IMDCT N= 256: RMS(noFMA)=9.074e-08 RMS(FMA)=9.304e-08 RMS(Q31)=6.819e-07 | FMA!=noFMA: 204/256 (79.7%) max_diff=2.384e-07
IMDCT N= 960: RMS(noFMA)=2.156e-07 RMS(FMA)=2.029e-07 RMS(Q31)=4.771e-06 | FMA!=noFMA: 858/960 (89.4%) max_diff=3.576e-07
IMDCT N=1024: RMS(noFMA)=2.257e-07 RMS(FMA)=2.294e-07 RMS(Q31)=5.304e-06 | FMA!=noFMA: 884/1024 (86.3%) max_diff=4.172e-07
SWR Cubic            taps=16->18: max_L1=1.0050 (even=0.4881 odd=0.5307) | S16 single_acc=1079099310 (<= INT32_MAX) even_acc=524059061
SWR Blackman-Nuttall taps=32->36: max_L1=1.9316 (even=0.9652 odd=1.2628) | S16 single_acc=2074084448 (<= INT32_MAX) even_acc=1036345915
SWR Kaiser-9         taps=32->36: max_L1=1.9810 (even=0.9897 odd=1.2908) | S16 single_acc=2127069495 (<= INT32_MAX) even_acc=1062658216
SWR Kaiser-9         taps=64->72: max_L1=2.2563 (even=1.1271 odd=1.4361) | S16 single_acc=2422697878 (OVERFLOWS INT32_MAX) even_acc=1210243037
```

## Revalidation

To revalidate the findings of this report against a newer `FFmpeg/FFmpeg` commit `<NEW_SHA>`:

1. **Check `libavutil/tx` SIMD backend expansion:**
    Query the repository tree under `libavutil/*/tx*` and `libavutil/tx_int32.c`. Check whether `riscv/tx*` (RVV), `x86` `AVX-512` codelets, or SIMD codelets for `AV_TX_INT32_*` have been added since `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`.
2. **Check `libswscale` backend graduation and `jit.c` removal:**
    Inspect `libswscale/swscale.h` (`enum SwsBackend`), `libswscale/utils.c` (`ff_sws_enabled_backends` and `ff_sws_jit_alloc`), and `libswscale/jit.c` to determine whether `SWS_BACKEND_{C,X86,AARCH64,SPIRV}` have graduated into `SWS_BACKEND_STABLE` and whether the legacy `SWS_FAST_BILINEAR` `mprotect` MMXEXT JIT has been retired.
3. **Check `opus/dec.c` `SwrContext` coupling and `flacdsp.c` `lpc33` invariants:**
    Diff `libavcodec/opus/dec.c` (presence of `#include "libswresample/swresample.h"` and `SwrContext *swr`) and `libavcodec/flacdsp.c` (`flac_lpc_33_c` `(uint64_t)` casts).
4. **Re-run `probe_audio_sws.c` if `libswresample/resample.c` or `resample_template.c` changes:**
    Diff `build_filter` (`resample.c`) and `resample_common`/`resample_linear` (`resample_template.c`) to verify whether per-row normalization (`if (!ph)` vs. all `ph`) or accumulator types (`FELEM2`, `FELEM2U`, `FELEML`) were modified.
