# FFmpeg First-Party Video and Audio Encoders: Complete Census, Rate-Distortion Architecture, UB/Panic Hazards, and Formal Verification Boundaries

## Summary

At upstream commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, `libavcodec/allcodecs.c` registers **273 `FFCodec` encoder descriptors**, which partition into four disjoint implementation regimes: **176 first-party CPU software encoders**, **3 first-party Vulkan GLSL compute-shader encoders** (`ffv1_vulkan`, `prores_ks_vulkan`, `apv_vulkan`), **54 platform/hardware API wrappers** (`nvenc`, `vaapi`, `qsv`, `amf`, `d3d12va`, `vulkan_encode`, `videotoolbox`, `mediacodec`, `v4l2m2m`, `mf`, `rkmpp`, `ohcodec`, `audiotoolbox`), and **40 external C/C++/Rust codec library wrappers** (`libx264`, `libx265`, `libvpx_vp8`, `libvpx_vp9`, `libaom_av1`, `libsvtav1`, `librav1e`, `libvvenc`, `libopus`, `libfdk_aac`, `libmp3lame`, etc.). Six structural findings govern clean-room engineering and formal verification across this encoder surface:

1. **Zero First-Party Software Encoders Exist for Modern Inter-Frame Delivery Video:** Upstream FFmpeg contains **no** first-party CPU software encoder for H.264/AVC, H.265/HEVC, VP8, VP9, AV1, or H.266/VVC. First-party software video encoding concentrates instead in lossless archival preservation (`ffv1`, `ffvhuff`, `huffyuv`, `magicyuv`, `utvideo`, `ljpeg`, `png`, `exr`), broadcast/post-production mezzanine intra codecs (`prores`/`prores_aw`, `prores_ks`, `dnxhd`, `dvvideo`, `cfhd`, `vc2`, `mjpeg`, `speedhq`), and **17 legacy `MPVMainEncContext` encoders** (`mpeg1video`, `mpeg2video`, `mpeg4`, `msmpeg4v2`, `msmpeg4v3`, `h261`, `h263`, `h263p`, `flv`, `rv10`, `rv20`, `wmv1`, `wmv2`, `mjpeg`, `amv`, `dnxhd`, `speedhq`) coupled to `libavcodec/mpegvideo_enc.c` (`4,707` lines).
2. **Asymmetric OSS-Fuzz Blind Spot Across Audio and Subtitle Encoders:** `tools/target_enc_fuzzer.c:105-106` executes `if (c->p.type != AVMEDIA_TYPE_VIDEO) return 0;` immediately before context allocation. Every non-video encoder in `libavcodec` (`flac`, `alac`, `wavpack`, `aac`, `opus`, `ac3`, `ac3_fixed`, `eac3`, `dca`, `mlp`, `truehd`, `vorbis`, PCM/ADPCM, and all 11 subtitle encoders) receives **zero** coverage from FFmpeg's generic `target_enc_%_fuzzer` target.
3. **Unchecked Bitstream/Range-Coder Output Pointers Shift Memory Safety Onto Worst-Case Size Bounds:** Neither `RangeCoder` (`libavcodec/rangecoder.h:62-77`, `renorm_encoder` raw `*c->bytestream++ = mask` writes without `bytestream_end` checks) nor `PutBitContext` (`libavcodec/put_bits.h:153-184, 207-251`, which drops 32/64-bit flushes with an `AV_LOG_ERROR` message when `buf_end - buf_ptr < sizeof(BitBuf)` in `NDEBUG` builds and then triggers a hard `av_assert0(s->buf_ptr < s->buf_end)` `abort()` inside `flush_put_bits`) dynamically grows output buffers. Memory and panic safety of every first-party encoder therefore reduce mathematically to proving that `ff_alloc_packet(avctx, pkt, maxsize)` upper-bounds the worst-case entropy expansion of any valid `AVFrame` (or triggers an explicit PCM/verbatim retry such as FFV1 v4 `slice_coding_mode = 1` at `ffv1enc.c:1915-1926` or ALAC `s->verbatim = 1` at `alacenc.c:610-611`).
4. **Vulkan Compute Encoders Introduce Device-Address Pointer Arithmetic Outside CPU Sandboxes:** `ffv1_vulkan` (`libavcodec/ffv1enc_vulkan.c`, `1,629` lines + `14` `.comp.glsl` shaders) and `prores_ks_vulkan` (`libavcodec/proresenc_kostya_vulkan.c`, `994` lines + `5` `.comp.glsl` shaders) bypass fixed-function `VK_KHR_video_encode_queue` hardware and execute full entropy coding in GLSL compute shaders via `GL_EXT_buffer_reference` raw 64-bit GPU physical storage buffer pointers (`u8buf bs = u8buf(slice_data + rc.bs_start)` in `vulkan/ffv1_enc.comp.glsl:585, 618`) and subgroup parallel CRC-32 reductions (`subgroupBroadcast`, `subgroupXor`, lines `649-655`).
5. **Encoder-Decoder State Lockstep Separates Normative Bit-Exact Paths From Heuristic Float Search:** Even within lossy codecs, critical inner sub-algorithms require bit-exact integer lockstep with the normative decoder—specifically `MPVEncContext`'s in-loop inverse quantizer + IDCT reconstruction (`mpv_reconstruct_mb`, `mpegvideo_enc.c:1148`, audited by `tools/enc_recon_frame_test.c`) and AC-3/E-AC-3's backward-adaptive masking/PSD bit-allocation pointer array (`s->ac3dsp.bit_alloc_calc_bap`, `ac3enc.c:1409-1413`), where a 1-LSB divergence desynchronizes mantissa bit widths across the entire frame without signaling. Conversely, psychoacoustic masking (`aacpsy.c`, `opus/enc_psy.c`) and rate-control (`ratecontrol.c`) execute IEEE-754 `float`/`double` heuristics that legitimately vary across FMA/SIMD targets.
6. **Sharp Formal Verification Dichotomy:** Lossless encoders (`ffv1`, `flac`, `alac`, `wavpack`, `png`, `exr`) admit a closed **left-inverse round-trip theorem** ($\forall F \in \mathcal{V},\; \mathrm{Decode}_{\mathrm{spec}}(\mathrm{Encode}(F)) = F$), whereas lossy encoders split into **machine-checkable syntactic/buffer/lockstep safety** ($\mathrm{Decode}_{\mathrm{spec}}(\mathrm{Encode}(F)) \neq \bot$, VBV/HRD non-underflow, `PutBitContext` bound adequacy) versus **empirical statistical conformance** (Bjontegaard Delta `BD-rate`, `PSNR`/`SSIM`/`VMAF`, `PEAQ`/`ODG`), which cannot and should not be phrased as bit-exact equivalence against FFmpeg's C float heuristics.

---

## Applicability

This report characterizes **`FFmpeg/FFmpeg`** (`libavcodec` SONAME `v63.28.100`) at exact commit **`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`** (`2026-11-20T01:06:10Z`), evaluated against seven normative codec specifications listed in `REPORT.json`:
- **IETF RFC 9043** (FFV1 v0, v1, and v3 lossless intra video, plus FFmpeg's experimental v4 float/remap extensions in `ffv1enc.c`);
- **SMPTE RDD 36:2015** (Apple ProRes `422 Proxy/LT/Standard/HQ` and `4444/4444 XQ` intra frame syntax);
- **SMPTE ST 2019-1:2016** (VC-3 / Avid DNxHD and DNxHR compression IDs and macroblock quantization);
- **IETF RFC 9639** (FLAC lossless audio coding, stereo decorrelation, 33-bit side-channel residuals, fixed/LPC predictors, and Rice partitions);
- **IETF RFC 6716** (Opus interactive audio codec—specifically contrasting normative hybrid SILK+CELT capability with FFmpeg's CELT-only native `opus` encoder);
- **ETSI TS 102 366 V1.4.1** (AC-3 and E-AC-3 MDCT, exponent strategies, and backward-adaptive `bap` bit allocation);
- **ISO/IEC 13818-7:2006** (MPEG-2/MPEG-4 AAC LC filterbank, scalefactor bands, TNS, M/S, Intensity Stereo, PNS, and Huffman codebooks).

**Scope and companion corpus links:**
- External codec wrappers (`libx264`, `libx265`, `libaom`, `libsvtav1`, `libopus`, `libfdk_aac`) and fixed-function hardware video encode APIs (`NVENC`, `VA-API`, `QSV`, `Vulkan Video` `VK_KHR_video_encode_queue`) are counted in the global registry partition (§1.1) to establish exact scope boundaries, while deep algorithmic analysis covers first-party CPU and Vulkan-compute encoders. For external library ABI trade-offs, hardware acceleration APIs, decoder-side architecture, and cross-ISA assembly dispatch, consult companion corpus reports `ffmpeg-codebase-architecture-cpuflags-dispatch-and-asm-corpus-census`, `ffmpeg-external-codec-and-crypto-library-ecosystem-replacement-vs-ffi-contracts`, `hardware-video-acceleration-apis-vaapi-nvdec-vulkan-video-videotoolbox-mediacodec`, `mpeg2-mpeg4-prores-mjpeg-png-and-legacy-video-codec-long-tail-architecture`, and `aac-mp3-opus-flac-ac3-audio-codecs-imdct-and-swresample-swscale-kernels`.

---

## Findings

### 1. Exhaustive Census of `libavcodec`'s 273 Encoders and Common Framing Infrastructure

**Basis:** source (`FFmpeg/FFmpeg` @ `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`: `libavcodec/allcodecs.c:1-960`, `configure`, `libavcodec/Makefile`, `libavcodec/vulkan/Makefile`, `libavcodec/encode.c:63-640`, `libavcodec/put_bits.h:37-285`, `tools/target_enc_fuzzer.c:83-228`).

#### 1.1 Exact Disjoint Partition of All 273 Registered `FFCodec` Encoders

Scanning every `extern const FFCodec ff_*_encoder;` declaration in `libavcodec/allcodecs.c` and cross-referencing `configure` (`*_encoder_deps` and transitive `*_encoder_select` graphs) yields an exact four-way partition summing to **273 encoders**:

| Implementation Regime | Count | Sub-Categories & Representative `FFCodec` Names | External / OS / GPU Dependencies |
| :--- | ---: | :--- | :--- |
| **1. First-Party CPU Software Encoders** | **176** | **Video & Still-Image (`88`):** `ffv1`, `prores`, `prores_aw`, `prores_ks`, `dnxhd`, `mjpeg`, `ljpeg`, `jpeg2000`, `jpegls`, `png`, `apng`, `exr`, `mpeg1video`, `mpeg2video`, `mpeg4`, `msmpeg4v2`, `msmpeg4v3`, `h261`, `h263`, `h263p`, `flv`, `rv10`, `rv20`, `wmv1`, `wmv2`, `dvvideo`, `cfhd`, `vc2`, `speedhq`, `utvideo`, `magicyuv`, `huffyuv`, `ffvhuff`, `qoi`, `tiff`, `webp`-free `bmp`/`dpx`/`targa`/`pam`/`ppm`/`sgi`, `snow`, `svq1`, `cinepak`, `roq`, `rpza`, `smc`, `qtrle`, `zmbv`, `flashsv`, `flashsv2`, `hap`, `v210`, `r210`, `rawvideo`, `wrapped_avframe` <br>**Compressed Audio (`28`):** `flac`, `alac`, `wavpack`, `tta`, `mlp`, `truehd`, `aac`, `opus`, `vorbis`, `ac3`, `ac3_fixed`, `eac3`, `dca`, `mp2`, `mp2fixed`, `aptx`, `aptx_hd`, `sbc`, `wmav1`, `wmav2`, `nellymoser`, `ra_144`, `g723_1`, `comfortnoise`, `s302m`, `dfpwm`, `dsd_msbf`, `hdr` <br>**PCM / DPCM / ADPCM (`47`):** `31` PCM (`pcm_s16le`..`pcm_f64be`, `pcm_alaw`, `pcm_mulaw`, `pcm_dvd`, `pcm_bluray`), `1` DPCM (`roq_dpcm`), `15` ADPCM (`adpcm_ima_*`, `adpcm_ms`, `adpcm_yamaha`, `adpcm_swf`, `g722`, `g726`, `g726le`) <br>**Subtitles & Null (`13`):** `ass`, `ssa`, `srt`, `subrip`, `webvtt`, `mov_text`, `ttml`, `dvbsub`, `dvdsub`, `xsub`, `text`, plus `vnull`, `anull` | `168` pure `libavutil`/`libavcodec` C+ASM; `7` select `zlib` (`png`, `apng`, `exr`, `flashsv`, `flashsv2`, `pdv`, `zlib`, `zmbv`—8 total with `exr`/`flashsv` direct `zlib` dep); `1` (`hap`) requires `libsnappy` for chunk framing after first-party `texturedspenc` DXT compression |
| **2. First-Party Vulkan Compute Encoders** | **3** | `ffv1_vulkan` (`14` GLSL `.comp` shaders), `prores_ks_vulkan` (`5` GLSL `.comp` shaders), `apv_vulkan` (`2` GLSL `.comp` shaders) | `vulkan`, `spirv_compiler` (`shaderc`/`glslang`), `vulkan_seg_gather` (not fixed-function silicon video blocks) |
| **3. Hardware / OS Codec API Wrappers** | **54** | `vaapi` (`8`), `mediacodec` (`6`), `v4l2m2m` (`6`), `qsv` (`6`), `mf` MediaFoundation (`6`), `audiotoolbox` `*_at` (`5`), `nvenc` (`3`), `amf` (`3`), `d3d12va` (`3`), `videotoolbox` (`3`), `vulkan_encode` `VK_KHR_video_encode_queue` (`3`: `h264_vulkan`, `hevc_vulkan`, `av1_vulkan`), `rkmpp` (`2`), OpenHarmony `*_oh` (`2`) — *note: counts reflect exact `allcodecs.c` entries* | Vendor drivers / OS frameworks (`libva`, CUDA/NVENC, Intel VPL/MFX, Vulkan 1.3/1.4 Video, Apple VT/AT, Android MediaCodec, V4L2 M2M) |
| **4. External Codec Library Wrappers** | **40** | **Video/Image (`26`):** `libx264`, `libx264rgb`, `libx265`, `libopenh264`, `libkvazaar`, `libvvenc`, `libxeve`, `libvpx_vp8`, `libvpx_vp9`, `libaom_av1`, `libsvtav1`, `librav1e`, `liboapv`, `libsvtjpegxs`, `libwebp`, `libwebp_anim`, `libjxl`, `libjxl_anim`, `libopenjpeg`, `libtheora`, `libx262`, `libxvid`, `libxavs`, `libxavs2`, `libastcenc` <br>**Audio (`14`):** `libopus`, `libfdk_aac`, `libfdk_xhe_aac`, `libmp3lame`, `libshine`, `libtwolame`, `libvorbis`, `libspeex`, `liblc3`, `libcodec2`, `libgsm`, `libgsm_ms`, `libilbc`, `libopencore_amrnb`, `libvo_amrwbenc` | Third-party C/C++/Rust shared or static libraries (`--enable-lib*`; GPLv2+ or `--enable-nonfree` for `libfdk_aac`) |

*(Note: `allcodecs.c` places `comfortnoise` at line `88` and `s302m` at line `301` inside the initial codec block prior to `/* audio codecs */` at line `425`, even though both have `.p.type = AVMEDIA_TYPE_AUDIO`; the table above classifies them by true `AVMediaType`, yielding `88` video/image + `28` non-PCM audio + `47` PCM/DPCM/ADPCM + `13` subtitle/null = `176` first-party CPU encoders).*

#### 1.2 Shared Dispatch (`encode.c`), `PutBitContext` Bounds Semantics, and Fuzzer Blind Spots

1. **Pull-driven state machine (`libavcodec/encode.c:346-640`):** Callers push `AVFrame`s via `avcodec_send_frame` (`encode.c:567`) and pull `AVPacket`s via `avcodec_receive_packet` (`encode.c:600`). Synchronous encoders implement `FF_CODEC_ENCODE_CB` (`cb.encode`), invoked by `encode_simple_internal` (`encode.c:346`); asynchronous/pipelined encoders (such as `ffv1_vulkan` and `prores_ks_vulkan`) implement `FF_CODEC_RECEIVE_PACKET_CB` (`cb.receive_packet`). For fixed-frame-size audio encoders without `AV_CODEC_CAP_VARIABLE_FRAME_SIZE`, `pad_last_frame` (`encode.c:158, 518`) allocates a zero-padded trailing `AVFrame` on EOF, whereas `AudioFrameQueue` (`afq` selected by `12` first-party audio encoders including `aac`, `ac3`, `eac3`, `opus`, `mlp`, `truehd`, `vorbis`) tracks exact input timestamps and trailing trim durations (`AV_PKT_DATA_SKIP_SAMPLES`).
2. **`PutBitContext` invariant and `NDEBUG` failure mode (`libavcodec/put_bits.h:37-285`):** On `ARCH_X86_64`, `BitBuf` is `uint64_t` (`BUF_BITS = 64`); on all other architectures (including `aarch64` and `riscv64`), `BitBuf` is `uint32_t` (`BUF_BITS = 32`). When `put_bits_no_assert` (`put_bits.h:207-251`) flushes a full `BitBuf`, it checks `if (s->buf_end - s->buf_ptr >= sizeof(BitBuf))` (`lines 219, 237`). If fewer than `sizeof(BitBuf)` bytes remain:
   - Under debug builds (`ASSERT_LEVEL >= 2`), `av_assert2(0)` (`lines 224, 242`) aborts.
   - Under release builds (`NDEBUG` / default `ASSERT_LEVEL == 0`), `put_bits_no_assert` logs `"Internal error, put_bits buffer too small"` and **silently drops the 4- or 8-byte write without advancing `s->buf_ptr`**, corrupting the output bitstream while continuing execution—until `flush_put_bits` (`put_bits.h:153-172`) executes `av_assert0(s->buf_ptr < s->buf_end)` (`line 160`), which is an **unconditional `abort()` in production builds** whenever `s->buf_ptr == s->buf_end`.
3. **OSS-Fuzz harness coverage limits (`tools/target_enc_fuzzer.c:83-228`):** `LLVMFuzzerTestOneInput` caps `maxpixels_per_frame = 512 * 512` (`line 84`) and `maxiteration = 8096` (`line 49`), parses 1,024 trailing fuzz bytes for `width`, `height`, `bit_rate`, `gop_size`, `max_b_frames`, `time_base`, `framerate`, `FF_COMPLIANCE_EXPERIMENTAL`, `av_force_cpu_flags(0)` differential toggling (`lines 145-146`), and `pix_fmt`, and special-cases dictionary options **only for `AV_CODEC_ID_FFV1`** (`coder`, `context`, `slicecrc` at `lines 159-165`). Because `lines 105-106` bail out on `c->p.type != AVMEDIA_TYPE_VIDEO`, **all 75 first-party audio/PCM/ADPCM encoders and 11 subtitle encoders are completely unexercised** by `target_enc_fuzzer.c`.

---

### 2. Lossless Archival FFV1: CPU Range/Golomb Coding, Slice CRCs, Float Remap, and Vulkan Compute Shaders

**Basis:** normative (`IETF RFC 9043` §§3–9) + source (`libavcodec/ffv1enc.c:50-2200`, `libavcodec/ffv1enc_template.c:1-265`, `libavcodec/ffv1.h`, `libavcodec/rangecoder.h:35-137`, `libavcodec/ffv1enc_vulkan.c:290-1629`, `libavcodec/vulkan/ffv1_enc.comp.glsl:37-690`).

#### 2.1 Predictor, Context Quantization, Range/Golomb Entropy Coding, and Slice CRCs

FFV1 (standardized for versions 0, 1, and 3 in RFC 9043, with experimental version 4 float/remap extensions in FFmpeg) is a strictly intra-coded (or GOP-state-persistent context-coded) lossless video format supporting 8- to 16-bit YUV/YUVA/GBR/GBRA/GRAY/Bayer and 16-/32-bit IEEE-754 floating-point planar formats (`ffv1enc.c:2172-2196`):
- **Spatial prediction and Reversible Color Transform (RCT):** Each plane predicts pixel $X$ from causal neighbors $L$ (left), $T$ (top), $TL$ (top-left), $TR$ (top-right), $LL$, and $TT$ using the median predictor $\hat{X} = \mathrm{median}(L, T, L + T - TL)$ (`ffv1.h`), reducing residuals modulo $2^{\text{bits}}$ (`int16_t` or `int32_t` wraparound when `use32bit == 1` for $\ge 16$-bit RGB, because the reversible transform $Y = \lfloor(R + 2G + B)/4\rfloor,\; Cb = B - G,\; Cr = R - G$ expands $b$-bit RGB channels to $(b+1)$-bit signed chroma differences!). In version $>3$, `choose_rct_params` (`ffv1enc.c:1195, 1826`) dynamically selects per-slice $(c_{by}, c_{ry})$ green/luma decorrelation weights, and `choose_rct_params_bayer` (`line 1293`) splits `AV_PIX_FMT_BAYER_RGGB16` into 4 sub-planes (`gr`, `gb`, `b`, `r`, `lines 1780-1795`).
- **Quantized gradient context states:** Five local differences $(L - TL, TL - T, T - TR, LL - L, TT - T)$ pass through configurable quantization tables (`qtable`: default, 8-bit, $>8$-bit, `ffv1enc.c:2131-2138`) to index context states (`context_count[i]` contexts per plane).
- **Dual entropy coders:**
  - **Binary Range Coder (`ac != AC_GOLOMB_RICE`, `rangecoder.h:35-105`):** Maintains `low` and `range` in $[2^{8}, 2^{16})$, splitting `range1 = (c->range * (*state)) >> 8` (`line 89`) and updating `*state` via Markov LUTs `zero_state[256]` / `one_state[256]` (`ff_build_rac_states` with `factor = 0.05 * 2^32`, `ffv1enc.c:2027`, or custom 2-pass state transitions `AC_RANGE_CUSTOM_TAB`, `lines 2041-2046`). Signed/unsigned integers are binarized via exponent + mantissa contexts in `put_symbol_inline` (`ffv1enc.c:198`).
  - **Adaptive Golomb-Rice Coder (`AC_GOLOMB_RICE`):** Terminates the slice header's range coder (`ff_rac_terminate`), initializes a `PutBitContext` (`ffv1enc.c:1876-1881`), and codes residuals using run-mode + adaptive Golomb parameter $k = \lceil \log_2(\text{error\_sum}/\text{count}) \rceil$ with bias/drift centering (`VlcState`).
- **Float16/Float32 monotone LUT remapping (`ffv1enc.c:1360-1575`):** IEEE-754 half/single floats have sparse, non-uniform bit patterns across adjacent exposures. FFV1 v4 scans present slice values (`load_plane` / `load_rgb_float32_frame`), optionally XOR-flips negative sign-magnitude floats by `0x7FFF` (`flipdualrle`, `line 1363`) so bit order matches numerical order, encodes the active-value compacting map via dual RLE or piecewise multiplier segments (`encode_histogram_remap` for $\le 16$-bit, `encode_float32_remap` using `152 KiB` heap-allocated `remap_buf` per slice for 32-bit, `lines 50-51, 1101`), and Losslessly encodes dense integer indices.
- **Slice parallelism, PCM fallback, and CRC-32 protection (`ffv1enc.c:1915-2083`):** Each frame is partitioned into `slice_count = num_h_slices * num_v_slices <= MAX_SLICES` (`256` or `1024`) independent slices executed concurrently via `avctx->execute(avctx, encode_slice, ...)` (`line 2061`). Slice $i$ receives `len = pkt->size / f->slice_count` bytes (`line 2052`).
  - **Critical memory-safety hazard:** `renorm_encoder` (`rangecoder.h:62-77`) performs **unbounded raw pointer stores** (`*c->bytestream = ...; *c->bytestream++ = mask;`) with no check against `c->bytestream_end`. Safety relies entirely on `ff_ffv1_encode_buffer_size` (`ffv1enc.c:1931-1953`) allocating enough headroom—**except** at `lines 2014-2021`, where if `maxsize > INT_MAX - AV_INPUT_BUFFER_PADDING_SIZE - 32` (reachable on ultra-high-resolution 16-/32-bit multi-plane frames), FFV1 logs a warning (`"Cannot allocate worst case packet size, the encoding could fail"`), clamps `maxsize` to `~2 GiB`, and proceeds! On incompressible high-entropy inputs exceeding the clamped slice slice-share, `encode_line` checks remaining range-coder margin and returns `< 0`: in FFV1 `version >= 4`, `encode_slice` (`lines 1915-1926`) resets `sc->c = c_bak` and re-encodes the slice uncompressed (`sc->slice_coding_mode = 1`); in `version <= 3`, incompressible overruns fail with `"Buffer too small"` (`line 1918`)—and any miscalculated line-margin check before `renorm_encoder` causes heap corruption.
  - **Slice trailer and IEEE CRC-32 (`lines 2068-2082`):** After `memmove` compacting slices contiguously, FFV1 writes the 24-bit big-endian slice byte length (`AV_WB24`) and, when `ec` (`slicecrc`) is enabled, appends 1 error-status zero byte plus a 32-bit little-endian CRC (`AV_CRC_32_IEEE` initialized with `f->crcref` and finalized with `^ 0x8CD88196` when `crcref != 0`, matching RFC 9043 §4.1.2).

#### 2.2 `ffv1_vulkan`: GPU Compute-Shader Entropy Coding and Physical Storage Buffer Hazards

`libavcodec/ffv1enc_vulkan.c` (`1,629` lines) and its `14` GLSL compute shaders (`libavcodec/vulkan/ffv1_enc*.comp.glsl`) implement complete FFV1 v3/v4 encoding on Vulkan GPUs:
- **Multi-pass dispatch pipeline:** Per frame in an `async_depth`-deep execution pool (`ff_vk_exec_pool_init`, `line 1337`), `ffv1enc_vulkan.c` dispatches compute shaders for RCT parameter search (`ffv1_enc_rct_search`), float/integer value sorting and remap construction (`ffv1_enc_remap`, `ffv1_enc_sort32`), slice range-coder setup (`ffv1_enc_setup`, `line 537`), context state reset (`ffv1_enc_reset` / `ffv1_enc_reset_golomb`, `line 590`), and per-slice entropy encoding (`ffv1_enc` / `ffv1_enc_rgb` / `ffv1_enc_bayer` / `*_golomb`, `line 714`), followed by `vulkan_seg_gather` device-to-host compaction into `compacted_buf` (`line 766`).
- **Subgroup-parallel CRC-32 (`vulkan/ffv1_enc.comp.glsl:624-658`):** Rather than computing CRC-32 serially on one GPU thread, `ffv1_enc.comp.glsl` loads the 256-entry IEEE CRC table into `shared uint crc_tab[256]` (`line 65`), computes strided partial CRCs per subgroup lane, and combines them via Galois-field fold tables and `subgroupBroadcast` / `subgroupXor` (`lines 649-655`).
- **Device-memory UB boundary:** `ffv1_enc.comp.glsl` uses `GL_EXT_buffer_reference` raw 64-bit GPU virtual addresses (`u8buf bs = u8buf(slice_data + rc.bs_start)`, `lines 585, 618`) to write compressed bytes directly into `out_data_buf` (`maxsize` per frame, `2 * maxsize * async_depth` VRAM footprint, `ffv1enc_vulkan.c:1334`). Without `VK_EXT_robustness2` page-fault isolation, any shader arithmetic bug in `rc.bs_start` or slice overrun writes out-of-bounds in GPU physical buffer space, corrupting adjacent slices or triggering `VK_ERROR_DEVICE_LOST`.

---

### 3. Mezzanine and Still-Image Intra Encoders (`prores_aw`, `prores_ks`, `dnxhd`, `mjpeg`, `png`, `exr`)

**Basis:** normative (`SMPTE RDD 36:2015`, `SMPTE ST 2019-1:2016`, `ITU-T T.81`, `W3C PNG`) + source (`proresenc_anatoliy.c`, `proresenc_kostya.c`, `proresenc_kostya_vulkan.c`, `dnxhdenc.c`, `mjpegenc.c`, `mjpegenc_common.c`, `pngenc.c`, `exrenc.c`).

| Encoder (`FFCodec`) | Source & Lines | Transform & Predictor | Rate Control & Quantization Search | Entropy Coding & Framing | Key Hazard / Clean-Room Seam |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`prores` / `prores_aw`** | `proresenc_anatoliy.c` (`950L`) | 10-bit `8x8` FDCT (`FDCTDSPContext.fdct`, `L297, 875`); `subimage_with_fill` edge clamping (`L447`) | Fast greedy heuristic quantizer search (`qp` step search per `8`-MB slice, `DEFAULT_SLICE_MB_WIDTH = 8`, `L43`) | Differential DC + hybrid Rice/Exp-Golomb run-level AC (`encode_slice_plane`, `L337`); optional 16-bit planar alpha (`4444`) | `FDCTDSPContext` requires 10-bit input range $[4, 1019]$ (`faandct` / x86 AVX2 / AArch64 NEON); slice size table `uint16_t` caps each slice at `65,535` bytes |
| **`prores_ks` + `prores_ks_vulkan`** | `proresenc_kostya.c` (`1,047L`); `*_vulkan.c` (`994L`) | 10-/12-bit `8x8` FDCT + RLE alpha (`encode_alpha_plane`, `L289`) + interlaced field DCT | Dynamic-programming **Viterbi trellis** across slice quantizers (`TRELLIS_WIDTH`, `L621-721`; GPU `prores_ks_trellis_node.comp.glsl`) + `overquant` fallback (`L689`) | Same SMPTE RDD 36 bitstream as `prores_aw`, adding `4444 XQ` and alpha quantization | Two separate CPU ProRes codebases exist purely for speed (`prores_aw`) vs trellis quality (`prores_ks`)—unifiable into one parameterized clean-room encoder |
| **`dnxhd`** | `dnxhdenc.c` (`1,369L`) | Embeds `MPVEncContext m` (`dnxhdenc.h`); 8-bit & 10-bit symmetric `8x4` pixel fetch + `8x8` FDCT (`dnxhd_10bit_dct_quantize`, `L178`) | Exact CBR frame-byte target (`cid_table->frame_size`) via `dnxhd_find_qscale` (`L1072`) + **4-pass 8-bit bucket `radix_sort`** (`L1138-1179`) upgrading MB `qscale`s in steepest bits/distortion order | SMPTE ST 2019-1 VLC tables (`ac_codes`, `dc_codes`, `run_codes`) + big-endian MSBs per MB slice offset table | Unnecessarily couples intra-only VC-3 encoding to `MPVEncContext` (`mpegvideoenc` dependency in `configure`); clean rewrite should sever `MPVEncContext` completely |
| **`mjpeg`** | `mjpegenc.c` (`730L`), `mjpegenc_common.c` (`583L`) | `MPVEncContext` `8x8` FDCT + zig-zag scan (`ff_zigzag_direct`) | Fixed `qscale` / `lmin`–`lmax` matrix scaling; 1-pass default Annex K tables or **2-pass buffered optimal Huffman** (`HUFFMAN_TABLE_OPTIMAL`, `mjpegenc.c:177-275`, default ON `L648`) | ITU-T T.81 DC DPCM + AC `(run, size)` Huffman + **`ff_mjpeg_escape_FF`** (`0xFF -> 0xFF 0x00` byte stuffing, `mjpegenc_common.c:464`) | `ff_mjpeg_escape_FF` scans and shifts already-written bytes *in place* inside `PutBitContext` buffer, doubling worst-case packet allocation (`2x` byte expansion if every byte is `0xFF`) |
| **`png` / `apng`** | `pngenc.c` (`1,331L`) | W3C PNG 5 scanline predictors (`None`, `Sub`, `Up`, `Avg`, `Paeth` via `LLVidEncDSPContext`, `L175`) | Lossless min-sum-of-abs-diffs row filter heuristic (`png_choose_filter`, `L206`); APNG bounding-box diff (`ACTL`/`FCTL`/`FDAT`) | `deflateBound` (`L633, 685`) + `zlib` `deflate(..., Z_NO_FLUSH / Z_FINISH)` (`L293, 368`) into `IDAT`/`fdAT` chunks with IEEE CRC-32 | Relies on external C `zlib` (`deflate_wrapper`); clean-room Rust replaces `zlib` with memory-safe verified DEFLATE while preserving exact `Paeth(a,b,c)` modular `u8` arithmetic |
| **`exr`** | `exrenc.c` (`559L`) | Channel planarization (`ABGR`/`BGR` alphabetical EXR channel order) + even/odd byte split (`reorder_pixels`, `L158`) + `+0x80`-biased delta `predictor` (`L170`) | Lossless (`NONE`, `RLE`, `ZIPS` 1-line, `ZIP` 16-line) for `EXR_HALF` (`fp16`) and `EXR_FLOAT` (`fp32`) | RLE or `zlib` `compress()`; falls back to uncompressed scanline block if `actual_size >= tmp_size` via `FFSWAP` (`L270, 341`) | At `exrenc.c:271, 342`, `FFSWAP(int, scanline->uncompressed_size, scanline->compressed_size)` swaps `unsigned int` fields through a signed `int` temporary |

---

### 4. Legacy `MPVMainEncContext` Inter-Frame Encoders, `motion_est.c` Bounds, and `ratecontrol.c`

**Basis:** source (`libavcodec/mpegvideo_enc.c:86-4707`, `libavcodec/mpegvideoenc.h`, `libavcodec/mpeg12enc.c`, `libavcodec/mpeg4videoenc.c`, `libavcodec/motion_est.c:545-1746`, `libavcodec/motion_est_template.c:50-1048`, `libavcodec/ratecontrol.c:167-1092`, `tools/enc_recon_frame_test.c:46-135`).

#### 4.1 Monolithic `MPVMainEncContext` Coupling and Reconstructed-Frame Lockstep

Transitive `configure` dependency resolution confirms that **17 encoders** link `mpegvideo_enc.c`: 13 true inter-frame codecs (`mpeg1video`, `mpeg2video`, `mpeg4`, `msmpeg4v2`, `msmpeg4v3`, `h261`, `h263`, `h263p`, `flv`, `rv10`, `rv20`, `wmv1`, `wmv2`) plus 4 intra-only codecs (`dnxhd`, `mjpeg`, `amv`, `speedhq`). `MPVMainEncContext` (`mpegvideoenc.h`) manages GOP/B-frame lookahead (`estimate_best_b_count`, `mpegvideo_enc.c:1497`) and spawns slice worker contexts `s->c.enc_contexts[]` via `avctx->execute(..., encode_thread, ...)` (`line 3924`).

**In-loop decoder equivalence invariant (`mpv_reconstruct_mb`, `mpegvideo_enc.c:1148, 2748, 3433`):** Every P- or B-referenced macroblock encoded by `s->dct_quantize` (`dct_quantize_c` or `dct_quantize_trellis_c`, `lines 300-307`, plus x86/AArch64 SIMD overrides) immediately undergoes inverse quantization (`dct_unquantize_mpeg1_intra/inter`, `mpeg2`, `h263`, `mpeg4`) and `IDCTDSPContext.idct` inside the encoder to populate reference planes. `tools/enc_recon_frame_test.c:68-130` tests `AV_CODEC_FLAG_RECON_FRAME` by asserting that Adler-32 plane checksums of exported encoder reconstructed frames match a fresh `AVCodecContext` decoder instance bit-for-bit (`SWS_BITEXACT`). Note that legacy MPEG-1/2/4 specs (`IEEE 1180-1990` / `ISO/IEC 23002-1`) permitted slight integer IDCT rounding variance across implementations, causing progressive P-frame drift unless encoder and decoder share matched IDCT kernels (`FF_IDCT_SIMPLE` / `SIMPLEAUTO`).

#### 4.2 Motion Estimation Spatial Bounds (`motion_est.c` & `motion_est_template.c`)

`ff_estimate_p_frame_motion` (`motion_est.c:888`) and `ff_estimate_b_frame_motion` (`line 1488`) execute Enhanced Predictive Zonal Search (`epzs_motion_search_internal`, `motion_est_template.c:860`), checking median/spatial/temporal predictors `P[10][2]` followed by `small_diamond_search` (`line 416`) or `sab_diamond_search` (`line 681`), `hpel_motion_search` (`line 50`), and `qpel_motion_search` (`line 207`) using `MECmpContext` (`pix_abs`, `sad`, `sse`, `vsad`, `hadamard8_diff`, `dct_sad` SIMD kernels).
- **Pointer-safety invariant (`get_limits`, `motion_est.c:545-579`):** `MECmpContext` assembly kernels take raw `const uint8_t *pix2 = ref_base + (y + mv_y) * stride + (x + mv_x)` pointers with zero internal bounds checks. `get_limits` establishes `(c->xmin, c->xmax, c->ymin, c->ymax)`:
  - Standard restricted MV mode (`lines 566-569`): `xmin = -x`, `ymin = -y`, `xmax = -x + mb_width * 16 - 16`, `ymax = -y + mb_height * 16 - 16` (clamped inside allocated macroblock-aligned frame dimensions).
  - Unrestricted MV mode (`c->unrestricted_mv`, e.g., H.263+/MPEG-4 with `UMV`, `lines 554-558`): `xmin = -x - 16`, `ymin = -y - 16`, `xmax = -x + width`, `ymax = -y + height`. This accesses **up to 16 pixels outside `[0, width) x [0, height)`** on all four borders! Memory safety holds **if and only if** `ff_mpv_frame_start` pads reference buffers by `EDGE_WIDTH = 16` pixels on all sides (`VideoDSPContext.emulated_edge_mc` / `AVFrame` edge allocation) **and** `safety_clipping` (`motion_est.c:603, 615`) clips `mv4` 8x8 sub-blocks when `width` or `height` is not a multiple of 16.

#### 4.3 `ratecontrol.c`: Runtime Expression Parsing and Float Non-Determinism

`ff_rate_control_init` (`ratecontrol.c:496`) and `ff_rate_estimate_qscale` (`line 927`) compute per-picture quantizers using `libavutil/eval.h` (`av_expr_parse_and_eval`) on user-configurable `rc_eq` strings (default `"tex^qComp"`), Gaussian-blurred 2-pass complexity curves (`blurred_qscale`), and Video Buffering Verifier (`ff_vbv_update`, `line 730`) clamping via `modify_qscale` (`line 167`). Because `ratecontrol.c` mixes `double` transcendentals (`pow`, `exp`, `log`) with `float` casts (`av_clipf`, `line 538`), qscale decisions near VBV boundaries are not bit-identical across x87, non-FMA SSE2, and FMA3/AArch64 builds unless IEEE-754 rounding and libm implementations match.

---

### 5. Lossless Audio Encoders (`flac`, `alac`, `wavpack`) and Exact Fixed-Point Overflow Proofs

**Basis:** normative (`IETF RFC 9639` §§8–9) + source (`libavcodec/flacenc.c:270-1771`, `libavcodec/lpc.c:133-370`, `libavcodec/flacencdsp.c`, `libavcodec/alacenc.c:68-651`, `libavcodec/wavpackenc.c:129-2990`) + execution (standalone `-fsanitize=undefined` C verification probe, §Evidence).

#### 5.1 FLAC (`flacenc.c` + `lpc.c`): 33-Bit Side-Channel Residuals, Cholesky/Levinson LPC, and Rice DP

FFmpeg's `flac` encoder supports 1–8 channels and up to 32-bit PCM (`AV_SAMPLE_FMT_S16` / `S32`), running uncompressed PCM bytes through `av_md5_update` (`flacenc.c:435, 1618, 1635`) to populate the 128-bit STREAMINFO MD5 digest:
1. **Mid-Side stereo widening to 33 bits (`obits == 33`):** On 32-bit stereo inputs (`smp[k] in [-2^31, 2^31 - 1]`), stereo decorrelation (`left-side`, `right-side`, `mid-side`, RFC 9639 §8.2.2) forms `side = left - right` in `$[-2^{32} + 1, 2^{32} - 1]$`, requiring **33 signed bits** (`int64_t *smp_33bps`, `flacenc.c:967, 977`). Applying the 4th-order fixed binomial predictor $r_t = s_t - 4s_{t-1} + 6s_{t-2} - 4s_{t-3} + s_{t-4}$ (`line 872`) on alternating full-scale 33-bit samples expands magnitude by $16\times$ to **`68,719,476,720`** ($32.00\times \text{INT32\_MAX}$, requiring **37 signed bits**). Because RFC 9639 Rice residuals must fit in `(INT32_MIN, INT32_MAX]` (`INT32_MIN` itself is forbidden because unsigned zig-zag/Rice folding overflows `uint32_t`, checked explicitly at `line 845`: `if (smp[i] == INT32_MIN) return 1;`), `encode_residual_fixed_with_residual_limit[_33bps]` (`lines 839-892`) evaluates residuals in `int64_t`, rejects orders exceeding `(INT32_MIN, INT32_MAX]`, and falls back to `FLAC_SUBFRAME_VERBATIM` (`lines 1027-1031`). *(Minor upstream quirk at `flacenc.c:1037`: when recomputing `sub->order != max_order`, the guard reads `else if (sub->obits + i >= 32)` using the post-loop variable `i == max_order + 1` instead of `sub->order`; because `max_order + 1 > sub->order`, this typo is conservative and safe rather than unsound.)*
2. **Autocorrelation/Levinson-Durbin vs. Multi-Pass Cholesky LLS LPC (`lpc.c:133-340`):** For `FLAC_SUBFRAME_LPC` (orders `1..32`), `ff_lpc_calc_coefs` computes Welch-windowed autocorrelations (`lpc_compute_autocorr` SIMD in `x86/lpc.asm` and `riscv/lpc_rvv.S`) solved via Schur/Levinson-Durbin recursion (`FF_LPC_TYPE_LEVINSON`, `line 272`) or Weighted Linear Least Squares Cholesky decomposition (`FF_LPC_TYPE_CHOLESKY`, `avpriv_solve_lls`, `lines 280-323`). `quantize_lpc_coefs` (`lines 133-181`) error-feedback-quantizes float coefficients to `[-qmax, +qmax]` where `qmax = (1 << (precision - 1)) - 1` and clamps `shift` to `[0, 15]` (negative shifts are forbidden by RFC 9639 §9.2.5, `lines 164-171`).
3. **Exact verification of `lpc_encode_choose_datapath` (`flacenc.c:923-948`):**
   - `flacenc.c:942` dispatches 32-bit accumulator SIMD (`lpc16_encode`) iff `bps + prec + av_log2(order) <= 32`, otherwise 64-bit accumulator SIMD (`lpc32_encode`).
   - **Algebraic proof & exhaustive execution check:** Since $\text{order} \le 2^{\lfloor\log_2(\text{order})\rfloor + 1} - 1$, $|s_k| \le 2^{\text{bps}-1}$, and $|c_j| \le 2^{\text{prec}-1} - 1$, the maximum unshifted inner product plus sample satisfies:
     $$|p| + |s_i| \le (2^{k+1}-1)(2^{\text{prec}-1}-1)2^{\text{bps}-1} + 2^{\text{bps}-1} < 2^{\text{bps}+\text{prec}+k-1} \le 2^{31} - 1 = \mathrm{INT32\_MAX}$$
     whenever $\text{bps} + \text{prec} + k \le 32$. Exhaustive execution over all `7,742` valid `(bps in 4..32, prec in 2..15, order in 1..32)` triples passing line `942` confirms **zero** 32-bit accumulator or `shift == 0` residual overflows.
   - Conversely, among the `5,250` triples routed to `lpc32_encode` (`int64_t p`, `int32_t *res`), **`3,464` triples (`66.0%`)** can overflow `int32_t res[i]` even at `shift = 4`! That narrowing UB is prevented **only** by the preceding worst-case `uint64_t max_residual_value > INT32_MAX` guard at `lines 928-941`, which routes hazardous coefficient vectors into checked `lpc_encode_with_residual_limit` (`lines 894-921`) and falls back to lower orders or `VERBATIM`.
4. **Optimal Rice partition dynamic programming (`flacenc.c:717-785`):** `calc_rice_params` precomputes unsigned zig-zag residual sums across $2^{\text{pmax}}$ blocks and merges adjacent partitions bottom-up from `pmax` down to `pmin`, choosing exact 4-bit (`RICE`) or 5-bit (`RICE2`) Rice parameters $k \in [0, 30]$.

#### 5.2 ALAC (`alacenc.c`) and WavPack (`wavpackenc.c`)

- **ALAC (`alacenc.c`, `651` lines):** Supports 16- and 24-bit PCM (`MAX_CHANNELS = 8`), using fixed order-4/6 or Levinson-Durbin FIR prediction (`alac_linear_predictor`, `line 259`) and adaptive modified Rice-Golomb coding (`alac_entropy_coder`, `line 323`). If the encoded frame reaches the uncompressed byte budget (`put_bits_count` check at `lines 608-612`), ALAC discards the bitstream, sets `s->verbatim = 1`, and re-emits raw interleaved PCM samples—guaranteeing strictly bounded packet size.
- **WavPack (`wavpackenc.c`, `2,990` lines):** Uniquely supports **lossless IEEE-754 32-bit float (`AV_SAMPLE_FMT_FLT`/`FLTP`)** as well as 8/16/24/32-bit integer PCM. `scan_int32` (`line 435`) strips trailing zero/ones-complement redundant LSBs/MSBs; `scan_float` (`line 268`) separates float sign, exponent, mantissa MSBs (fed as pseudo-integers through up to 16 reversible cascading stereo decorrelation passes in `decorr_stereo`, `line 1129`, plus adaptive median Rice coding), and emits denormals, NaNs, negative zeros, and shifted LSBs into a separate `WVP` `wv_extra` correction bit-stream—achieving bit-exact IEEE-754 payload preservation including quiet/signaling NaN payloads.

---

### 6. Lossy Psychoacoustic Audio Encoders (`aac`, `opus`, `ac3` / `ac3_fixed` / `eac3`)

**Basis:** normative (`ISO/IEC 13818-7:2006`, `IETF RFC 6716`, `ETSI TS 102 366 V1.4.1`) + source (`aacenc.c`, `aacenc.h`, `aacpsy.c`, `aaccoder.c`, `opus/enc.c`, `opus/enc_psy.c`, `ac3enc.c`, `ac3enc_template.c`, `ac3enc_fixed.c`, `ac3enc_float.c`, `eac3enc.c`).

1. **Native AAC (`aacenc.c`, `2,090L`; `aacpsy.c`, `1,450L`; `aaccoder.c`, `876L`):**
   - **Filterbank & psychoacoustics:** 1024-sample (`ONLY_LONG`) / $8\times 128$-sample (`EIGHT_SHORT`) Sine or Kaiser-Bessel Derived (`KBD`) MDCT via `libavutil/tx` (`av_tx`). `aacpsy.c` implements a 3GPP TS 26.403-derived Bark-band spreading and perceptual entropy (`calc_pe_3gpp`, `line 901`) model controlling eight-short transient window switching and stereo window coupling (`pair_decoupled`, `aacenc.c:1056`).
   - **Three selectable rate-distortion coders (`aacenc.h:44-50`):** `AAC_CODER_TWOLOOP` (`search_for_quantizers_twoloop`, `aaccoder.c:838`), `AAC_CODER_FAST`, and the newer Noise-to-Mask Ratio coder `AAC_CODER_NMR` (`aacenc.c:1109`) with dynamic Viterbi sectioning trellis over the 12 spectral Huffman codebooks (`ZERO`, `SQUAD`, `UQUAD`, `SPAIR`, `UPAIR`, `ESC`, plus `NOISE_BT` PNS and `INTENSITY_BT` stereo, `aaccoder.c:237-255`), Temporal Noise Shaping (`aacenc_tns.c`), Mid/Side stereo (`aacenc_is.c`), and `AACEncDSPContext` (`abs_pow34`, `quant_bands` x86/AArch64/RISC-V SIMD).
   - **Hard syntax invariants:** Scalefactor differential jumps must satisfy `diff + SCALE_DIFF_ZERO in [0, 120]` (`av_assert0` at `aacenc.c:1145`), and total frame bits cannot exceed ISO/IEC 13818-7's `6144 * channels` bit-reservoir ceiling (enforced via outer `destbits` re-encoding loop in `aac_encode_frame`).
2. **Native Opus (`opus/enc.c`, `762L`; `opus/enc_psy.c`, `657L`):**
   - **CELT-only & experimental status (`opus/enc.c:745-752`):** Unlike `libopus` (which implements SILK narrow/medium/wideband LP speech coding, CELT fullband MDCT coding, and Hybrid mode), FFmpeg's first-party `ff_opus_encoder` implements **only the CELT layer** (`celt_encode_frame`, `lines 428-492`) and carries **`AV_CODEC_CAP_EXPERIMENTAL`** (`line 751`, rejected by `avcodec_open2` unless `strict_std_compliance <= FF_COMPLIANCE_EXPERIMENTAL`).
   - **Backward-adaptive bit accounting:** Opus range coding (`OpusRangeCoder`) packs symbols from the front of the packet buffer and raw bits from the **back** of the same buffer toward the middle, using fractional 1/8-bit `tell_frac` bit accounting inside `ff_celt_bitalloc` (`line 482`) to compute exact Pyramid Vector Quantization (`PVQ`) pulse counts (`ff_celt_quant_bands`, `line 484`) without explicit bit-allocation side information. Any 1-ulp divergence in `ff_celt_bitalloc` integer log-allocation tables corrupts packet decoding.
3. **AC-3 Float/Fixed & E-AC-3 (`ac3enc.c`, `2,575L`; `ac3enc_template.c`, `462L`; `eac3enc.c`, `285L`):**
   - **Dual float and 24/32-bit fixed-point compilation:** `ac3enc_template.c` compiles twice—once as `ff_ac3_encoder` (`float` KBD window + MDCT) and once as `ff_ac3_fixed_encoder` (`AC3_FIXED = 1`, pure `int32_t` fixed-point MDCT and normalization, `ac3enc_fixed.c:112`). `ff_eac3_encoder` (`eac3enc.c:268`) extends `ff_ac3_encoder` with 6-block frame exponent-strategy index LUTs (`eac3_frame_expstr_index_tab`, `lines 61-66`) and spectral extension/coupling states.
   - **Normative encoder-decoder `bap[]` lockstep (`ac3enc.c:1393-1466`):** AC-3 transmits exponents (`EXP_D15`, `EXP_D25`, `EXP_D45`, `EXP_REUSE`) and a 10-bit `snr_offset` (`coarse_snr_offset << 4 | fine_snr_offset`), **never** the per-bin mantissa bit widths. Both encoder (`s->ac3dsp.bit_alloc_calc_bap`, `line 1409`) and decoder run the exact integer masking curve in ETSI TS 102 366 §7.2 to derive `bap[0..255]` (`0..15`). `cbr_bit_allocation` (`lines 1424-1466`) steps `snr_offset` down by `64` until `count_mantissa_bits(s) <= bits_left`, then refines upward with steps `64, 16, 4, 1` (`for (snr_incr = 64; snr_incr > 0; snr_incr >>= 2)`). Any SIMD vs. scalar mismatch in `AC3DSPContext.bit_alloc_calc_bap` produces an invalid bitstream whose mantissas shift out of alignment.

---

### 7. Formal Verification Priority Architecture & Clean-Room Rewrite Implications

**Basis:** derived (synthesizing §§1–6 source invariants, execution probes, and normative codec standards).

| Verification Priority Tier | Lossless Encoders (`ffv1`, `flac`, `alac`, `wavpack`, `png`, `exr`) | Lossy Encoders (`prores`, `dnxhd`, `mjpeg`, `mpeg1/2/4`, `aac`, `opus`, `ac3`/`eac3`) |
| :--- | :--- | :--- |
| **1. UB-Freedom (Highest)** | Safe slice indexing; eliminate raw pointer `RangeCoder` (`renorm_encoder`) & `PutBitContext` unchecked writes via slice-bounded byte writers; eliminate `GL_EXT_buffer_reference` raw pointer arithmetic unless machine-checked against slice buffer bounds | Bounds-checked `MotionEstContext` reference windows (replacing `get_limits` implicit `EDGE_WIDTH = 16` pointer offset assumptions); safe SIMD intrinsics/verified `.asm` for `FDCTDSP`, `MECmp`, `AACEncDSP`, `AC3DSP` |
| **2. Panic-Freedom** | Prove `maxsize` worst-case entropy expansion theorems **or** totalize slice/frame overrun via normative uncompressed fallback (`FFV1 v4` PCM slice, `ALAC` verbatim, `FLAC` `VERBATIM` subframe, `EXR` raw scanline swap); eliminate `av_assert0` aborts in `flush_put_bits` | Replace `aacenc.c:1145` `av_assert0(diff <= 120)` and `put_bits.h:160` `av_assert0` with clamped scalefactor deltas and `Result<Packet, EncodeError>` propagation; guard `0`-denominator `time_base` / `rc_buffer_size` |
| **3. Behavioral & SIMD-vs-Scalar Equivalence** | Bit-exact equivalence between x86/AArch64/RVV SIMD (`lpc_compute_autocorr`, `lpc16/32_encode`, `llvidencdsp` `sub_left_predict`/Paeth) and scalar reference; bit-exact `AV_CRC_32_IEEE` and `AVMD5` trailers | **Bit-exact SIMD-vs-scalar equivalence** on integer lockstep kernels (`AC3DSP.bit_alloc_calc_bap`, `IDCTDSP.idct` inside `mpv_reconstruct_mb`, `ff_celt_bitalloc`); differential FATE testing on fixed-point `ac3_fixed`, `dnxhd`, `prores` |
| **4. Functional Spec Conformance** | **Closed Round-Trip Theorem:** $\forall F \in \mathcal{V},\; \mathrm{Decode}_{\mathrm{RFC}}(\mathrm{Encode}(F)) = F$ (modulo NaN canonicalization except WavPack which preserves exact NaN bits) | **Syntactic & Buffer Conformance Theorem:** $\forall F,\; \mathrm{Decode}_{\mathrm{spec}}(\mathrm{Encode}(F)) \neq \bot \land \mathrm{VBV/BitReservoirValid}$; **Statistical Quality Gate (CI, non-theorem):** `BD-rate`, `PSNR`/`SSIM`/`VMAF`, `PEAQ` parity on standard media corpora |

**Clean-room modularity divorces from historical FFmpeg C:**
1. **Sever `dnxhd` and `mjpeg` from `MPVMainEncContext`:** Neither SMPTE ST 2019-1 nor ITU-T T.81 uses motion estimation, GOP B-frame reordering, or `ratecontrol.c`; standalone intra-frame pipelines eliminate `>4,700` lines of shared mutable state.
2. **Unify `prores_aw` and `prores_ks`:** Merge both CPU encoders into one clean-room SMPTE RDD 36 module parameterized by a `QuantSearchStrategy::{GreedyFast, ViterbiTrellis}` trait.
3. **Retire experimental CELT-only `opus` or complete SILK+Hybrid:** Clean-room deployments requiring production voice quality below `32 kbps` cannot rely on FFmpeg's experimental CELT-only `opus/enc.c` without adding RFC 6716 SILK/Hybrid encoding or wrapping a verified Opus implementation.

---

## Boundaries

1. **Modern inter-frame software video encoders (`known not to apply` to FFmpeg first-party C):** `FFmpeg/FFmpeg` at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` has zero first-party CPU software encoders for H.264, HEVC, VP8, VP9, AV1, or VVC. Achieving 100% clean-room software encoding for those codecs requires replacing external libraries (`libx264`, `libx265`, `libvpx`, `libsvtav1`/`librav1e`, `libvvenc`) rather than porting code inside `libavcodec`.
2. **Bit-exact cross-ISA output identity on float rate-control and psychoacoustic encoders (`known not to apply`):** Encoders driven by IEEE-754 `float`/`double` psychoacoustics or rate control (`aac`, `opus`, `vorbis`, `ac3` float, and `mpegvideo_enc` with `ratecontrol.c`) legitimately emit different valid packets across FMA vs. non-FMA targets; bit-exact cross-ISA output equivalence applies only when float contractions are disabled (`-ffp-contract=off`) and `libm` transcendentals (`pow`, `log2f`, `cos`) are replaced by deterministic software approximations, or on purely integer encoders (`ffv1`, `flac`, `alac`, `wavpack`, `ac3_fixed`, `dnxhd`, `prores_aw`).
3. **FFV1 version $\le 3$ worst-case packet clamping above 2 GiB (`unsupported`):** Because `AVPacket.size` is `int` (`INT_MAX = 2,147,483,647`), `ffv1enc.c:2014-2021` clamps `maxsize` below `2 GiB`, and FFV1 versions `0, 1, 3` lack version 4's uncompressed `slice_coding_mode = 1` escape (`line 1917`), making extreme multi-gigapixel incompressible frames unsupported.
4. **Throughput of `ffv1_vulkan` and `prores_ks_vulkan` across discrete GPUs (`not examined` by execution):** Capsule sandbox execution lacked physical Vulkan 1.3+ GPU hardware; shader memory-safety invariants and subgroup CRC reductions were established statically from `ffv1enc_vulkan.c`, `proresenc_kostya_vulkan.c`, and `.comp.glsl` sources (`Basis: source`).

---

## Evidence

### Primary Source Coordinates (`FFmpeg/FFmpeg` @ `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`)

- **Global encoder registry & build graph:** `libavcodec/allcodecs.c:1-960` (`273` `ff_*_encoder` symbols), `configure` (`*_encoder_deps`, `*_encoder_select`), `libavcodec/Makefile`, `libavcodec/vulkan/Makefile` (`21` Vulkan encoder `.comp.spv.o` targets), `tools/Makefile`, `tools/target_enc_fuzzer.c:83-228` (`line 105`: `c->p.type != AVMEDIA_TYPE_VIDEO`), `tools/enc_recon_frame_test.c:46-135`.
- **Framing & bitstream primitives:** `libavcodec/encode.c:63-640` (`ff_alloc_packet`, `pad_last_frame`, `encode_simple_internal`), `libavcodec/put_bits.h:37-285` (`BitBuf`, `flush_put_bits` `av_assert0` at `line 160`, `put_bits_no_assert` drop at `lines 222-225, 240-243`), `libavcodec/rangecoder.h:35-105` (`renorm_encoder` at `lines 62-77`, `put_rac` at `lines 87-105`).
- **FFV1 CPU & Vulkan:** `libavcodec/ffv1enc.c:198-255` (`put_symbol_inline`), `lines 527, 2075-2081` (`AV_CRC_32_IEEE` + `0x8CD88196`), `lines 1195-1575` (`choose_rct_params`, `encode_histogram_remap`, `encode_float32_remap`), `lines 1804-2094` (`encode_slice`, `ff_ffv1_encode_buffer_size`, `encode_frame`); `libavcodec/ffv1enc_vulkan.c:290-835, 1213-1629`; `libavcodec/vulkan/ffv1_enc.comp.glsl:37-690` (`u8buf` physical buffer pointers at `lines 585, 618`; subgroup CRC-32 at `lines 624-658`).
- **Mezzanine & image encoders:** `libavcodec/proresenc_anatoliy.c:294-950`; `libavcodec/proresenc_kostya.c:244-1047` (Viterbi trellis `lines 621-721`); `libavcodec/proresenc_kostya_vulkan.c:109-994`; `libavcodec/dnxhdenc.c:81-210, 1072-1220, 1344-1369` (`radix_sort`); `libavcodec/mjpegenc.c:177-278, 648-730`; `libavcodec/mjpegenc_common.c:464-565` (`ff_mjpeg_escape_FF`); `libavcodec/pngenc.c:175-370, 633-690, 1290-1331`; `libavcodec/exrenc.c:63-68, 158-345, 545-559`.
- **Inter-frame `MPVMainEncContext`:** `libavcodec/mpegvideo_enc.c:300-310, 553-985, 1148-1190, 1497-1725, 2550-2755, 3920-4707`; `libavcodec/mpeg12enc.c:661-1377`; `libavcodec/mpeg4videoenc.c:452-1373`; `libavcodec/motion_est.c:545-620, 888-1165, 1488-1520`; `libavcodec/motion_est_template.c:50-995`; `libavcodec/ratecontrol.c:167-230, 496-545, 730-1060`.
- **Audio encoders:** `libavcodec/flacenc.c:717-1230, 1618-1771`; `libavcodec/lpc.c:133-355`; `libavcodec/flacencdsp.c:1-40`; `libavcodec/alacenc.c:68-651`; `libavcodec/wavpackenc.c:129-500, 1129-1925, 2530-2990`; `libavcodec/aacenc.h:44-160`; `libavcodec/aacenc.c:1050-1240, 2070-2090`; `libavcodec/aacpsy.c:890-1035, 1440-1450`; `libavcodec/aaccoder.c:73-295, 695-876`; `libavcodec/opus/enc.c:124-762`; `libavcodec/opus/enc_psy.c:1-657`; `libavcodec/ac3enc.c:727-950, 1393-1485, 2014-2575`; `libavcodec/ac3enc_fixed.c:110-129`; `libavcodec/ac3enc_float.c:110-131`; `libavcodec/eac3enc.c:60-285`.

### Executed Standalone Verification Probe (`2026-11-20`, Linux x86_64, `gcc -O2 -Wall -Wextra -Werror -fsanitize=undefined`)

```c
/* probe_encoders.c — Self-contained verification of FLAC 33-bit order-4 expansion
 * and exhaustive proof of flacenc.c:942 lpc16_encode vs lpc32_encode narrowing bounds. */
#include <stdint.h>
#include <stdio.h>
#include <limits.h>

static int av_log2_u32(uint32_t v) { return v ? 31 - __builtin_clz(v) : 0; }

int main(void) {
    int64_t smp33[5] = {
         ((int64_t)1 << 32) - 1, -((int64_t)1 << 32) + 1,
         ((int64_t)1 << 32) - 1, -((int64_t)1 << 32) + 1, ((int64_t)1 << 32) - 1
    };
    int64_t r4 = smp33[4] - 4*smp33[3] + 6*smp33[2] - 4*smp33[1] + smp33[0];
    printf("FLAC_33BPS_ORDER4_MAX_RESIDUAL=%lld (bits_needed=37, ratio_vs_INT32_MAX=%.2f)\n",
           (long long)r4, (double)r4 / (double)INT32_MAX);

    int lpc16_triples = 0, lpc16_acc_overflows = 0, lpc16_res_overflows_shift0 = 0;
    int lpc32_triples = 0, lpc32_res_overflows_shift4 = 0;
    for (int b = 4; b <= 32; b++) {
        for (int p = 2; p <= 15; p++) {
            for (int o = 1; o <= 32; o++) {
                __int128 s_abs = (__int128)1 << (b - 1);
                __int128 c_sym = ((__int128)1 << (p - 1)) - 1;
                __int128 max_acc = (__int128)o * c_sym * s_abs;
                if (b + p + av_log2_u32((uint32_t)o) <= 32) {
                    lpc16_triples++;
                    if (max_acc > INT32_MAX) lpc16_acc_overflows++;
                    if (max_acc + s_abs > INT32_MAX) lpc16_res_overflows_shift0++;
                } else {
                    lpc32_triples++;
                    if ((max_acc >> 4) + s_abs > INT32_MAX) lpc32_res_overflows_shift4++;
                }
            }
        }
    }
    printf("FLAC_LPC16_GUARD_EXHAUSTIVE: triples=%d acc_overflows=%d shift0_res_overflows=%d\n",
           lpc16_triples, lpc16_acc_overflows, lpc16_res_overflows_shift0);
    printf("FLAC_LPC32_NARROWING_HAZARD: triples=%d shift4_res_overflows=%d\n",
           lpc32_triples, lpc32_res_overflows_shift4);
    return 0;
}
```

Observed output (`exit 0`, zero UBSan diagnostics):
```text
FLAC_33BPS_ORDER4_MAX_RESIDUAL=68719476720 (bits_needed=37, ratio_vs_INT32_MAX=32.00)
FLAC_LPC16_GUARD_EXHAUSTIVE: triples=7742 acc_overflows=0 shift0_res_overflows=0
FLAC_LPC32_NARROWING_HAZARD: triples=5250 shift4_res_overflows=3464
```

---

## Revalidation

To revalidate these findings against a newer `FFmpeg/FFmpeg` revision `<NEW_SHA>`:
1. **Encoder census & modern codec check (<5s):** Fetch `libavcodec/allcodecs.c` and `configure` at `<NEW_SHA>`, count `extern const FFCodec ff_*_encoder;`, and check whether any non-`lib*`, non-hwaccel symbol matches `(h264|hevc|vp8|vp9|av1|vvc)` or whether `libavcodec/vulkan/Makefile` added new `*_VULKAN_ENCODER` compute targets beyond `ffv1_vulkan`, `prores_ks_vulkan`, and `apv_vulkan`.
2. **OSS-Fuzz audio blind-spot & `opus` experimental flag check (<3s):** Inspect `tools/target_enc_fuzzer.c` around `c->p.type != AVMEDIA_TYPE_VIDEO` and `libavcodec/opus/enc.c` around `ff_opus_encoder` `.p.capabilities` (`AV_CODEC_CAP_EXPERIMENTAL`).
3. **Bitstream writer & FLAC LPC bounds re-execution (<2s):** Diff `libavcodec/put_bits.h` (`flush_put_bits`, `put_bits_no_assert`), `libavcodec/rangecoder.h` (`renorm_encoder`), and `libavcodec/flacenc.c` (`lpc_encode_choose_datapath`), and re-run `gcc -O2 -Wall -Wextra -Werror -fsanitize=undefined probe_encoders.c -o /tmp/probe_encoders && /tmp/probe_encoders`.
