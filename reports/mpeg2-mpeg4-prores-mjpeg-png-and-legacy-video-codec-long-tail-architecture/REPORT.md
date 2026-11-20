# FFmpeg Video and Still-Image Codec Long-Tail Architecture: Shared DSP Factorization, IDCT Conformance Regimes, and Bounds-Safe Decoding

## Summary

At commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, `FFmpeg/FFmpeg` defines `276` video and still-image `AVCodecID` values (`libavcodec/codec_id.h:50-330`) and declares `883` `FFCodec` descriptors (`610` decoders, `273` encoders) across `2,788` files (`46.49 MB`) in `libavcodec/`. Despite surface diversity spanning legacy broadcast/optical standards (MPEG-1/2, MPEG-4 Part 2, H.263, VC-1, DV), post-production mezzanine codecs (Apple ProRes, SMPTE VC-3/DNxHD), still/HDR raster formats (MJPEG, PNG, WebP, OpenEXR), archival lossless codecs (FFV1, UtVideo, HuffYUV), and dozens of legacy game/multimedia formats (Bink, Smacker, Cinepak, QTRLE, S3TC/RGTC textures), transitive build-graph closure over `configure` reveals extreme structural concentration: `54` decoders share `idctdsp`, `53` share `blockdsp`, `46` share `videodsp`, `40` share `hpeldsp`, `35` share `bswapdsp`, `24` share `mpegvideodec` (`MpegEncContext`), `20` share `golomb`, `16` share `inflate_wrapper`, `15` share `jpegtables`, `8` share `llviddsp`, and `6` share `texturedsp`.

Clean-room formal verification and high-assurance Rust reimplementation of this long tail avoid per-codec proof explosion only by factoring codecs along six shared semantic substrates while eliminating three pervasive C-level coupling hazards documented in upstream sources:

1. **Non-local bitstream overread invariants (`UNCHECKED_BITSTREAM_READER`):** Performance-critical decoders (`mpeg12dec.c:30`, `mpeg4videodec.c:23`, `dnxhddec.c:35`, `utvideodec.c:31`, `smacker.c:49`) compile `get_bits.h` without index clamping. In `dnxhddec.c`, macroblock row decoding (`dnxhd_decode_row`, lines `595-618`) executes zero `get_bits_left` checks; memory safety relies on a non-local three-way invariant uniting `AV_INPUT_BUFFER_PADDING_SIZE == 64` zeroed tail bytes (`defs.h:40`), Kraft-complete static Huffman tables (`dnxhddata.c`), and the fact that every DNxHD/DNxHR AC table maps the zero prefix `00` (`2` bits) to a non-EOB symbol (`index == 0`), forcing `++i > 63` termination after `213` bits (`< 512` padding bits). Unpadded slices or uninitialized padding bytes break memory safety.
2. **Pre-offset out-of-bounds pointer arithmetic in motion compensation (`emulated_edge_mc`):** Callers pass `src = plane_base + src_y * stride + src_x` for out-of-frame motion vectors, and `videodsp_template.c:38-54` arithmetically subtracts the out-of-bounds offset back inside `[0, h - 1] x [0, w - 1]`. Under ISO C11 §6.5.6p8 and Rust `pointer::offset` provenance rules, forming the out-of-bounds intermediate pointer is immediate undefined behavior even without dereferencing it.
3. **Bifurcated inverse-transform conformance and scantable-permutation coupling:** Legacy standards governed by IEEE Std 1180-1990 / ISO/IEC 23002-1:2006 (MPEG-1, MPEG-2, H.263, MPEG-4 Part 2, baseline JPEG) specify statistical floating-point error envelopes rather than a bit-exact integer transform. Standalone execution of FFmpeg's `ff_simple_idct_int16_8bit` (`simple_idct_template.c:48-285`) and `ff_faanidct` (`faanidct.c:27-136`) over `10,000` IEEE 1180 pseudo-random blocks confirms both comfortably pass every normative threshold (`PPE == 1`, `OMSE <= 0.0110 <= 0.02`), yet disagree with each other on `50.72%` of blocks (`max_diff == 1` LSB). Conversely, SIMD `simple_idct` kernels (`x86_64` SSE2/AVX and `aarch64` NEON) are bit-exact with scalar `simple_idct` up to a mandatory input-scantable bijection $\pi_{\text{perm}}$ (`IDCTDSPContext::idct_permutation`, `idctdsp.c:30-71`) satisfying the fixed-point law $\pi(0) = 0 \land \pi(63) = 63$ required by direct DC assignment and H.262 §7.4.4 `block[63] ^= mismatch & 1` parity toggling (`mpeg12dec.c:303, 385`; `mpeg4videodec.c:2267`). Newer long-tail standards (VC-1 SMPTE ST 421M) abandon statistical tolerances in favor of normatively bit-exact integer transforms (`vc1dsp.c:262-406`).

## Applicability

The findings in this report apply to `FFmpeg/FFmpeg` at commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (specifically `libavcodec/` and its build-system dependency graph in `configure` and `libavcodec/Makefile`) interpreted alongside the normative codec and transform specifications listed in `REPORT.json`: ITU-T Rec. H.262 | ISO/IEC 13818-2 (MPEG-2), ISO/IEC 14496-2 (MPEG-4 Visual), ISO/IEC 23002-1:2006 and its historical baseline IEEE Std 1180-1990, SMPTE ST 421:2006 (VC-1), SMPTE RDD 36:2015 (ProRes), SMPTE ST 2019-1 (VC-3/DNxHD), IETF RFC 9043 (FFV1), IETF RFC 9649 (WebP), and ISO/IEC 15948:2004 / W3C PNG.

Scope qualifications:

- **In scope:** Software video and still-image decoding/encoding architectures outside the modern ITU/AOM flagship quartet (H.264/AVC, H.265/HEVC, H.266/VVC, and AV1, which use dedicated `h264dsp`, `hevcdsp`, `vvcdsp`, and `dav1d`/AV1 pipelines); shared `libavcodec` bitstream readers (`get_bits.h`, `bytestream.h`, `vlc.h`, `rangecoder.h`) and DSP dispatch tables (`IDCTDSPContext`, `HpelDSPContext`, `QpelDSPContext`, `VideoDSPContext`, `BswapDSPContext`, `BlockDSPContext`, `LLVidDSPContext`, `PNGDSPContext`, `ExrDSPContext`, `ProresDSPContext`, `VC1DSPContext`, `TextureDSPContext`); SIMD dispatch across `x86_64`, `aarch64`, and `riscv64`; and clean-rewrite verification architecture across UB-freedom, panic-freedom, reference/SIMD equivalence, and normative conformance.
- **Relationship to sibling corpus reports:** General entropy-bitstream parser hazards and Huffman subtable sizing in standalone `libwebp`/`dav1d` are analyzed in `entropy-coded-media-bitstreams-video-codec-security-and-simd-decoders` and `libwebp-huffman-tables-dav1d-rans-cdfs-and-lcms2-icc-tetrahedral-luts`; DEFLATE/inflate mechanics underlying PNG and OpenEXR `ZIP`/`ZIPS` chunks are covered in `deflate-inflate-algorithms-optimal-dp-and-block-splitting`. This report focuses specifically on `FFmpeg/FFmpeg`'s internal multi-codec factorization, shared DSP contracts, transform accuracy semantics, and long-tail codec invariants without duplicating standalone `libwebp` or `zlib` internals.
- **Execution environment for empirical probes:** Standalone C conformance and divergence probes were compiled and executed on Linux `x86_64` using `gcc (Debian 15.2.0-14) 15.2.0` at `-O2` with standard IEEE-754 binary32/binary64 round-to-nearest-even (`FE_TONEAREST`) semantics.

## Findings

### 1. Quantitative Census and Six-Family Structural Factorization of `libavcodec`

`Basis: source + derived`

Inspection of `libavcodec/codec_id.h:50-601` and `libavcodec/allcodecs.c:1-890` at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` establishes the scale and internal partitioning of `libavcodec`:

- **Codec identifier and descriptor totals:** `enum AVCodecID` defines `276` distinct video and still-image codec IDs (`codec_id.h:50-330`), `226` audio codec IDs (`0x10000` upward, `codec_id.h:332-569`), and `27` subtitle codec IDs (`0x17000` upward, `codec_id.h:571-600`). `allcodecs.c` registers `883` `FFCodec` descriptors (`610` decoders and `273` encoders). Within the video/image section (`allcodecs.c:32-424`) plus late-priority wrapper sections (`allcodecs.c:757-890`), `270` first-party software video/image decoders and `90` first-party software encoders coexist alongside `79` external-library or hardware-API wrapper decoders and `89` wrapper encoders (`_nvenc`, `_vaapi`, `_qsv`, `_v4l2m2m`, `_videotoolbox`, `_mediacodec`, `_amf`, `_vulkan`, `_cuvid`, `lib*`).
- **ISA directory distribution:** Across `libavcodec/`'s `2,788` files (`46,489,936` bytes), `1,738` root files (`30.69 MB`) hold target-independent C codecs and templates, while ISA-specific assembly and init glue occupy `218` files in `x86/` (`2.33 MB`), `129` in `arm/` (`1.26 MB`), `111` in `riscv/` (`0.45 MB`), `110` in `mips/` (`4.48 MB`), `96` in `aarch64/` (`1.81 MB`), `74` in `ppc/` (`0.29 MB`), `55` in `loongarch/` (`1.71 MB`), and `48` in `vulkan/` (`0.27 MB`).

Evaluating the transitive closure of all `220` `*_decoder_select` rules in `configure` shows that FFmpeg's `~270` first-party video and image decoders collapse into **six reusable architectural families**, summarized below:

| Family | Representative `libavcodec` Decoders | Shared `configure` / C Substrates (Transitive Decoder Count) | Core Mathematical / State Kernel |
| :--- | :--- | :--- | :--- |
| **F1: Hybrid Block MC + 8x8 DCT (`MPV`)** | MPEG-1/2 (`mpeg12dec.c`), H.261, H.263/H.263+, MPEG-4 Part 2 (`mpeg4videodec.c`), MSMPEG4v1-v3, WMV1/2, RV10/20, FLV1 | `mpegvideodec` (`24`), `idctdsp` (`54`), `blockdsp` (`53`), `videodsp` (`46`), `hpeldsp` (`40`), `h263_decoder` (`11`), `qpeldsp` (`9`), `mpeg_er` (`24`) | `MpegEncContext` (`mpegvideo.h:67`): `16x16` macroblocks, `Last`/`Next` reference frames, half/quarter-pel MC, RL-VLC + zigzag scan + 8x8 IDCT |
| **F2: hybrid Integer-Transform + Loop/Overlap Filter** | VC-1 / WMV3 (`vc1dec.c`), VP3/Theora, VP5/6, VP8 (`vp8.c`), RV30/40, RealVideo 6, IntraX8 | `vc1dsp`, `vp3dsp` (`7`), `vp8dsp` (`4`), `h264chroma` (`32`), `videodsp` (`46`), `golomb` (`20`) | Bit-exact integer `8x8`/`8x4`/`4x8`/`4x4` transforms, spatial intra prediction, overlap smoothing and/or conditional loop deblocking |
| **F3: Broadcast Intra-DCT Mezzanine & Still JPEG** | MJPEG / Lossless JPEG (`mjpegdec.c`), Apple ProRes (`proresdec.c`), VC-3 / DNxHD / DNxHR (`dnxhddec.c`), DV (`dvdec.c`), SpeedHQ, HQX | `idctdsp` (`54`), `jpegtables` (`15`), `mjpeg_decoder` (`11`), `proresdsp`, `blockdsp` (`53`), `exif` | Frame-independent `I`-only coding; explicit slice/row byte-offset tables (`mb_scan_index`) enabling data-parallel slice threads (`AV_CODEC_CAP_SLICE_THREADS`) |
| **F4: Lossless Spatial-Predictive + VLC / Range / Inflate** | FFV1 (`ffv1dec.c`), PNG / APNG (`pngdec.c`), UtVideo (`utvideodec.c`), HuffYUV, MagicYUV, Lagarith, LOCO | `llviddsp` (`8`), `bswapdsp` (`35`), `inflate_wrapper` (`16`), `rangecoder` (`2`), `pngdsp`, `utvideodsp`, `huffyuvdsp` | Causal `2D` neighborhood predictors (Left, Top, Median, Gradient, Paeth), reversible color transforms (`RCT`/deloco), exact modular `2^b` wraparound |
| **F5: HDR / Wavelet / Subband / Hybrid Container Images** | OpenEXR (`exr.c`), WebP (`webp.c`), JPEG 2000, Dirac / VC-2, CineForm (`cfhd`), Snow | `exrdsp`, `inflate_wrapper` (`16`), `vp8dsp` (`4`), `jpeg2000dsp`, `diracdsp`, `cfhddsp`, `bswapdsp` (`35`) | Scanline/tile offset directories, 2D DWT (`5/3` reversible, `9/7` float/fixed, Haar/PIZ), half-float byte split + delta prediction (`exrdsp.c:27-57`), LZ77+color cache (VP8L) |
| **F6: Fixed-Block Texture, VQ, Palette, and RLE Multimedia** | HAP / DXV (`texturedsp.c`), Bink (`bink.c`), Smacker (`smacker.c`), Cinepak (`cinepak.c`), QTRLE (`qtrle.c`), RPZA | `texturedsp` (`6`), `binkdsp`, `bytestream.h`, `vlc.h` | `4x4` endpoint interpolation (DXT1/DXT5/RGTC), `256`-entry vector codebooks (`cvid_codebook`), bundle queues (`BinkContext`), stateful skip/repeat RLE cursors |

**Architectural consequence for verification (`Basis: derived`):** A naive verification strategy that treats `270` video/image decoders as `270` bespoke state machines incurs prohibitive proof cost. However, inside each family above, codecs differ primarily in **bitstream header syntax, static VLC/quantization tables, and predictor/transform parameterizations**, whereas memory write topologies (macroblock grids, slice partitions, row ring buffers, or `4x4` tile grids) and inner DSP kernels are shared. Proving memory safety and functional correctness once on parameterized family engines—instantiated via const-generic or verified table descriptors—reduces the verification surface from hundreds of ad-hoc loops to six family skeletons plus ~15 shared DSP/bitstream modules.

---

### 2. Shared Bitstream, VLC, and Range-Coding Substrates and Hidden Padding Preconditions

`Basis: source + derived`

Nearly every long-tail codec ingests untrusted packet bytes through one of three primitives in `libavcodec/`: bit-level `GetBitContext` (`get_bits.h`), byte-level `GetByteContext` (`bytestream.h`), or arithmetic `RangeCoder` (`rangecoder.h`).

#### 2.1 `GetBitContext`, `AV_INPUT_BUFFER_PADDING_SIZE`, and `UNCHECKED_BITSTREAM_READER`

In `libavcodec/get_bits.h:109-114` (default non-cached reader), `GetBitContext` stores:

```c
typedef struct GetBitContext {
    const uint8_t *buffer;
    int index;
    int size_in_bits;
    int size_in_bits_plus8;
} GetBitContext;
```

`init_get_bits` (`get_bits.h:517-534`) rejects `bit_size < 0` or `bit_size >= INT_MAX - FFMAX(7, AV_INPUT_BUFFER_PADDING_SIZE * 8)` (preventing `int` overflow on `bit_size + 8` and subsequent index increments) and sets `s->size_in_bits_plus8 = bit_size + 8`. All `AVPacket` and bitstream buffers in FFmpeg carry a mandatory tail allocation of `AV_INPUT_BUFFER_PADDING_SIZE == 64` zeroed bytes (`512` zero bits, `libavcodec/defs.h:40`).

Two distinct bounds-checking regimes exist (`get_bits.h:52-55, 176-226`):

1. **Checked reader (`UNCHECKED_BITSTREAM_READER == 0`):** `SKIP_COUNTER` (`get_bits.h:224`) clamps `name_index = FFMIN(name_size_plus8, name_index + num)`. Even in this checked mode, `name_index` advances up to `bit_size + 8` (`1` byte past the logical bit payload), and `UPDATE_CACHE_BE_32` / `UPDATE_CACHE_LE_32` (`get_bits.h:191-199`) executes `AV_RB64(gb->buffer + (name_index >> 3))`, reading `8` bytes starting up to `1` byte past `(bit_size >> 3)`—a mandatory **up-to-9-byte hardware read past the logical payload end** that requires valid padded allocation even when safe bitstream reading is enabled.
2. **Unchecked reader (`UNCHECKED_BITSTREAM_READER == 1`):** Individual decoders override global `CONFIG_SAFE_BITSTREAM_READER` by defining `#define UNCHECKED_BITSTREAM_READER 1` prior to `#include "get_bits.h"`. Verified examples in the long tail include `mpeg12dec.c:30`, `mpeg4videodec.c:23`, `dnxhddec.c:35`, `utvideodec.c:31`, and `smacker.c:49`. Under this flag, `SKIP_COUNTER` compiles to bare `name_index += (num)` (`get_bits.h:221`) with zero bounds clamping.

**Hidden three-way safety invariant in `dnxhddec.c` (`Basis: source + derived`):**
Inspection of every occurrence of `buf_size`, `mb_width`, and `get_bits_left` in `libavcodec/dnxhddec.c:1-743` alongside `libavcodec/dnxhddata.h:40-60` and `libavcodec/dnxhddata.c:1043-1078` reveals a subtle non-local safety dependency:
- For variable-resolution DNxHR profiles (`cid` `1270..1274`), `coding_unit_size` in `dnxhd_cid_table` is `DNXHD_VARIABLE` (`0`, `dnxhddata.h:41`). Consequently, `if (buf_size < ctx->cid_table->coding_unit_size)` (`dnxhddec.c:300`) reduces to `buf_size < 0` (vacuously false), and `dnxhd_decode_header` accepts any packet with `buf_size >= data_offset` (`>= 640` bytes, `dnxhddec.c:185, 333`) and `mb_scan_index[rownb] <= buf_size - data_offset` (`dnxhddec.c:349`), even when `ctx->buf_size - offset == 0` while `ctx->mb_width` is up to `4,096` (`width <= 65535`, `dnxhddec.c:220, 306`).
- `dnxhd_decode_row` (`dnxhddec.c:595-618`) loops `for (x = 0; x < ctx->mb_width; x++) dnxhd_decode_macroblock(...)` with **zero** `get_bits_left(&row->gb)` checks anywhere in `dnxhddec.c`.
- Why does `dnxhd_decode_row` not walk off the end of the `64`-byte (`512`-bit) padding on a truncated `0`-byte slice? Algebraic inspection of all six AC Huffman tables (`dnxhd_1235`, `1237`, `1238`, `1250`, `1251`, `1252` in `dnxhddata.c`) proves two exact table properties:
  1. All six `ac_bits` (`257` entries, max length `16`) and `run_bits` (`62` entries, max length `10`) satisfy Kraft equality $\sum_{k} 2^{-\ell_k} = 1$ exactly, which is why `dnxhd_decode_dct_block` (`dnxhddec.c:416-438`) omits `index1 < 0` and `run < 0` error checks (whereas 8-bit `dc_vlc` truncates a 14-entry Kraft-1 table to `12` entries at `dnxhddec.c:142`, making it Kraft-incomplete and requiring `if (len < 0) goto error;` at line `400`).
  2. Every single DNxHD/DNxHR AC table assigns codeword `0` (`00`, `2` bits) to `index1 = 0` (`level = 3`, `flags = 0`), whereas `eob_index` is `3`, `4`, or `5` (`dnxhddata.c:981-1072`). When `row->gb` enters the zero-filled `AV_INPUT_BUFFER_PADDING_SIZE` region, the macroblock header consumes `12` bits, DC `000` (`len = 5`) consumes `3 + 5 = 8` bits, and `while (index1 != eob_index)` consumes `3` bits (`2` VLC + `1` sign) per coefficient for `64` iterations until `if (++i > 63)` triggers `ret = -1` (`dnxhddec.c:439-442`) at exactly `12 + 8 + 2 + 63 * 3 + 2 = 213` bits (`26.6` bytes $< 64$ bytes), aborting `dnxhd_decode_row` cleanly.
- **Crucial verification implication:** In `dnxhddec.c` (and similarly in `mpeg12dec.c:167-215`, where `0x00000000` fails the `GET_RL_VLC` table and hits invalid/escape bounds), the `64`-byte tail buffer is **not** merely an uninitialized read-slop guard—its **all-zero byte content** is an active termination sentinel. Passing an unpadded Rust `&[u8]` or padding with uninitialized arena bytes permits crafted or stale `eob_index` bit patterns in the padding to drive `x` across thousands of macroblocks out of bounds.

#### 2.2 Multi-Stage `VLC` Table Invariants (`vlc.h`, `get_bits.h`)

`VLC` (`libavcodec/vlc.h:32-54`) packs Huffman lookup entries into `4`-byte `VLCElem` unions (`int16_t sym; int16_t len;` or `int16_t level; int8_t len8; uint8_t run;`). `GET_VLC` (`get_bits.h:573-600`) resolves codes up to `max_depth` (`1`, `2`, or `3`) stages of width `bits` (typically `7..11` bits):

- If `n_ > 0`, `table[idx_]` is a leaf consuming `n_` bits (`1 <= n_ <= bits`).
- If `n_ < 0` and `max_depth > 1`, `table[idx_]` is an internal prefix node: `nb__bits = -n_` gives the subtable bit width (`1 <= nb__bits <= bits`), and `code` holds the positive base offset in `table[]` so the next lookup evaluates `idx_ = SHOW_UBITS(name, gb, nb__bits) + code` (`get_bits.h:585, 594`).
- If `n_ == 0` (an unassigned prefix in a Kraft-incomplete code where $\sum 2^{-\ell_k} < 1$), `code == -1` and `SKIP_BITS(name, gb, 0)` consumes **zero bits** (`get_bits.h:599`). Any caller loop that invokes `get_vlc2` without terminating on `code < 0` enters a zero-bit-progress livelock on malformed input, and `SHOW_UBITS_BE` (`NEG_USR32(cache, num)`, shifting a `uint32_t` by `32 - num`) requires `1 <= num <= 25` (`get_bits.h:341`) to avoid C shift-by-32 undefined behavior—meaning table construction (`ff_vlc_init_sparse` / `ff_vlc_init_from_lengths`) must guarantee `1 <= -len <= 25` and `code + (1 << (-len)) <= table_size` for every negative-length entry.

#### 2.3 `GetByteContext` (`bytestream.h`) vs. `RangeCoder` (`rangecoder.h`)

- **`bytestream.h` (`lines 33-99`):** `DEF(...)` generates paired checked (`bytestream2_get_le32`) and unchecked (`bytestream2_get_le32u`) accessors. Checked reads saturate `g->buffer = g->buffer_end` and return `0` when `g->buffer_end - g->buffer < bytes` (`lines 74-77`), providing total, panic-free byte parsing used across `pngdec.c`, `webp.c`, `exr.c`, `cinepak.c`, and `qtrle.c`. Unchecked `*u` calls require an dominating `bytestream2_get_bytes_left(&gb) >= K` guard in the enclosing block.
- **`rangecoder.h` (`lines 35-136`) and `rangecoder.c` (`lines 42-106`):** Used by FFV1 (`ffv1dec.c`) and Snow. `ff_init_range_decoder` (`rangecoder.c:53-66`) initializes `c->range = 0xFF00` and reads `c->low = AV_RB16(c->bytestream)`. If `c->low >= 0xFF00`, it clamps `c->low = 0xFF00` and collapses `c->bytestream_end = c->bytestream`. On every `get_rac(c, state)` call (`rangecoder.h:118-136`), `ff_build_rac_states` (`rangecoder.c:68-106`) guarantees `*state` stays in `[1, 255]`; with `0x100 <= c->range <= 0xFF00`, `range1 = (c->range * (*state)) >> 8` satisfies `1 <= range1 < c->range`. `refill` (`rangecoder.h:107-116`) checks `c->bytestream < c->bytestream_end` before dereferencing and otherwise increments `c->overread++` (`#define MAX_OVERREAD 2`, checked per line via `is_input_end` in `ffv1dec.c:80-90`), making the range decoder memory-safe on arbitrary `buf_size >= 2` buffers (while `buf_size < 2` relies on packet padding for the initial `AV_RB16`). By contrast, `renorm_encoder` (`rangecoder.h:62-77`) writes `*c->bytestream++` **without** checking `c->bytestream_end`, requiring callers to pre-allocate worst-case expansion slack.

---

### 3. Shared Spatial/Temporal DSP Contexts, Scantable Permutations, and Motion-Compensation Provenance

`Basis: source + derived`

Across `libavcodec`, inner pixel loops are isolated behind function-pointer tables initialized to portable C fallbacks and overridden per CPU capability flag (`av_get_cpu_flags()`):

1. **`IDCTDSPContext` (`idctdsp.h:43-90`, `idctdsp.c:228-314`):** Exposes `idct`, `idct_put`, `idct_add`, `put_pixels_clamped`, `put_signed_pixels_clamped`, and `add_pixels_clamped`, plus `uint8_t idct_permutation[64]` (`enum idct_permutation_type`).
   - **ISA permutation coupling:** Scalar `ff_simple_idct_int16_8bit` sets `FF_IDCT_PERM_NONE` (`idctdsp.c:287`). On `x86_64`, `ff_idctdsp_init_x86` (`x86/idctdsp_init.c:86-151`) installs `ff_simple_idct8_sse2` / `ff_simple_idct8_avx` (and `10`-/`12`-bit `ff_simple_idct{10,12}_put_{sse2,avx}`) and mutates `c->perm_type = FF_IDCT_PERM_TRANSPOSE` (`((i & 7) << 3) | (i >> 3)`). On `aarch64`, `ff_idctdsp_init_aarch64` (`aarch64/idctdsp_init_aarch64.c:39-54`) installs 8-bit `ff_simple_idct_neon` and sets `c->perm_type = FF_IDCT_PERM_PARTTRANS` (`(i & 0x24) | ((i & 3) << 3) | ((i >> 3) & 3)`), leaving `10`-/`12`-bit paths on scalar C. On `riscv64`, `ff_idctdsp_init_riscv` (`riscv/idctdsp_init.c:36-48`) accelerates `put/add_pixels_clamped_rvv` (`VLEN >= 128`) but leaves `idct`/`idct_put`/`idct_add` on scalar C.
   - **Global fixed-point invariant on `idct_permutation`:** Every decoder composes its zigzag or alternate scan table with `idct_permutation` at initialization (`ff_permute_scantable`, `idctdsp.c:30-37`), writing AC coefficients to `block[scantable[i]]`. However, MPEG-1/2 (`mpeg12dec.c:160, 251, 303, 334, 385`), MPEG-4 (`mpeg4videodec.c:2267`), and DNxHD (`dnxhddec.c:411`) address DC directly at literal `block[0]` and apply H.262 §7.4.4 mismatch parity directly at literal `block[63] ^= mismatch & 1`. Inspection of all six `enum idct_permutation_type` mappings (`idctdsp.c:50-66`, `x86/idctdsp_init.c:29-58`) confirms every permutation is a bijection on `{0..63}` satisfying $\pi(0) = 0$ and $\pi(63) = 63$. Any SIMD kernel permutation violating $\pi(0) = 0 \land \pi(63) = 63$ silently corrupts DC reconstruction and MPEG-2/MPEG-4 mismatch control.
2. **`VideoDSPContext::emulated_edge_mc` (`videodsp.h:32-69`, `videodsp_template.c:24-102`):** Replicates frame border pixels into a scratch block when a motion vector references coordinates `(src_x, src_y)` outside `[0, w - block_w] x [0, h - block_h]`.
   - **Pointer-provenance UB in the C calling convention:** Callers compute `src = ref_data + src_y * src_linesize + src_x * sizeof(pixel)` prior to checking frame bounds. Inside `emulated_edge_mc` (`videodsp_template.c:38-54`), when `src_y >= h` or `src_y <= -block_h`, the function recovers an in-bounds pointer via `src -= src_y * src_linesize; src += (h - 1) * src_linesize;`, and analogously adjusts `src` horizontally when `src_x >= w` or `src_x <= -block_w`. Under ISO C11 §6.5.6p8 and Rust/LLVM `getelementptr inbounds` rules, constructing `ref_data + src_y * src_linesize + src_x` outside the allocated `AVFrame` buffer object (including negative row strides for bottom-up frames) has undefined behavior before `emulated_edge_mc` is even entered. A verified Rust redesign must pass `(plane_slice: &[T], plane_offset: usize, stride: isize, src_x: i32, src_y: i32, w: i32, h: i32)` and clamp `(src_x, src_y)` in integer arithmetic prior to slice indexing.
3. **`HpelDSPContext` (`hpeldsp.h:46-96`) and `QpelDSPContext` (`qpeldsp.h`):** Provide `4 x 4` function-pointer matrices (`put_pixels_tab`, `avg_pixels_tab`, `put_no_rnd_pixels_tab`) indexed by block width (`{16, 8, 4, 2}`) and subpel phase (`xhalf + 2 * yhalf`), separating MPEG-1/2/H.263 rounding `(a + b + 1) >> 1` from MPEG-4/DivX `no_rnd` `(a + b) >> 1`. Notably, `hpeldsp.h:80-83` documents that `put_no_rnd_pixels_tab` is over-dimensioned to `[3][4]` despite only supporting widths `16` and `8` specifically `"to avoid out of bounds accesses in the motion estimation code"`.
4. **`BswapDSPContext` (`bswapdsp.h:24-27`), `BlockDSPContext` (`blockdsp.h`), and `LLVidDSPContext` (`lossless_videodsp.h:28-40`):** Factor bulk `16`/`32`-bit endianness conversion (`35` decoders including `utvideodec.c`, `exr.c` big-endian, `fraps`, `truemotion`), `clear_block`/`clear_blocks` (`53` decoders), and causal lossless row predictors (`add_left_pred`, `add_median_pred`, `add_gradient_pred`, `add_left_pred_int16` across `8` lossless video codecs).

---

### 4. Statistical IDCT Tolerance (IEEE 1180 / ISO 23002-1) vs. Exact Integer Transform Regimes

`Basis: normative + source + execution + derived`

Long-tail transform video codecs split cleanly into **two incompatible mathematical conformance regimes**:

#### 4.1 Regime A: Statistical Floating-Point Tolerance + Mismatch Control (MPEG-1, MPEG-2, H.263, MPEG-4 Part 2, JPEG)

Early DCT standards left the `8x8` IDCT implementation open to hardware vendors, constraining drift via **IEEE Std 1180-1990** (withdrawn February 7, 2003) and its normative replacement **ISO/IEC 23002-1:2006** (*MPEG video technologies — Part 1: Accuracy requirements for implementation of integer-output 8x8 inverse discrete cosine transform*). Evaluated over `N >= 10,000` pseudo-random spatial blocks in `[-L, +H]` transformed by a 64-bit float forward DCT and compared against a 64-bit float reference IDCT clipped to `[-256, 255]`, a compliant IDCT must satisfy five simultaneous bounds:

- **Peak Pixel Error (`PPE`):** $\max |e_{x,y}| \le 1$ (for `L = 256` and `L = 300`);
- **Peak Mean Square Error (`PMSE`):** $\max_{x,y} \frac{1}{N}\sum e_{x,y}^2 \le 0.06$ (and **Overall MSE** $\text{OMSE} \le 0.02$);
- **Peak Mean Error (`PME`):** $\max_{x,y} \left|\frac{1}{N}\sum e_{x,y}\right| \le 0.015$ (and **Overall Mean Error** $|\text{OME}| \le 0.0015$);
- **All-zero property:** `block == 0` implies exact `idct(block) == 0`.

To bound open-loop encoder/decoder P-frame accumulation when $\pm 1$ LSB differences occur, standards add **syntax-level mismatch control** prior to the IDCT:
- **MPEG-1 (`mpeg12dec.c:177, 202, 206`):** Per-coefficient oddification—every non-zero dequantized inter AC level is forced odd via `level = (level - 1) | 1` (preventing exact `0.5` half-way tie bias in butterfly shifts).
- **MPEG-2 (ITU-T H.262 §7.4.4, `mpeg12dec.c:235, 303, 336, 385`) and MPEG-4 Part 2 (`mpeg4videodec.c:2171, 2267`):** Whole-block parity toggling—`mismatch` accumulates the XOR of all `64` reconstructed integer levels initialized with `1`; if the total sum of coefficients is even (`(mismatch & 1) == 1`), the highest-frequency coefficient is toggled via `block[63] ^= (mismatch & 1)` so the block sum is strictly odd.

**Empirical execution audit (`Basis: execution`):** Compiling and executing FFmpeg's exact 8-bit fixed-point `ff_simple_idct_int16_8bit` (`W1=22725..W7=4520`, `ROW_SHIFT=11`, `COL_SHIFT=20`, `simple_idct_template.c:48-285`) alongside FFmpeg's floating-point Arai-Agui-Nakajima `ff_faanidct` (`faanidct.c:27-136`) against the 64-bit IEEE-754 `double` reference IDCT over `N = 10,000` IEEE 1180-1990 §5 blocks yields:

| Range `[L, H]` (`N = 10,000`) | Implementation | `PPE` ($\le 1$) | `PMSE` ($\le 0.06$) | `OMSE` ($\le 0.02$) | `PME` ($\le 0.015$) | `OME` ($\le 0.0015$) | Pairwise Block Disagreement (`simple` vs. `faan`) |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| `[-256, +255]` | `simple_idct` (`int16` fixed) | `1` | `0.014400` | `0.010994` | `0.003000` | `0.000106` | **`5,072 / 10,000` blocks (`50.72%`)**, `7,038 / 640,000` pixels (`1.10%`), `max_diff = 1` |
| `[-256, +255]` | `faanidct` (`float` AAN) | `1` | `0.000100` | `0.000022` | `0.000100` | `0.000009` | (same pair) |
| `[-300, +300]` | `simple_idct` (`int16` fixed) | `1` | `0.013700` | `0.010736` | `0.003300` | `0.000027` | **`4,982 / 10,000` blocks (`49.82%`)**, `6,872 / 640,000` pixels (`1.07%`), `max_diff = 1` |
| `[-300, +300]` | `faanidct` (`float` AAN) | `1` | `0.000100` | `0.000014` | `0.000100` | `0.000005` | (same pair) |

Both implementations pass all five IEEE 1180 / ISO 23002-1 limits with wide margin and pass the all-zero check, yet **half of all non-trivial 8x8 blocks differ by $\pm 1$ LSB** between two valid FFmpeg `FF_IDCT_*` algorithms (`avcodec.h:1555-1567`; historical MPEG-4 encoders using Xvid/Walken IDCT similarly required `FF_IDCT_XVID` in `idctdsp.c:280` to avoid P-frame drift). Furthermore, inside `simple_idct_template.c:112-113, 167-216`, FFmpeg explicitly casts arithmetic operands to unsigned `(SUINT)` (`MUL`/`MAC`) because malformed DCT coefficients in untrusted bitstreams can exceed nominal `[-2048, 2047]` spectral bounds and otherwise trigger C signed `int32_t` overflow undefined behavior.

#### 4.2 Regime B: Normative Bit-Exact Integer Transforms & Mezzanine Scaled IDCTs (VC-1, ProRes, DNxHD)

- **VC-1 (SMPTE ST 421:2006, `vc1dsp.c:241-460`):** Eliminates statistical drift entirely by specifying exact integer matrices for `8x8` (`{12, 16, 6}` even, `{16, 15, 9, 4}` odd), `8x4`, `4x8`, and `4x4` (`{17, 22, 10}`) inverse transforms with explicit asymmetric rounding bias (`+64` on rows `0..3` and `+65` on rows `4..7` prior to `>> 7` in `vc1_inv_trans_8x8_c`, `vc1dsp.c:302-325`), paired with `vc1_v_overlap_c`/`vc1_h_overlap_c` (`vc1dsp.c:40-85`) and conditional `vc1_filter_line` (`vc1dsp.c:150-180`). Every compliant VC-1 implementation—scalar or SIMD (`x86`, `aarch64`, `riscv`)—must be **100% bit-exact**.
- **Apple ProRes (SMPTE RDD 36:2015, `proresdec.c`, `proresdsp.c:57-190`):** Reuses `simple_idct_template.c` at `10`-bit (`EXTRA_SHIFT`, `ROW_SHIFT=13, COL_SHIFT=18`), `12`-bit (`ROW_SHIFT=16, COL_SHIFT=17`), and `16`-bit ProRes RAW (`IN_IDCT_DEPTH=32`), clamping `10`-bit output to SMPTE legal code words `[4, 1019]` and `12`-bit output to `[4, 4091]` (`proresdsp.c:100-105`). Note a subtle overflow hazard in `prores_idct_10` and `prores_idct_12` (`proresdsp.c:60, 74`): `block[i] *= qmat[i]` multiplies two `int16_t` values via C `int` promotion and truncates back to `int16_t` (implementation-defined narrowing in C, **arithmetic panic in safe Rust** unless written with explicit `i32` widening or `wrapping_mul`), whereas `prores_idct_bayer_16` (`proresdsp.c:91`) explicitly writes `av_clip_int16(block[i] * (unsigned)qmat[i])`.

---

### 5. Intra Mezzanine, Lossless Predictive, HDR Tile, and Legacy Game Codec Families

`Basis: normative + source + derived`

Inspecting the primary source implementations of FFmpeg's non-`MPV` families exposes concrete memory-safety, arithmetic, and concurrency invariants required for clean-room reimplementation:

1. **MJPEG (`mjpegdec.c:311-960`):** `ff_mjpeg_decode_sof` (`line 311`) multiplexes baseline/extended sequential DCT (`SOF0`/`SOF1`), progressive multi-scan spectral-selection/successive-approximation DCT (`SOF2`, requiring persistent `int16_t (*blocks)[64]` coefficient buffers across scans, `lines 810, 916-933`), lossless spatial DPCM (`SOF3`, including `16`-bit Bayer DNG sub-formats, `lines 344, 502, 541`), and JPEG-LS (`s->ls`).
2. **PNG / APNG (`pngdec.c:250-435`, ISO/IEC 15948):** Decompresses `IDAT`/`fdAT` DEFLATE streams row-by-row into `s->crow_buf` (`1` filter-type byte + `row_size` payload bytes) and applies `Sub`, `Up`, `Average`, and `Paeth` reconstruction (`ff_png_filter_row`, `pngdec.c:263-316`) plus Adam7 7-pass interlacing (`lines 383-422`) and MNG/LOCO reversible green-subtraction (`deloco_rgb8`/`rgb16`, `lines 320-333`). Two concrete C hazards appear in `ff_png_filter_row`:
   - At `pngdec.c:276-280`, the `bpp == 4` `Sub` fast path casts `*(const int *)(src + i)` and `*(int *)(dst + i)` directly (`p = ((s & 0x7f7f7f7f) + (p & 0x7f7f7f7f)) ^ ((s ^ p) & 0x80808080)`), violating C strict aliasing and alignment rules unless `src` (`crow_buf + 1`) is explicitly `4`-byte aligned; in Rust this SWAR addition is cleanly and soundly expressed via `u32::from_ne_bytes` / `to_ne_bytes`.
   - At `pngdec.c:303-313`, SIMD `dsp->add_paeth_prediction` processes `4`-byte SIMD lanes even for `24`-bit RGB (`bpp == 3`), which would overwrite `1` byte past row end on the final pixel; `ff_png_filter_row` explicitly peels `int w = (bpp & 3) ? size - 3 : size;` before calling scalar `ff_png_add_paeth_prediction` on the final pixel.
3. **WebP (`webp.c:63-190`, RFC 9649):** Parses RIFF `VP8X`/`VP8 `/`VP8L`/`ALPH`/`ANIM`/`ANMF` chunks, delegating lossy intra keyframes to `ff_vp8_decode_frame` while implementing standalone `VP8L` lossless decoding internally via recursive `ImageRole` sub-images (`IMAGE_ROLE_ARGB`, `ENTROPY`, `PREDICTOR` with `14` spatial modes `PRED_MODE_BLACK..PRED_MODE_ADD_SUBTRACT_HALF`, `COLOR_TRANSFORM`, and `COLOR_INDEXING` palette expansion, `webp.c:119-177`) plus 2D LZ77 backward-distance offsets (`lz77_distance_offsets[120]`, `webp.c:89-105`) and color-cache hashing (`MAX_CACHE_BITS = 11`).
4. **OpenEXR (`exr.c:70-195`, `exrdsp.c:27-69`):** Supports arbitrary `EXRChannel` lists (`EXR_UINT`, `EXR_HALF` IEEE-754 binary16, `EXR_FLOAT` binary32), scanline blocks and mipmap/ripmap tiles (`EXRTileAttribute`), and compression modes (`NONE`, `RLE`, `ZIPS`, `ZIP`, `PIZ` 2D Haar wavelet + 16-bit `HuffEntry` canonical Huffman, `PXR24`, `B44`/`B44A` `4x4` half-float block compression, and `DWAA`/`DWAB` lossy DCT). `ExrDSPContext` (`exrdsp.c:27-68`, accelerated on `x86` SSE2/AVX2 and `riscv` RVV) isolates the two universal `ZIP`/`ZIPS`/`RLE` post-inflate kernels: `predictor_scalar` (byte delta `src[i] + src[i-1] - 128` encoded via `^ 0x80`) and `reorder_pixels_scalar` (interleaving split high-byte and low-byte halves `src[0..size/2]` and `src[size/2..size]`). Note that `predictor_scalar` (`exrdsp.c:44`) accesses `src[1]` unconditionally when `(size & 1) == 0`, requiring callers to reject `size == 0` prior to invocation.
5. **FFV1 (`ffv1.h:45-145`, `ffv1dec.c:60-235`, RFC 9043) and UtVideo (`utvideodec.c:50-185`):**
   - FFV1 partitions frames into up to `MAX_SLICES = 1024` independent slices (`FFV1SliceContext`, `ffv1.h:71-124`) with per-slice CRC-32 integrity footers, `AC_GOLOMB_RICE` (rejecting `slice_width >= (1 << 23)` at `ffv1dec.c:210` to prevent `run_index` / Golomb state overflow) or `RangeCoder` (`AC_RANGE_DEFAULT_TAB` / `AC_RANGE_CUSTOM_TAB`), quantized gradient context modeling (`MAX_QUANT_TABLES = 8`), reversible YCgCo-style RGB color transform (`slice_rct_by_coef`, `slice_rct_ry_coef`), and `16`/`32`-bit float remapping tables (`fltmap`/`fltmap32`, `ffv1dec.c:112-160`). Notice `ffv1dec.c:121-136` allocates a `2 * (w + 6)` ring buffer with `3`-element left/right border sentinels (`sample[0] = sc->sample_buffer + 3`) so causal `2D` context reads `sample[p][-1]`, `sample[p][-2]`, and `sample[0][x + 1]` are unconditionally in-bounds without per-pixel edge branches.
   - UtVideo (`utvideodec.c:77-140`) builds canonical length-sorted Huffman tables per plane (`build_huff`, using `VLC_MULTI` up to `6` symbols per lookup via `ff_vlc_init_multi_from_lengths` at `line 113`, handling degenerate single-symbol zero-length trees via `*fsym = i` fill at `lines 86-88, 159-180`) and applies modular left/median/gradient prediction via `LLVidDSPContext`.
6. **Legacy Game, Broadcast, and GPU Texture Long Tail (`texturedsp.h`, `bink.c`, `smacker.c`, `cinepak.c`, `qtrle.c`):**
   - `TextureDSPContext` (`texturedsp.h:42-61`) unifies `15` `4x4`-pixel block decompressors (`dxt1..dxt5ys`, `rgtc1s..rgtc2u`, `dxn3dc`) outputting `AV_PIX_FMT_RGBA` across `hap`, `dxv`, `dds`, `tdsc`, and `rasc` via slice-threaded `TextureDSPThreadContext`—a pure stateless `(&[u8; 8|16]) -> [[u8; 4]; 16]` function family with zero inter-block state.
   - `BinkContext` (`bink.c:104-130, 292-510`) decodes `BINKB_NB_SRC` typed symbol queues (`Bundle` buffers for block types, runs, motion offsets, `8x8` DCT DCs, patterns, and colors) per plane; `Smacker` (`smacker.c:39, 142-190, 356-362`) recursively decodes `16`-bit compound `bigtree` Huffman structures (`SMK_NODE = 0x80000000`) guarded by explicit recursion-depth and node-count limits; `Cinepak` (`cinepak.c:46-74, 188-216`) indexes `256`-entry `cvid_codebook[12]` arrays directly by `uint8_t` byte (`strip->v4_codebook[*data++]`—trivially in-bounds on `[0..255]`, requiring only initialized codebook state on strip `0` and destination tile bounds); and `QTRLE` (`qtrle.c:58-110`) runs `GetByteContext`-backed skip/repeat RLE guarded by `CHECK_PIXEL_PTR(...)` before every write span.

---

### 6. Verification Priority Stack and Clean-Rewrite Modularity Implications

`Basis: derived`

Mapping the findings above onto a clean-room verified Rust media architecture ordered by (1) UB-freedom, (2) panic-freedom, (3) behavioral/SIMD equivalence, and (4) full standard conformance yields concrete design rules:

1. **Priority 1 — UB-freedom (100% safe Rust for long-tail syntax; tiny isolated SIMD trait boundary):**
   - None of the `~270` long-tail parsers, entropy decoders, predictors, RLE/VQ engines, or coefficient loops require `unsafe` code once three C idioms are retired: (a) replace `UNCHECKED_BITSTREAM_READER` + `64`-byte zero-padding preconditions with a safe `BitReader<'a>` holding a `u64` bit reservoir refilled via bounds-checked `slice.get(pos..pos+8)` (`u64::from_be_bytes` / `from_le_bytes`) with byte-by-byte tail fallback (1 predicted check per `56` consumed bits, zero padding allocation required); (b) pass integer coordinates `(src_x, src_y)` and plane slice descriptors into `emulated_edge_mc` instead of pre-offset out-of-bounds pointers; and (c) replace raw pointer casts in `pngdec.c:276` and `ffv1dec.c:154` with typed slice views and SWAR integer operations.
   - Restrict `unsafe` / verified assembly strictly to stateless fixed-shape kernels (`IDCT 8x8`, `VC-1 8x8/8x4/4x8/4x4`, `Hpel/Qpel 16xH/8xH`, `LLVidDSP` row prefix sums, `PNG Paeth`, `ExrDSP` reorder/predictor) whose spatial memory footprints are statically known (`[i16; 64]`, `&mut [u8]` row slices of verified length).
2. **Priority 2 — Panic-freedom on adversarial bitstreams:**
   - Replace implicit C signed-to-unsigned `(SUINT)` / `(unsigned)` casts (`simple_idct_template.c:112`, `proresdsp.c:60, 91`, `flacdsp.c:51`) with explicit Rust `wrapping_add` / `wrapping_mul` (where modular 2's-complement semantics is intended, as in PNG/FFV1/UtVideo `2^b` predictors and IDCT intermediate butterflies) or widened `i32`/`i64` saturating arithmetic.
   - Encode `VLC` table well-formedness as a type-level invariant constructed once by `VlcTable::build(...)`: every entry is either `Leaf { sym, bits: 1..=25 }`, `Subtable { offset, width: 1..=11 }` with `offset + (1 << width) <= table.len()`, or `Invalid` returning `Err(InvalidBitstream)` immediately (forbidding `0`-bit `SKIP_BITS` livelocks).
3. **Priority 3 — Behavioral equivalence to FFmpeg & SIMD-vs-scalar equivalence:**
   - Because FFmpeg sets default `FF_IDCT_AUTO` (`idctdsp.c:284`, `x86/idctdsp_init.c:86`, `aarch64/idctdsp_init_aarch64.c:41`) to `simple_idct` across `x86_64`, `aarch64`, and scalar C, pinning the clean rewrite's canonical 8/10/12-bit MPEG/MJPEG/DNxHD/ProRes IDCT to `simple_idct` enables **bit-exact differential FATE testing** against upstream FFmpeg AND **machine-checked bit-exact SIMD-vs-scalar equivalence** modulo the static bijective scantable permutation $\pi_{\text{perm}}$:
     $$\forall B \in \mathtt{i16}^{64},\; \mathrm{idct\_simd}(\pi_{\text{perm}}(B)) = \mathrm{idct\_scalar}(B) \quad \land \quad \pi_{\text{perm}}(0) = 0 \;\land\; \pi_{\text{perm}}(63) = 63.$$
4. **Priority 4 — Full functional specification conformance:**
   - For Regime B standards (VC-1 SMPTE ST 421M, FFV1 RFC 9043, PNG ISO 15948, WebP VP8L RFC 9649, UtVideo, OpenEXR lossless modes), functional spec conformance coincides with bit-exactness.
   - For Regime A standards (ITU-T H.262, ISO/IEC 14496-2, ISO/IEC 23002-1), proving that scalar `simple_idct` satisfies the ISO/IEC 23002-1 empirical/statistical test suite (`PPE <= 1`, `PMSE <= 0.06`, `OMSE <= 0.02`, `PME <= 0.015`, `OME <= 0.0015`, `idct(0) = 0`) plus proving exact bit-equivalence of all SIMD backends to `simple_idct` discharges both normative compliance and cross-ISA determinism simultaneously.

## Boundaries

The following boundaries separate established evidence in this report from unexamined, unknown, or non-applicable cases:

- **Modern flagship block-coding pipelines (`not examined` here):** H.264/AVC (`h264dec.c`), HEVC (`hevc/`), VVC (`vvc/`), and AV1 (`dav1d` / `cbs_av1`) employ context-adaptive binary/multi-symbol arithmetic coding (CABAC/rANS), complex reference picture list management, and multi-stage in-loop filters (SAO, ALF, CDEF, loop restoration) distinct from the `MpegEncContext` and intra/lossless long-tail families analyzed here.
- **Hardware decode acceleration (`known not to apply` to software `IDCTDSPContext` bit-exactness):** Decoding MPEG-2, MPEG-4, VC-1, MJPEG, or ProRes via `VA-API`, `VDPAU`, `NVDEC`, `D3D11VA`/`D3D12VA`, `VideoToolbox`, or `Vulkan Video` delegates inverse transforms and motion compensation to fixed-function vendor silicon. For Regime A codecs (MPEG-2, MPEG-4, MJPEG), hardware ASICs implement vendor-proprietary ISO/IEC 23002-1 IDCT approximations that are **known not to apply** to `simple_idct` bit-exactness (differing by $\pm 1$ LSB on ~50% of blocks, matching our `simple_idct` vs. `faanidct` result).
- **Encoder rate-distortion and motion-estimation search (`not examined` in full):** While shared DSP primitives (`fdctdsp`, `pixblockdsp`, `me_cmp`, `llvidencdsp`, `texturedspenc`, `RangeCoder` encoding) were inspected at interface level, encoder psycho-visual rate control (`ratecontrol.c`), motion estimation diamond/EPZS search heuristics (`motion_est.c`), and trellis quantization optimality are outside this decoder-and-kernel architecture scope.
- **End-to-end throughput benchmarks of full FFmpeg codecs (`not examined` via execution):** In light-mode capsule verification, full `FFmpeg` binary compilation and multi-stream FATE wall-clock benchmarking were not executed; execution evidence is strictly scoped to the standalone C transform conformance and divergence probe documented under **Evidence**, and architectural/SIMD conclusions rely on direct source inspection (`Basis: source + derived`).
- **OpenEXR `DWAA`/`DWAB` floating-point lossy compression (`unknown` cross-ISA bit-exactness):** `exr.c` decodes `DWAA`/`DWAB` blocks using `float block[3][64]` (`exr.c:135`) and floating-point color/DCT reconstruction; exact ULP determinism across FMA vs. non-FMA targets for `DWAA`/`DWAB` was not empirically measured in this investigation.

## Evidence

### Primary Repository Source Citations (`FFmpeg/FFmpeg` @ `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`)

- **Codec registry, IDs, and build-system dependency closure:**
  - `libavcodec/codec_id.h:47-602` (`enum AVCodecID`: `276` video/image IDs, `226` audio IDs, `27` subtitle IDs).
  - `libavcodec/allcodecs.c:32-890` (`883` `FFCodec` extern declarations: `610` decoders, `273` encoders).
  - `libavcodec/defs.h:40` (`#define AV_INPUT_BUFFER_PADDING_SIZE 64`).
  - `configure` (`220` `*_decoder_select` rules establishing transitive counts: `idctdsp=54`, `blockdsp=53`, `videodsp=46`, `hpeldsp=40`, `bswapdsp=35`, `h264chroma=32`, `mpegvideodec=24`, `golomb=20`, `inflate_wrapper=16`, `jpegtables=15`, `mjpeg_decoder=11`, `h263_decoder=11`, `qpeldsp=9`, `llviddsp=8`, `vp3dsp=7`, `texturedsp=6`).
- **Bitstream, VLC, and Range-Coder primitives:**
  - `libavcodec/get_bits.h:52-55, 109-287, 337-409, 517-658` (`UNCHECKED_BITSTREAM_READER`, `GetBitContext`, `size_in_bits_plus8`, `UPDATE_CACHE_BE_32`, `GET_VLC`, `GET_RL_VLC`).
  - `libavcodec/vlc.h:27-160` (`VLCElem`, `VLC`, `VLC_MULTI`, `ff_vlc_init_sparse`, `ff_vlc_init_from_lengths`).
  - `libavcodec/bytestream.h:33-220` (`GetByteContext`, `PutByteContext`, saturating `bytestream2_get_*` vs. unchecked `*u`).
  - `libavcodec/rangecoder.h:35-136` and `libavcodec/rangecoder.c:42-120` (`RangeCoder`, `MAX_OVERREAD`, `ff_init_range_decoder` `0xFF00` clamp, `ff_build_rac_states`, `get_rac`, `renorm_encoder`).
- **Shared DSP contexts and ISA backends:**
  - `libavcodec/idctdsp.h:27-113`, `libavcodec/idctdsp.c:30-314`, `libavcodec/avcodec.h:1555-1567` (`FF_IDCT_*`, `IDCTDSPContext`, `ff_permute_scantable`, `ff_init_scantable_permutation`).
  - `libavcodec/simple_idct_template.c:46-285`, `libavcodec/faanidct.c:27-160`, `libavcodec/x86/idctdsp_init.c:29-153`, `libavcodec/aarch64/idctdsp_init_aarch64.c:34-55`, `libavcodec/riscv/idctdsp_init.c:36-48`.
  - `libavcodec/videodsp.h:32-80`, `libavcodec/videodsp_template.c:24-102` (`emulated_edge_mc` pointer back-tracking on out-of-bounds `src_x`/`src_y`).
  - `libavcodec/hpeldsp.h:46-106`, `libavcodec/lossless_videodsp.h:28-47`, `libavcodec/bswapdsp.h:24-32`, `libavcodec/texturedsp.h:42-96`, `libavcodec/exrdsp.c:27-69`.
- **Representative long-tail codec implementations:**
  - `libavcodec/mpegvideo.h:48-165`, `libavcodec/mpeg12dec.c:30, 132-390`, `libavcodec/mpeg4videodec.c:23, 2162-2268` (`MpegEncContext`, MPEG-1 oddification vs. MPEG-2/MPEG-4 `block[63] ^= mismatch & 1`).
  - `libavcodec/vc1dsp.c:40-180, 241-420` (exact integer `8x8`/`8x4`/`4x8` inverse transforms, overlap filter, loop filter).
  - `libavcodec/proresdec.c:80-190`, `libavcodec/proresdsp.c:31-190` (`10`/`12`/`16`-bit scaled `simple_idct`, `[4, 1019]`/`[4, 4091]` legal clipping, `block[i] *= qmat[i]` narrowing).
  - `libavcodec/dnxhddec.c:35, 115-670`, `libavcodec/dnxhddata.h:40-60`, `libavcodec/dnxhddata.c:980-1108` (`UNCHECKED_BITSTREAM_READER`, `DNXHD_VARIABLE`, Kraft-complete AC/run tables with `code(0) -> index 0 != eob_index`).
  - `libavcodec/mjpegdec.c:311-940`, `libavcodec/pngdec.c:250-430`, `libavcodec/webp.c:63-185`, `libavcodec/exr.c:70-195`, `libavcodec/ffv1.h:45-140`, `libavcodec/ffv1dec.c:60-230`, `libavcodec/utvideodec.c:31, 50-180`, `libavcodec/bink.c:104-510`, `libavcodec/smacker.c:39-362`, `libavcodec/cinepak.c:46-318`, `libavcodec/qtrle.c:58-110`.

### Reproducible Execution Evidence (IEEE 1180 / ISO 23002-1 IDCT Conformance & Divergence Probe)

Observed on `2026-11-20` on Linux `x86_64` with `gcc (Debian 15.2.0-14) 15.2.0` (`gcc -O2 probe_idct_1180.c -lm`). The standalone probe implements the exact IEEE Std 1180-1990 §5 linear congruential generator (`seed = (seed * 1103515245 + 12345) & 0x7fffffff`), 64-bit `double` forward/inverse reference DCTs, FFmpeg's exact 8-bit `simple_idct` (`W1=22725..W7=4520`, `ROW_SHIFT=11`, `COL_SHIFT=20`), and FFmpeg's `faanidct` (`B0..B7`, `A2`, `A4`), producing:

```text
Range [-256,255] N=10000:
  simple_idct: PPE=1 PMSE=0.014400 OMSE=0.010994 PME=0.003000 OME=0.000106
  faanidct   : PPE=1 PMSE=0.000100 OMSE=0.000022 PME=0.000100 OME=0.000009
  simple vs faan: diff_blocks=5072/10000 (50.72%), diff_samples=7038/640000 (1.10%), max_diff=1
Range [-300,300] N=10000:
  simple_idct: PPE=1 PMSE=0.013700 OMSE=0.010736 PME=0.003300 OME=0.000027
  faanidct   : PPE=1 PMSE=0.000100 OMSE=0.000014 PME=0.000100 OME=0.000005
  simple vs faan: diff_blocks=4982/10000 (49.82%), diff_samples=6872/640000 (1.07%), max_diff=1
All-zero exact: PASS
```

## Revalidation

To revalidate the material claims of this report against a newer `FFmpeg/FFmpeg` revision `<NEW_SHA>` in under 15 seconds without building FFmpeg:

1. **Re-verify shared DSP transitive dependency counts and `AV_INPUT_BUFFER_PADDING_SIZE`:**
    Fetch `configure` and `libavcodec/defs.h` from `https://raw.githubusercontent.com/FFmpeg/FFmpeg/<NEW_SHA>/...`, confirm `AV_INPUT_BUFFER_PADDING_SIZE` in `defs.h`, and compute the transitive closure over `^([a-z0-9_]+)_select="([^"]*)"` for all `*_decoder` keys. Significant drops in `idctdsp`, `videodsp`, `hpeldsp`, or `mpegvideodec` counts indicate architectural refactoring of `MpegEncContext` or DSP dispatch.
2. **Re-verify `IDCTDSPContext` permutation fixed points (`0` and `63`) and `emulated_edge_mc` calling convention:**
    Diff `libavcodec/idctdsp.c`, `libavcodec/x86/idctdsp_init.c`, `libavcodec/aarch64/idctdsp_init_aarch64.c`, `libavcodec/riscv/idctdsp_init.c`, and `libavcodec/videodsp_template.c` against `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`. Confirm every `FF_IDCT_PERM_*` formula maps `0 -> 0` and `63 -> 63`, and check whether `emulated_edge_mc` still receives pre-offset out-of-bounds `src` pointers or has migrated to plane-base + coordinate parameters.
3. **Re-verify `UNCHECKED_BITSTREAM_READER` and DNxHD/DNxHR zero-padding termination:**
    Diff `libavcodec/get_bits.h`, `libavcodec/dnxhddec.c`, and `libavcodec/dnxhddata.c`. If any new `cid_table` AC Huffman table is added to `dnxhddata.c` while `dnxhddec.c` retains `#define UNCHECKED_BITSTREAM_READER 1` without `get_bits_left` checks in `dnxhd_decode_row`, verify via Kraft sum ($\sum 2^{-\ell_k} = 1$) and zero-codeword lookup (`ac_codes[idx] == 0` implies `idx != eob_index`) that zero-padded packet tails still terminate within `512` bits.
4. **Re-run the IEEE 1180 / ISO 23002-1 accuracy probe:**
    If `W1..W7` or shift constants in `libavcodec/simple_idct_template.c` change, re-run the `10,000`-block IEEE 1180 §5 C harness against 64-bit floating-point reference DCT/IDCT and confirm `PPE <= 1`, `PMSE <= 0.06`, `OMSE <= 0.02`, `PME <= 0.015`, `OME <= 0.0015`, and all-zero exactness.
