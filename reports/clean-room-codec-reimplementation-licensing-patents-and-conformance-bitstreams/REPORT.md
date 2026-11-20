# Clean-Room Media Codec Reimplementation, Patent and Copyleft Boundaries, Drop-In `libav*` ABI Compatibility, and Normative Conformance Suites

## Summary

Reimplementing a multimedia codec and demuxer stack in memory-safe Rust—with optional drop-in compatibility for FFmpeg's `libav*` C ABI—requires keeping three orthogonal axes separate: copyright derivation, utility patent encumbrance, and normative conformance oracles. Grounded in pinned upstream sources (`FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, `xiph/opus@31b4b36284394b66a4c9d7352991aa977dfc8bc1`, `xiph/flac@59fa3402cb19b6b7c85b916f138cfb03c7b27504`, `ietf-wg-cellar/flac-test-files@aa7b0c6cf32994c106ae517a08134c28a96ff5b2`, `webmproject/libvpx@18656c27cf3bee114562297274b64a84d0a6187c`, `AOMediaCodec/av1-spec@5e04f3f75e73a5898d7616c47c52f032144b8f80`, `AOMediaCodec/SVT-AV1@462771f87694e959cc1d3f9addde23d7015662e3`, `cisco/openh264@78783f195ce116ecbaea83f7fac0ea8a355518b5`, `mstorsjo/fdk-aac@ec82feb39662ac77e24ee9b324d5962e91bc79c5`, `fraunhoferhhi/vvdec@8909ff880412629bdd31e87a9f68d652db89479c`, `pdeljanov/Symphonia@5f879df0bf309246a48d57caae457fd8c0e2a5cb`, `memorysafety/rav1d@2e7216c20ac2a75de204d6c8d7268b75a45959b4`) and ITU-T, ISO/IEC, and IETF standards:

1. **Mechanical translation preserves upstream copyright; clean-room specification authoring breaks it.** Direct ports or `c2rust` transpilation (exemplified by `rav1d`'s port from `dav1d`, which retains the BSD-2-Clause copyright chain in `COPYING:1-24`) remain derivative works of the C source under copyright law. Obtaining an unencumbered permissive license (`Apache-2.0 OR MIT`) when replacing `LGPLv2.1+`/`GPLv2+` components (`FFmpeg/LICENSE.md:3-11`) requires clean-room reimplementation from normative standards (ITU-T, ISO/IEC, IETF RFCs) and black-box conformance vectors rather than inspecting copyleft C bodies, matching the specification-driven model of `Symphonia` (`#![forbid(unsafe_code)]`, MPL-2.0).
2. **Copyright independence does not neutralize codec utility patents.** Permissively licensed source implementations (`BSD-2-Clause`, `Clear BSD`, `MIT`, `Apache-2.0`) routinely remain subject to standard-essential patent (SEP) pools. `VVdeC`'s Clear BSD `LICENSE.txt:21` and `FDK-AAC`'s `NOTICE:60-68` explicitly disclaim any patent grant; `SVT-AV1` (`PATENTS.md:5-44`) attaches the royalty-free Alliance for Open Media Patent License 1.0 with defensive termination; and `OpenH264` relies on Cisco's pre-built binary plugin distribution to cap MPEG LA H.264 royalties for end users.
3. **Exposing a permissive drop-in `libav*` C ABI requires `Apache-2.0 OR MIT` dual licensing and clean-room ABI header synthesis.** Upstream `FFmpeg/LICENSE.md:108-111` explicitly documents that `Apache-2.0` alone is incompatible with `LGPLv2.1` and `GPLv2` (forcing `--enable-version3` to upgrade to `(L)GPLv3`). A clean-room Rust library targeting drop-in `libavcodec.so` / `libavutil.so` / `libavformat.so` replacement must dual-license `Apache-2.0 OR MIT`, generate C headers independently from documented ABI field offsets/signatures rather than copying `LGPL` FFmpeg `.h` files verbatim, and replace coherent library clusters because `libavcodec.v:5` exports private cross-library `avpriv_*` symbols.
4. **Normative codec conformance splits into three mutually distinct oracle classes.** Bit-exact MD5/CRC frame hashes govern modern integer-transform video codecs (`ITU-T H.264.1`, `H.265.1`, `H.266.1`, `AV1` Argon Streams, `VP9`) and lossless audio (`RFC 9639` FLAC); statistical RMS + peak-LSB error envelopes govern floating/fixed-point lossy transform audio (`ISO/IEC 14496-4` AAC); and psychoacoustic Bark-band masking (`xiph/opus` `src/opus_compare.c`) governs `RFC 6716`/`RFC 8251` Opus.
5. **FFmpeg `FATE` mixes GPL test harnesses (`tiny_ssim.c`, `checkasm`) with an unbundled third-party sample archive (`fate-suite`).** Clean-room projects cannot vendor `fate-suite.ffmpeg.org` assets into a permissive repository; they must consume `FATE` strictly as an external out-of-tree differential oracle alongside redistributable ITU/IETF/AOM/CC0 vectors and deterministic synthetic generators.

---

## Applicability

This report governs clean-room media codec reimplementation, licensing/patent isolation, `libav*` C ABI interoperability, and normative conformance test integration across the 15 primary subjects recorded in `REPORT.json`:

- **FFmpeg Licensing, Build Gates, ABI Scripts, and FATE Harness (`FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`):** Applies to `LICENSE.md`, `COPYING.LGPLv2.1`, `COPYING.GPLv2`, `configure` (`--enable-gpl`, `--enable-version3`, `--enable-nonfree`), `libavcodec/{version_major.h,libavcodec.v,packet.h,avcodec.h}`, `libavformat/libavformat.v`, `libavutil/libavutil.v`, `doc/fate.texi`, and `tests/fate-run.sh` (`LIBAVCODEC_VERSION_MAJOR == 63`).
- **Normative Conformance & Test Vector Repositories:** Covers `ITU-T H.264.1 / H.265.1 / H.266.1`, `AOMediaCodec/av1-spec@5e04f3f75e73a5898d7616c47c52f032144b8f80` + Argon Streams AV1, `webmproject/libvpx@18656c27cf3bee114562297274b64a84d0a6187c` (`test/test-data.sha1`), `ISO/IEC 14496-4:2004` (AAC) + `ISO/IEC 14496-12` (ISOBMFF), `xiph/flac@59fa3402cb19b6b7c85b916f138cfb03c7b27504` + `ietf-wg-cellar/flac-test-files@aa7b0c6cf32994c106ae517a08134c28a96ff5b2` (`RFC 9639`), and `xiph/opus@31b4b36284394b66a4c9d7352991aa977dfc8bc1` (`RFC 6716`, `RFC 8251`, `src/opus_compare.c`, `tests/run_vectors.sh`).
- **Reference Codec Copyright/Patent Terms & Clean-Room Precedents:** Covers `AOMediaCodec/SVT-AV1@462771f87694e959cc1d3f9addde23d7015662e3` (`PATENTS.md`), `cisco/openh264@78783f195ce116ecbaea83f7fac0ea8a355518b5`, `mstorsjo/fdk-aac@ec82feb39662ac77e24ee9b324d5962e91bc79c5`, `fraunhoferhhi/vvdec@8909ff880412629bdd31e87a9f68d652db89479c`, `pdeljanov/Symphonia@5f879df0bf309246a48d57caae457fd8c0e2a5cb`, and `memorysafety/rav1d@2e7216c20ac2a75de204d6c8d7268b75a45959b4`.

Related corpus reports treat C-to-Rust migration and ABI strangulation ([`incremental-c2rust-lifting-mvee-shadow-execution-and-ffi-strangulation`](../incremental-c2rust-lifting-mvee-shadow-execution-and-ffi-strangulation/REPORT.md)), C calling conventions ([`c-abi-stack-conventions-and-process-interface-archaeology`](../c-abi-stack-conventions-and-process-interface-archaeology/REPORT.md)), entropy-coded bitstream hazards ([`entropy-coded-media-bitstreams-video-codec-security-and-simd-decoders`](../entropy-coded-media-bitstreams-video-codec-security-and-simd-decoders/REPORT.md)), and Opus/FLAC DSP arithmetic ([`webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows`](../webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows/REPORT.md)). All claims here describe technical and license-text structure observed in primary artifacts and do not constitute formal legal advice.

---

## Findings

### 1. Clean-Room Specification Synthesis vs. Mechanical Porting (`rav1d`, `Symphonia`, `FFmpeg`)

Basis: source (`memorysafety/rav1d@2e7216c2`: `COPYING:1-24`, `pdeljanov/Symphonia@5f879df0`: `README.md:38-75`, `symphonia-core/src/lib.rs:1-19`, `FFmpeg/FFmpeg@7ddf7bc8`: `LICENSE.md:1-75`) + derived.

Under software copyright law, mechanical C-to-Rust transpilation (`c2rust`) or line-by-line structural translation preserves expressive control flow, constant tables, and internal module factoring, creating a **derivative work** bound by the original source copyright license:

- **Direct Translation Inheriting Permissive Terms (`rav1d`):** `memorysafety/rav1d` explicitly started from `c2rust` translation of VideoLAN's `dav1d` and progressively refactored toward safe Rust. Consequently, `rav1d`'s `COPYING:1-24` carries forward the original `Copyright © 2018-2019, VideoLAN and dav1d authors` BSD-2-Clause notice alongside `2023-2024 ... Internet Security Research Group`. This inheritance succeeds for `dav1d` because `dav1d` itself is BSD-2-Clause; performing the identical mechanical process on `FFmpeg` (`LGPLv2.1+`) or `x264`/`x265` (`GPLv2+`) would permanently encumber the resulting Rust crate under `(L)GPL`, blocking permissive (`Apache-2.0 OR MIT`) distribution.
- **Specification-Driven Clean-Room Architecture (`Symphonia` + Two-Team Isolation):** `Symphonia` (`pdeljanov/Symphonia@5f879df0`, MPL-2.0, `#![forbid(unsafe_code)]` at `symphonia-core/src/lib.rs:7`) demonstrates clean-room Rust authoring from published codec standards and black-box differential comparison against `ffmpeg` (`README.md:74`). When reimplementing codecs whose primary documentation is fragmented across legacy C code (`FFmpeg`) and international standards (ITU-T, ISO/IEC, IETF), a strict **two-team clean-room boundary** prevents copyright contamination:
  1. **Specification & Oracle Team (dirty room):** Reads `FFmpeg` C sources, normative standards, and bug trackers solely to extract **written algorithmic specifications** (exact bitstream syntax, integer rounding rules, error-concealment edge behaviors, C ABI struct layouts) and **black-box conformance bitstreams / reference PCM or YUV hashes**, never emitting Rust or C implementation fragments across the barrier.
  2. **Implementation & Proof Team (clean room):** Authors idiomatic, modular Rust and formal safety/equivalence proofs solely from the specification dossier and runs against black-box conformance suites and differential `FFmpeg` binaries.
- **Distinguishing Legacy C Historical Accident from Algorithmic/Hardware Necessity:**
  - *Historical accident in `FFmpeg` C:* Monolithic mutable state structs (`AVCodecContext` spanning `libavcodec/avcodec.h:443-1958`, >1,500 lines of mixed decoder/encoder/internal/deprecated fields), `#ifdef CHECKED` `SUINT` signed-vs-unsigned UB workarounds (`libavutil/internal.h:133-141`), C preprocessor template re-inclusion (`bit_depth_template.c` included repeatedly with `#undef` macros), and global static codec registration tables. None of these are required by codec mathematics or hardware; a clean Rust rewrite separates immutable stream configuration (`SequenceHeader`/`SPS`/`PPS`), per-frame decoded picture buffers (DPB), and entropy decoders into strongly typed state machines, exposing `AVCodecContext` only at a thin outer C-ABI adapter layer.
  - *Fundamental algorithmic/hardware constraints:* Reference-counted aligned plane buffers (`AVBufferRef`, padded by 32–64 bytes beyond `width`/`height` for SIMD vector loads and motion-compensation edge extension), explicit `linesize` strides, planar YUV memory layouts, and bit-exact integer transform matrices (`H.264`/`HEVC`/`VVC`/`AV1`) are dictated directly by SIMD microarchitecture and normative specifications.

### 2. Copyright Licenses vs. Codec Utility Patent Regimes

Basis: source (`FFmpeg/FFmpeg@7ddf7bc8`: `LICENSE.md:13-127`, `configure:98-101, 4829-4844, 7526`; `mstorsjo/fdk-aac@ec82feb3`: `NOTICE:1-92`; `AOMediaCodec/SVT-AV1@462771f8`: `PATENTS.md:1-107`; `fraunhoferhhi/vvdec@8909ff88`: `LICENSE.txt:1-32`; `cisco/openh264@78783f19`: `LICENSE:1-23`; `AOMediaCodec/av1-spec@5e04f3f7`: `LICENSE:1-40`; `xiph/opus@31b4b362`: `COPYING`; `xiph/flac@59fa3402`: `COPYING.Xiph`).

Clean-room source authorship resolves **copyright** ownership only; it grants **zero immunity** from standard-essential utility patents (SEPs) covering transform, intra/inter prediction, loop filtering, or perceptual coding methods defined by the codec standard itself. Primary license texts across the media ecosystem fall into five distinct copyright + patent regimes:

| Codec / Implementation | Pinned Copyright License | Explicit Patent Clause in Primary Source | Operational Distribution / Patent Consequence |
| :--- | :--- | :--- | :--- |
| **FFmpeg core** (`FFmpeg/FFmpeg`) | `LGPLv2.1+` default; `--enable-gpl` escalates to `GPLv2+`; `--enable-version3` upgrades to `(L)GPLv3` (`LICENSE.md:3-11, 61-64`; `configure:98-101`) | `GPLv2` §7 / `LGPLv2.1` §11 liberty-or-death patent conflict if encumbered; `GPLv3` §11 explicit patent grant from contributors; zero third-party SEP indemnity | Three GPL-only x86 asm/C files (`flac_dsp_gpl.asm`, `idct_mmx.c`, `vf_removegrain.asm`), `tests/checkasm/*`, `tests/tiny_ssim.c`, and 32 filters (`LICENSE.md:15-59`) remain isolated behind `--enable-gpl` |
| **Opus (`libopus`) & FLAC (`libFLAC`)** (`xiph/opus`, `xiph/flac`) | `BSD-3-Clause` (`COPYING`, `COPYING.Xiph` for `libFLAC`/`libFLAC++`; CLI `flac`/`metaflac` are `GPL` per `flac/README.md:47-51`) | Royalties waived / SEP holders granted open RF patent licenses during IETF standardization (`RFC 6716`, `RFC 9639`) | Safest baseline targets for unencumbered permissive (`Apache-2.0 OR MIT`) clean-room Rust reimplementation |
| **VP9 (`libvpx`) & AV1 (`SVT-AV1`, `rav1d`)** (`webmproject/libvpx`, `AOMediaCodec/SVT-AV1`, `memorysafety/rav1d`) | `BSD-3-Clause` (`libvpx`), `BSD-3-Clause-Clear` (`SVT-AV1`, `aom`), `BSD-2-Clause` (`rav1d`) | **Alliance for Open Media Patent License 1.0** (`SVT-AV1/PATENTS.md:5-44, 67-107`): perpetual worldwide royalty-free grant to Necessary Claims + defensive termination (`lines 34-43`); `PATENTS.md:20-27` requires reproducing the patent notice in source/binary distributions | Spec `Decoder`/`Encoder` conformance (`PATENTS.md:67-71`) is a precondition of the AOM Necessary Claims grant; clean-room AV1 codecs **must** pass conformance and preserve `PATENTS.md` notice |
| **H.264 (`OpenH264`)** (`cisco/openh264`) | `BSD-2-Clause` (`LICENSE:1-23`) | Source carries no patent grant; Cisco covers MPEG LA (now Via LA) H.264 royalties solely on Cisco-built official binaries downloaded directly by end users | Compiling `openh264` from source or embedding clean-room H.264 inside commercial binaries bypasses Cisco's binary-download patent shield |
| **AAC (`FDK-AAC`) & VVC (`VVdeC`)** (`mstorsjo/fdk-aac`, `fraunhoferhhi/vvdec`) | `FDK-AAC`: custom Android notice forbidding copyright fees (`NOTICE:51-52`), marked `--enable-nonfree` in `FFmpeg/LICENSE.md:122-127`; `VVdeC`: Clear BSD (`LICENSE.txt:1-32`) | **Explicitly NO patent license:** `FDK-AAC/NOTICE:60-68` (*"NO EXPRESS OR IMPLIED LICENSES TO ANY PATENT CLAIMS"*); `VVdeC/LICENSE.txt:21` (*"NO EXPRESS OR IMPLIED LICENSES TO ANY PARTY'S PATENT RIGHTS ARE GRANTED"*) | Clean-room H.264, H.265/HEVC, H.266/VVC, and AAC code must isolate patent-encumbered modules behind optional feature flags (cf. `Symphonia` `README.md:56`) |

### 3. Permissive Clean-Room Licensing and Drop-In `libav*` C ABI Interoperability

Basis: source (`FFmpeg/FFmpeg@7ddf7bc8`: `LICENSE.md:84-127`, `configure:4829-4844, 7526`, `libavcodec/libavcodec.v:1-9`, `libavcodec/version_major.h:28-45`, `libavcodec/packet.h:578-650`, `libavformat/libavformat.v:1-6`, `libavutil/libavutil.v:1-6`) + derived.

Exposing a drop-in C ABI binary compatible with FFmpeg's shared libraries (`libavcodec.so.63`, `libavformat.so`, `libavutil.so` at `LIBAVCODEC_VERSION_MAJOR == 63`, `version_major.h:28`) introduces two critical engineering traps:

1. **Why `Apache-2.0` Alone Breaks `LGPLv2.1` / `GPLv2` Drop-In Linking (`FFmpeg/LICENSE.md:108-111`):**
   `FFmpeg/LICENSE.md:108-111` explicitly states:
   > *"The mbedTLS, RK MPI, OpenCORE, VisualOn and libastcenc libraries are under the Apache License 2.0. That license is incompatible with the LGPL v2.1 and the GPL v2, but not with version 3 of those licenses. So to combine these libraries with FFmpeg, the license version needs to be upgraded by passing `--enable-version3` to configure."*
   If a clean-room Rust codec library is licensed solely under `Apache-2.0`, downstream `GPLv2-only` applications or default `LGPLv2.1` builds cannot legally link against it as a drop-in `libavcodec` replacement without triggering GPLv2-vs-Apache-2.0 patent-clause incompatibility. **Dual-licensing the clean-room Rust crates under `Apache-2.0 OR MIT`** allows GPLv2/LGPLv2.1 consumers to elect `MIT` while preserving `Apache-2.0`'s explicit patent grant for permissive/Apache/GPLv3 consumers.
2. **Symbol Versioning and the `avpriv_*` Cross-Library ABI Trap (`libavcodec.v:1-9`):**
   Inspecting FFmpeg's linker version scripts reveals:
   - `libavcodec/libavcodec.v:1-9` exports `LIBAVCODEC_MAJOR { global: av_*; avcodec_*; avpriv_*; avsubtitle_free; local: *; };`, while `libavformat/libavformat.v` and `libavutil/libavutil.v` export `av*`.
   - `avpriv_*` symbols are **internal private entry points** exported dynamically solely so `libavformat.so` and `libavdevice.so` can invoke undocumented codec helpers in `libavcodec.so` (and vice versa across `libavutil.so`). Their signatures change freely without major-version bumps (`version_major.h:30-38`). Consequently, replacing `libavcodec.so` *alone* beneath an upstream `FFmpeg` `libavformat.so` fails immediately at dynamic link time unless all needed `avpriv_*` entry points are matched at the exact micro-revision—or the clean-room shim replaces the coherent `{libavutil, libavcodec, libavformat, libswresample, libswscale}` library boundary together.
   - Public ABI structs such as `AVPacket` (`libavcodec/packet.h:578-650`) explicitly warn that `sizeof(AVPacket)` is being retired from the public ABI once `FF_API_INIT_PACKET` (`version_major.h:40`) is dropped, requiring `av_packet_alloc()` / `av_packet_unref()` heap allocation and exact field ordering (`buf`, `pts`, `dts`, `data`, `size`, `stream_index`, `flags`, `side_data`, `side_data_elems`, `duration`, `pos`, `opaque`, `opaque_ref`, ...). Any clean-room C header must be **independently synthesized** (e.g., via Rust `#[repr(C)]` + `cbindgen`) from published ABI field specifications rather than copying FFmpeg's LGPL `.h` files.

### 4. Official Codec Conformance Suites and Three Normative Oracle Paradigms

Basis: normative (`ITU-T H.264.1`, `H.265.1`, `H.266.1`, `ISO/IEC 14496-4:2004`, `RFC 6716`, `RFC 8251`, `RFC 9639`) + source (`xiph/opus@31b4b362`: `src/opus_compare.c:88-381`, `tests/run_vectors.sh:36-120`; `webmproject/libvpx@18656c27`: `test/test-data.sha1:1-879`; `ietf-wg-cellar/flac-test-files@aa7b0c6c`: `README.txt:1-73`; `AOMediaCodec/av1-spec@5e04f3f7`: `LICENSE`).

Unlike generic byte parsers, media codecs specify conformance using **three incompatible mathematical oracle definitions**. Selecting the wrong oracle silently accepts broken decoders or falsely rejects compliant fixed-point transforms:

| Standard / Suite | Primary Source & Vector Origin | Conformance Oracle Class | Key Structural Coverage & Edge Cases |
| :--- | :--- | :--- | :--- |
| **H.264/AVC** (`ITU-T H.264.1`) | ITU-T Test Signal Database (electronic annex bitstreams + `.yuv` / MD5 logs) | **Bit-exact YUV MD5** (integer $4\times 4$ / $8\times 8$ IDCT, H.264 §8.5.12 eliminated IEEE 1180 IDCT mismatch drift) | Baseline, Main, High, High-10/4:2:2/4:4:4 profiles; POC wraparound, DPB bumping/MMCO, MBAFF/PAFF, `CABAC` vs `CAVLC` |
| **HEVC** (`ITU-T H.265.1`) & **VVC** (`ITU-T H.266.1`) | ITU-T Test Signal Database (`*.bit`, `*.opl` output picture logs, `*.yuv.md5`) | **Bit-exact YUV MD5 + Decoded Picture Hash SEI** (SEI payload type `132`: `MD5`, `CRC-16`, or checksum over cropped picture arrays) | Tiles, WPP, dependent slices, 10-bit Main10, SAO/ALF/LMCS (`VVC`), subpicture extraction, `OPL` picture-output order checks |
| **AV1** (`AOMediaCodec/av1-spec`, Argon Streams AV1, `libaom`) | AOMedia Argon Streams AV1 (open-sourced rule-based generator + 5–20 frame streams + `.md5` digests + spec equation coverage report) | **Bit-exact YUV MD5** (mandatory spec conformance under `PATENTS.md:67-68`) | Directed-random coverage of MSAC CDF extremes, film grain synthesis, CDEF, loop restoration, super-res, `warped` motion, max tile grids |
| **VP9** (`webmproject/libvpx`) | `libvpx/test/test-data.sha1` (`879` entries, e.g. `3eaf216d9fc8... *bus_352x288_420_f20_b8.yuv` + `invalid-vp90-*.ivf.res` MD5/SHA-1 manifests) | **Bit-exact frame MD5** on valid streams + explicit non-crash error handling on fuzzed `invalid-vp90-*` inputs | Intra/inter prediction, loop filter, segmentation, frame parallel resize, malformed header resilience |
| **AAC & ISOBMFF** (`ISO/IEC 14496-4:2004`, `14496-12`) | ISO/IEC 14496-4 electronic conformance vectors + `14496-5` reference software | **Statistical RMS + Peak LSB envelope** (for 16-bit lossy AAC: $\max_n \|e[n]\| \le 2^{-14}$ = $2\text{ LSB}_{16}$ and $\text{RMS}(e) \le 2^{-15}/\sqrt{12} \approx 8.81 \times 10^{-6}$; bit-exact only for lossless MPEG-4 ALS) | Fixed-point IMDCT/MDCT and QMF filterbanks (`HE-AAC` SBR/PS) cannot match double-precision `14496-5` bit-for-bit; unbiased rounding passes while $-1\text{ LSB}$ bias fails |
| **FLAC** (`RFC 9639`, `flac-test-files`) | `ietf-wg-cellar/flac-test-files` (`README.txt:18-73`: three CC0 groups `subset`, `uncommon`, `faulty`) | **Bit-exact PCM + `STREAMINFO` 128-bit MD5** (`RFC 9639` §8.2) | `subset` (baseline streamable audio), `uncommon` (`32-bit` PCM requiring `33-bit` stereo side channels & `64-bit` LPC accumulators), `faulty` (crash/hang resilience) |
| **Opus** (`RFC 6716`, `RFC 8251`) | `xiph/opus` `tests/run_vectors.sh:77-120` + `src/opus_compare.c:88-381` (`testvector01..12.{bit,dec,m.dec}`) | **Psychoacoustic Bark-band masking metric** ($Q \ge 0.0$ pass threshold, `opus_compare.c:370-380`) | Tolerates floating-point vs. `FIXED_POINT` rounding and `8 kHz` (`bin 79..81`) `SILK`/`CELT` crossover filter variance (`lines 352-353`); rejects audible `PVQ`/range-coder desynchronization; dual `.dec`/`m.dec` reference vectors cover `RFC 8251` errata (`run_vectors.sh:90-94`) |

Inspecting `xiph/opus@31b4b362` `src/opus_compare.c:153-381` exposes exact normative tolerances that naive bit-exact or raw-SNR audio tests miss:
- `opus_compare.c` windows `48 kHz` PCM into `480`-sample (`10 ms`) Hann frames stepped by `120` samples (`2.5 ms`) across `21` Bark-scaled bands (`BANDS[0..21]` spanning bins `0..200`, up to `20 kHz`), applying `+10 dB/Bark` upward spectral masking (`0.1`, `line 265`), `-15 dB/Bark` downward masking (`0.03`, `line 272`), `-3 dB / 2.5 ms` temporal forward masking (`0.5`, `line 280`), and `0.01` stereo cross-talk (`lines 290-291`).
- At `lines 350-353`, `opus_compare.c` explicitly scales distortion by `0.1` across bins `79..81` (and `0.01` total at `xj == 80`, exact `8.0 kHz` `SILK`/`CELT` crossover) to permit mode freedom in hybrid resampling filters without failing conformance, before aggregating via an $L^{16}$ frame norm (`pow(err/nframes, 1.0/16)`, `line 369`) into $Q = 100 \cdot (1 - 0.5 \ln(1 + \text{err}) / \ln(1.13))$. Any $Q \ge 0$ (`line 371`) passes.

### 5. FFmpeg `FATE` Architecture, Redistribution Limits, and Priority Mapping

Basis: source (`FFmpeg/FFmpeg@7ddf7bc8`: `doc/fate.texi:45-107, 192-216`, `tests/fate-run.sh:10-95, 194-260`, `LICENSE.md:19-25, 74`) + derived.

1. **Test Runner Oracles (`tests/fate-run.sh`):** FATE invokes `ffmpeg -bitexact -threads $threads -thread_type $thread_type -cpuflags $cpuflags` (`lines 194-201`) and checks outputs with:
   - Exact hash comparators (`md5`, `framemd5`, `framecrc` at `lines 213-238`),
   - Sample-wise bounded error via `tests/tiny_psnr` (`do_tiny_psnr`, `oneoff` checking `MAXDIFF <= fuzz`, and `stddev` checking RMS error `lines 66-91`), and
   - Random thread counts (`THREADS=random16`, `lines 37-43`) plus SIMD capability masking (`CPUFLAGS=mmx`, `avx2`, `neon`, `doc/fate.texi:273-299`).
   Note that `tests/checkasm/*` and `tests/tiny_ssim.c` are **GPLv2+** (`LICENSE.md:24-25`), meaning clean-room permissive projects must use independent Rust comparison binaries (e.g., pure-Rust `tiny_psnr` / `opus_compare` equivalents) rather than copying FATE C utilities.
2. **Sample Archive Licensing (`doc/fate.texi:192-216`):** The `fate-suite` dataset (`fate-suite.ffmpeg.org`, synced via `rsync`) is an append-only archive of heterogeneous third-party audio/video excerpts contributed over 20+ years (including commercial/broadcast sample clips without uniform permissive open-source licenses). **It must never be vendored into a permissively licensed repository.** Clean-room Rust projects should combine: (a) redistributable `CC0` / permissive vectors (`ietf-wg-cellar/flac-test-files`, `libvpx` vectors, RFC 6716 Opus vectors), (b) clean-room deterministic synthetic bitstream generators checked in-tree, and (c) opt-in CI differential jobs fetching `fate-suite` and ITU-T annexes out-of-tree at test time.
3. **Mapping onto the Four-Tier Verification Priority Stack:**
   - *Priority 1 (UB-freedom) & Priority 2 (Panic-freedom):* Exercised adversarially via `ietf-wg-cellar/flac-test-files` `faulty/`, `libvpx` `invalid-vp90-*`, `FATE` `run_with_patched_temp` header-corruption tests (`fate-run.sh:131-143`), and coverage-guided fuzzers.
   - *Priority 3 (Differential & SIMD Equivalence):* Enforced by `FATE` `CPUFLAGS` sweeps (`scalar` vs `AVX2`/`NEON`), `THREADS=random16` determinism, and formal relational equivalence (`SafeTwin`) over fixed-point kernels.
   - *Priority 4 (Normative Conformance):* Enforced by selecting the exact codec-specific oracle class (MD5 for integer video/FLAC, RMS/LSB for AAC, Bark-band masking for Opus) rather than assuming universal bit-exactness.

### 6. Execution Probe: Discriminating Power of Bit-Exact, RMS/LSB, and Psychoacoustic Oracles

Basis: execution (standalone three-oracle probe preserved in Evidence; Python 3.13, `x86_64` Linux).

Running the standalone three-oracle probe reproduced the exact rejection boundaries of each conformance class:

| Oracle Class | Test Stimulus | Measured Metric vs. Threshold | Outcome |
| :--- | :--- | :--- | :--- |
| **A. Bit-Exact MD5** (`64×64` 8-bit YUV420) | Identical frame vs. `+1 LSB` flip on 1 luma pixel (`byte[4095]`) | `ref = ef738759bc8150294d49d5ab0ca0eaa6`; `+1 LSB = c7cc0e752747b2be178e744898bbac8e` | `True` / **`False`** |
| **B. Statistical RMS + Peak LSB** (`ISO/IEC 14496-4`, $N=48000$) | Unbiased `round()` quantization noise vs. continuous float | `max_err = 1.525866e-05` ($\le 1.22 \times 10^{-4}$), `rms = 8.807934e-06` ($\le 8.809666 \times 10^{-6}$) | **PASS** |
| **B. Statistical RMS + Peak LSB** (`ISO/IEC 14496-4`, $N=48000$) | Unrounded `floor()` truncation vs. continuous float | `max_err = 3.051625e-05` ($1\text{ LSB}$!), `rms = 1.764914e-05` ($> 8.809666 \times 10^{-6}$) | **FAIL** |
| **B. Statistical RMS + Peak LSB** (`ISO/IEC 14496-4`, $N=48000$) | Sparse unbiased $\pm 1\text{ LSB}$ vs. Systematic $-1\text{ LSB}$ DC bias | Sparse: `max_lsb = 1`, `rms = 7.629395e-06` (**PASS**); Bias: `max_lsb = 1`, `rms = 3.051758e-05` (**FAIL**) | **PASS** / **FAIL** |
| **C. Bark-Band Masking** (`opus_compare.c` `48 kHz` mono) | $\pm 1\text{ LSB}$ fixed/float dither | `Q = 99.70%`, `err = 0.000725` ($Q \ge 0.0$ required) | **PASS** |
| **C. Bark-Band Masking** (`opus_compare.c` `48 kHz` mono) | `2500`-amplitude tone delta at `8 kHz` (`bin 80` crossover) | `Q = 53.86%`, `err = 0.119376` (attenuated $0.01\times$ by `lines 352-353`) | **PASS** |
| **C. Bark-Band Masking** (`opus_compare.c` `48 kHz` mono) | `2500`-amplitude tone delta at `12 kHz` (`bin 120`, unattenuated) | `Q = -49.94%`, `err = 0.442688` ($Q < 0.0$) | **FAIL** |

Crucially, in Oracle B, a `-1 LSB` truncation bias satisfies the `2 LSB` peak threshold (`max_lsb = 1 <= 2`) yet fails RMS conformance by $3.46\times$ (`3.051758e-05` vs `8.809666e-06`), demonstrating why fixed-point audio reimplementations require unbiased round-to-nearest shifts (`+ (1 << (s-1))`) rather than raw truncation.

---

## Boundaries

- **Known not to apply:**
  - *Clean-room copyright vs. patents:* Clean-room reimplementation from ITU-T/ISO specifications does **not** eliminate SEP patent claims for H.264, HEVC, VVC, or AAC (`FDK-AAC/NOTICE:60-68`, `VVdeC/LICENSE.txt:21`).
  - *Single `Apache-2.0` licensing with FFmpeg:* Licensing a drop-in library under `Apache-2.0` alone is explicitly incompatible with `LGPLv2.1` and `GPLv2` builds (`FFmpeg/LICENSE.md:108-111`); dual `Apache-2.0 OR MIT` is required for seamless bidirectional interoperability.
  - *Partial `.so` replacement under `avpriv_*`:* Dropping an independent `libavcodec.so` beneath an unmodified upstream `libavformat.so` is invalid across arbitrary builds because `libavcodec.v:5` exports unstable `avpriv_*` private cross-library ABI entry points.
  - *`opus_compare` vs. bit-exactness:* Passing `opus_compare.c` ($Q \ge 0$) confirms perceptual conformance across `float` and `FIXED_POINT` builds, **not** bit-for-bit integer equivalence across builds or target CPUs.
- **Not examined:**
  - Specific hardware acceleration driver redistributable EULAs (proprietary `NVDEC`/`NVENC` SDK headers vs. open `Vulkan Video`, `VA-API`, `VideoToolbox`, and `MediaCodec` NDK headers).
  - Legal case-law interpretation across jurisdictions regarding header-file API copyrightability (`AVCodecContext` field names/constants) or exact `fate-suite` per-file copyright chains beyond FFmpeg's documented upload policy (`doc/fate.texi:192-216`).
- **Unknown:**
  - Exact upstream `fate-suite` total byte count and per-sample provenance manifest, as `rsync://fate-suite.ffmpeg.org/fate-suite/` was not mirrored or enumerated inside the offline validation sandbox.
- **Unsupported:**
  - Direct redistribution of `tests/checkasm`, `tests/tiny_ssim.c`, `--enable-nonfree` `fdk-aac`, or third-party `fate-suite` media samples inside an `Apache-2.0 OR MIT` source repository.

---

## Evidence

### Pinned Upstream Artifacts and Standards Inspected

| Subject | Pinned Identity | Verified Files & Citations |
| :--- | :--- | :--- |
| `FFmpeg/FFmpeg` | `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` | `LICENSE.md:1-127`, `configure:98-101, 4829-4844, 7526`, `libavcodec/libavcodec.v:1-9`, `libavcodec/version_major.h:28-45`, `libavcodec/packet.h:578-650`, `libavcodec/avcodec.h:443-1958`, `libavformat/libavformat.v:1-6`, `libavutil/libavutil.v:1-6`, `doc/fate.texi:45-299`, `tests/fate-run.sh:10-260` |
| `xiph/opus` | `31b4b36284394b66a4c9d7352991aa977dfc8bc1` | `COPYING`, `src/opus_compare.c:88-381`, `tests/run_vectors.sh:36-120` |
| `xiph/flac` | `59fa3402cb19b6b7c85b916f138cfb03c7b27504` | `COPYING.Xiph`, `README.md:38-72` |
| `ietf-wg-cellar/flac-test-files` | `aa7b0c6cf32994c106ae517a08134c28a96ff5b2` | `README.txt:1-73` |
| `webmproject/libvpx` | `18656c27cf3bee114562297274b64a84d0a6187c` | `LICENSE`, `test/test-data.sha1:1-879` |
| `AOMediaCodec/av1-spec` | `5e04f3f75e73a5898d7616c47c52f032144b8f80` | `LICENSE:1-40` |
| `AOMediaCodec/SVT-AV1` | `462771f87694e959cc1d3f9addde23d7015662e3` | `PATENTS.md:1-107` |
| `cisco/openh264` | `78783f195ce116ecbaea83f7fac0ea8a355518b5` | `LICENSE:1-23` |
| `mstorsjo/fdk-aac` | `ec82feb39662ac77e24ee9b324d5962e91bc79c5` | `NOTICE:1-92` |
| `fraunhoferhhi/vvdec` | `8909ff880412629bdd31e87a9f68d652db89479c` | `LICENSE.txt:1-32` |
| `pdeljanov/Symphonia` | `5f879df0bf309246a48d57caae457fd8c0e2a5cb` | `README.md:38-120`, `symphonia-core/src/lib.rs:1-19` |
| `memorysafety/rav1d` | `2e7216c20ac2a75de204d6c8d7268b75a45959b4` | `COPYING:1-24` |

### Standalone Reproducible Conformance Oracle Probe

Save as `/tmp/probe_conformance_oracles.py` and run `python3 /tmp/probe_conformance_oracles.py` (Python 3.10+ stdlib only):

```python
#!/usr/bin/env python3
"""Standalone probe for three normative media codec conformance oracle classes."""
import hashlib
import math
import random

def run_bit_exact_oracle() -> None:
    rng = random.Random(20261120)
    ref_frame = bytearray(rng.randrange(16, 236) for _ in range(6144))
    ref_md5 = hashlib.md5(ref_frame).hexdigest()
    dut_exact = bytearray(ref_frame)
    dut_1lsb = bytearray(ref_frame)
    dut_1lsb[4095] ^= 0x01
    print("[Oracle A: Bit-Exact MD5 (64x64 YUV420)]")
    print(f"  ref_md5       = {ref_md5}")
    print(f"  exact_match   = {hashlib.md5(dut_exact).hexdigest() == ref_md5}")
    print(f"  +1 LSB pixel  = {hashlib.md5(dut_1lsb).hexdigest()} (match={hashlib.md5(dut_1lsb).hexdigest() == ref_md5})")

def run_rms_lsb_oracle() -> None:
    N = 48000
    max_tol = 2.0 ** -14
    rms_tol = (2.0 ** -15) / math.sqrt(12.0)
    rng = random.Random(42)
    ref_float = [16000.0 * math.sin(2.0 * math.pi * 997.0 * n / 48000.0) + rng.uniform(-0.5, 0.5) for n in range(N)]
    ref_round = [int(round(x)) for x in ref_float]
    diffs_round = [(round(x) - x) / 32768.0 for x in ref_float]
    diffs_trunc = [(math.floor(x) - x) / 32768.0 for x in ref_float]
    print("[Oracle B: Statistical RMS & Peak LSB (ISO/IEC 14496-4 16-bit Envelope)]")
    for label, diffs in [("Continuous ref -> round()", diffs_round), ("Continuous ref -> floor()", diffs_trunc)]:
        rms = math.sqrt(sum(e * e for e in diffs) / N)
        print(f"  {label:28s}: max_err={max(abs(e) for e in diffs):.6e} rms={rms:.6e} (tol={rms_tol:.6e}) -> {'PASS' if rms <= rms_tol else 'FAIL'}")
    for label, dut in [
        ("Sparse unbiased +/-1 LSB", [r + (1 if (i % 32 == 0) else (-1 if (i % 32 == 16) else 0)) for i, r in enumerate(ref_round)]),
        ("Systematic -1 LSB bias", [r - 1 for r in ref_round]),
    ]:
        diffs = [(d - r) / 32768.0 for d, r in zip(dut, ref_round)]
        peak = max(abs(x) for x in diffs)
        rms = math.sqrt(sum(x * x for x in diffs) / N)
        peak_lsb = max(abs(d - r) for d, r in zip(dut, ref_round))
        print(f"  {label:28s}: max_lsb={peak_lsb} peak={peak:.6e} rms={rms:.6e} (tol={rms_tol:.6e}) -> {'PASS' if (peak <= max_tol and rms <= rms_tol) else 'FAIL'}")

NBANDS, NFREQS, TEST_WIN_SIZE, TEST_WIN_STEP = 21, 240, 480, 120
BANDS = [0, 2, 4, 6, 8, 10, 12, 14, 16, 20, 24, 28, 32, 40, 48, 56, 68, 80, 96, 120, 156, 200]

def opus_compare_mono_48k(x_samples: list[float], y_samples: list[float]) -> tuple[float, float]:
    nframes = (len(x_samples) - TEST_WIN_SIZE + TEST_WIN_STEP) // TEST_WIN_STEP
    window = [0.5 - 0.5 * math.cos((2.0 * math.pi / (TEST_WIN_SIZE - 1)) * j) for j in range(TEST_WIN_SIZE)]
    c = [math.cos((2.0 * math.pi / TEST_WIN_SIZE) * j) for j in range(TEST_WIN_SIZE)]
    s = [math.sin((2.0 * math.pi / TEST_WIN_SIZE) * j) for j in range(TEST_WIN_SIZE)]
    def band_energy(sig: list[float], compute_xb: bool) -> tuple[list[float], list[float]]:
        xb = [0.0] * (nframes * NBANDS) if compute_xb else []
        ps = [0.0] * (nframes * NFREQS)
        for xi in range(nframes):
            xw = [window[xk] * sig[xi * TEST_WIN_STEP + xk] for xk in range(TEST_WIN_SIZE)]
            xj = 0
            for bi in range(NBANDS):
                p = 0.0
                while xj < BANDS[bi + 1]:
                    ti, re, im = 0, 0.0, 0.0
                    for xk in range(TEST_WIN_SIZE):
                        re += c[ti] * xw[xk]
                        im -= s[ti] * xw[xk]
                        ti += xj
                        if ti >= TEST_WIN_SIZE:
                            ti -= TEST_WIN_SIZE
                    val = re * re + im * im + 100000.0
                    ps[xi * NFREQS + xj] = val
                    p += val
                    xj += 1
                if compute_xb:
                    xb[xi * NBANDS + bi] = p / (BANDS[bi + 1] - BANDS[bi])
        return xb, ps
    xb, X = band_energy(x_samples, True)
    _, Y = band_energy(y_samples, False)
    for xi in range(nframes):
        for bi in range(1, NBANDS):
            xb[xi * NBANDS + bi] += 0.1 * xb[xi * NBANDS + bi - 1]
        for bi in range(NBANDS - 2, -1, -1):
            xb[xi * NBANDS + bi] += 0.03 * xb[xi * NBANDS + bi + 1]
        if xi > 0:
            for bi in range(NBANDS):
                xb[xi * NBANDS + bi] += 0.5 * xb[(xi - 1) * NBANDS + bi]
        for bi in range(NBANDS):
            mask = 0.1 * xb[xi * NBANDS + bi]
            for xj in range(BANDS[bi], BANDS[bi + 1]):
                X[xi * NFREQS + xj] += mask
                Y[xi * NFREQS + xj] += mask
    for bi in range(NBANDS):
        for xj in range(BANDS[bi], BANDS[bi + 1]):
            xt, yt = X[xj], Y[xj]
            for xi in range(1, nframes):
                x2, y2 = X[xi * NFREQS + xj], Y[xi * NFREQS + xj]
                X[xi * NFREQS + xj] += xt
                Y[xi * NFREQS + xj] += yt
                xt, yt = x2, y2
    err = 0.0
    for xi in range(nframes):
        Ef = 0.0
        for bi in range(NBANDS):
            Eb = 0.0
            for xj in range(BANDS[bi], BANDS[bi + 1]):
                re = Y[xi * NFREQS + xj] / X[xi * NFREQS + xj]
                im = re - math.log(re) - 1.0
                if 79 <= xj <= 81:
                    im *= 0.1
                if xj == 80:
                    im *= 0.1
                Eb += im
            Ef += (Eb / (BANDS[bi + 1] - BANDS[bi])) ** 2
        Ef /= NBANDS
        err += (Ef * Ef) ** 2
    err = (err / nframes) ** (1.0 / 16.0)
    return 100.0 * (1.0 - 0.5 * math.log(1.0 + err) / math.log(1.13)), err

def run_opus_oracle() -> None:
    N, rng = 1200, random.Random(99)
    ref = [round(4000*math.sin(2*math.pi*440*n/48000) + 2000*math.sin(2*math.pi*2000*n/48000) +
                 1200*math.sin(2*math.pi*8000*n/48000) + 800*math.sin(2*math.pi*12000*n/48000)) for n in range(N)]
    print("[Oracle C: Psychoacoustic Bark-Band Masking (opus_compare.c 48 kHz mono)]")
    for label, sig in [
        ("+/-1 LSB fixed/float dither", [s + rng.choice([-1, 0, 1]) for s in ref]),
        ("8 kHz crossover perturbation (bin 80)", [ref[n] + round(2500*math.sin(2*math.pi*8000*n/48000)) for n in range(N)]),
        ("12 kHz unattenuated perturbation", [ref[n] + round(2500*math.sin(2*math.pi*12000*n/48000)) for n in range(N)]),
    ]:
        q, e = opus_compare_mono_48k([float(v) for v in ref], [float(v) for v in sig])
        print(f"  {label:38s}: Q={q:7.2f}%  err={e:.6f} -> {'PASS' if q >= 0.0 else 'FAIL'}")

if __name__ == "__main__":
    run_bit_exact_oracle()
    run_rms_lsb_oracle()
    run_opus_oracle()
```

---

## Revalidation

1. **Re-check FFmpeg license gates and ABI `avpriv_*` symbol exports at a newer FFmpeg commit:**
   ```bash
   curl -sSL --http1.1 https://raw.githubusercontent.com/FFmpeg/FFmpeg/<NEW_SHA>/LICENSE.md | grep -E "Apache License 2\.0|GPL|nonfree"
   curl -sSL --http1.1 https://raw.githubusercontent.com/FFmpeg/FFmpeg/<NEW_SHA>/libavcodec/libavcodec.v
   curl -sSL --http1.1 https://raw.githubusercontent.com/FFmpeg/FFmpeg/<NEW_SHA>/libavcodec/version_major.h
   ```
2. **Re-check Opus conformance comparator tolerances and dual-vector runner:**
   ```bash
   curl -sSL --http1.1 https://raw.githubusercontent.com/xiph/opus/<NEW_SHA>/src/opus_compare.c | grep -n -A5 "xj==80\|Q=100"
   curl -sSL --http1.1 https://raw.githubusercontent.com/xiph/opus/<NEW_SHA>/tests/run_vectors.sh | grep -n "OPUS_COMPARE"
   ```
3. **Re-run the standalone three-oracle probe (`< 0.5 s`):**
   ```bash
   python3 /tmp/probe_conformance_oracles.py
   ```
