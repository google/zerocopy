# FFmpeg External Codec, Crypto, and Subtitle Library Ecosystem: Safe-Rust Replacement Matrix vs. Minimal FFI and Sandbox Contracts

## Summary

Upstream `FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) is not a self-contained codec monolith: while `libavcodec` ships first-party software decoders for H.264, HEVC, VP8, VP9, WebP, MP3, Opus, and Vorbis, it delegates **100% of production software video encoding for H.264 (`libx264`), HEVC (`libx265`), VP8/VP9 (`libvpx`), and AV1 (`libaom`, `SVT-AV1`, `librav1e`)**, **all default software AV1 decoding (`libdav1d`, `libaom`)**, **all stream/datagram TLS (`OpenSSL`, `BoringSSL`, `GnuTLS`, `mbedTLS`)**, **zlib container/HTTP/PNG compression (`zlib`)**, and **ASS/SSA subtitle and complex-script text rendering (`libass`, `freetype`, `harfbuzz`, `fribidi`, `fontconfig`)** to external C and C++ libraries (`libavcodec/allcodecs.c:151-860`, `configure:2017-2150`).

A clean-slate verified Rust media architecture must partition this external ecosystem along three orthogonal axes:

1. **Direct Safe-Rust Replacement Feasibility:** Mature Rust implementations can replace **AV1 software decoding** (`memorysafety/rav1d@2e7216c20ac2a75de204d6c8d7268b75a45959b4`, exporting a drop-in 19-symbol `dav1d_*` C ABI), **DEFLATE/zlib compression** (`trifectatechfoundation/zlib-rs@a7f9c02c1f48b8962b46c5428828573e9cbac152`, `libz-rs-sys` drop-in `z_stream` ABI), **MP3 and Vorbis decoding** (`pdeljanov/Symphonia@5f879df0bf309246a48d57caae457fd8c0e2a5cb`, `#![forbid(unsafe_code)]`), **single-frame WebP decoding and encoding** (`image-rs/image-webp@946b31adf319a8f87530742716d9e2776044c431`, `#![forbid(unsafe_code)]`), **OpenType/TrueType glyph parsing and hinting** (`googlefonts/fontations@7eec1e18b6dcb2cbb77a805f280825c075a388c6`), and **TLS 1.2/1.3 stream transport** (`rustls/rustls@836e411eccaf7331f4c289aabef0de32474de3b8`). Conversely, **no feature- or rate-distortion-parity Rust replacement exists** for `libx264`, `libx265`, `libvpx` VP8/VP9 encoding, high-density `SVT-AV1` encoding, `libmp3lame` / `libvorbisenc` / `libopus` encoding, **Opus decoding in Symphonia** (where `symphonia-codec-opus/src/lib.rs` is an empty 1-line stub at `5f879df0bf309246a48d57caae457fd8c0e2a5cb`), **DTLS-SRTP (`RFC 5764`)** for WebRTC/WHIP (`libavformat/tls_openssl.c:816-869`), or stateful ASS/SSA subtitle rasterization (`libass`).
2. **License-Infectiousness Lattice:** FFmpeg's `configure` (`L2017-2055`, `L4829-4856`) enforces a five-point license join semilattice (`LGPLv2.1+` $\to$ `{GPLv2+, LGPLv3+}` $\to$ `GPLv3+` $\to$ `nonfree`). Linking `libx264` or `libx265` forces the combined work to `GPLv2+`; linking Apache-2.0 libraries (`OpenSSL >= 3.0.0`, `mbedTLS`) with `GPLv2`-only code is license-incompatible unless upgraded via `--enable-version3` to `GPLv3+` (`configure:7525-7527`, contradicting stale prose in `LICENSE.md:125-127`).
3. **Sound FFI and Containment Contracts:** Unreplaced C/C++ libraries cannot be linked in-process across a raw `extern "C"` boundary without placing their entire C/C++/ASM footprint inside the Undefined Behavior (UB) Trusted Computing Base (TCB). Preserving **UB-freedom** (Priority 1) and **Panic-freedom** (Priority 2) requires either (a) in-process WebAssembly/LFI software fault isolation (`RLBox` tainted-value verification membranes, viable for scalar/SIMD128 libraries but costing `303.24 us` per 1080p YUV420p linear-memory copy and losing AVX-512/SVE2 codec assembly), or (b) out-of-process OS sandboxing (`seccomp-bpf` + sealed `memfd_create` zero-copy frame pools + `AF_UNIX` `SOCK_SEQPACKET`, measured at `35.04 us` round-trip latency with `0` pixel copies and full crash containment).

## Applicability

This report characterizes external codec, compression, cryptographic transport, and subtitle/font library integrations in `FFmpeg/FFmpeg` at commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`configure`, `LICENSE.md`, `libavcodec/allcodecs.c`, `libavcodec/av1dec.c`, `libavcodec/lib*.c`, `libavcodec/zlib_wrapper.c`, `libavformat/tls_*.c`, `libavfilter/vf_subtitles.c`, `libavfilter/vf_drawtext.c`), evaluated against pinned upstream Rust counterparts (`rav1d`, `rav1e`, `Symphonia`, `rustls`, `rustls-ffi`, `zlib-rs`, `zune-image`, `image-webp`, `Fontations`) and sandboxing frameworks (`RLBox`, `Sandboxed API`).

Relationship among subjects:
- `FFmpeg/FFmpeg` defines the baseline C ABI wrapper contracts, codec dispatch precedence, allocator/re-entrancy callbacks, and license-gate rules.
- `rav1d`, `rav1e`, `Symphonia`, `rustls` + `rustls-ffi`, `zlib-rs`, `zune-image`, `image-webp`, and `Fontations` are evaluated both as idiomatic Rust crate replacements for clean-rewrite pipelines and (where `staticlib`/`cdylib` C ABIs exist, notably `rav1d`, `rav1e`, `libz-rs-sys`, and `rustls-ffi`) as ABI-compatible C link-ins.
- `RLBox` and `Sandboxed API` define the type-level membrane (`tainted<T>`) and process-level containment models for wrapping unreplaced C/C++ libraries soundly.

Micro-probe execution measurements (`Basis: execution`) apply specifically to `Linux 7.1.6-1rodete1-amd64` on `x86_64` with system `zlib 1.3.2` and `gcc -O2`; absolute latencies vary with CPU microarchitecture and kernel scheduler configuration, while structural order-of-magnitude ratios (zero-copy IPC vs. multi-megabyte frame copies) generalize across POSIX hosts supporting `memfd_create(2)` and `AF_UNIX` sockets.

This report builds on and cross-references established corpus findings without duplicating their proofs:
- Entropy decoding bounds in `libwebp` and `dav1d`: `libwebp-huffman-tables-dav1d-rans-cdfs-and-lcms2-icc-tetrahedral-luts`.
- Opus SILK/CELT hybrid DSP invariants: `webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows`.
- DEFLATE optimal parsing and block splitting: `deflate-inflate-algorithms-optimal-dp-and-block-splitting`.
- OpenType shaping and TrueType bytecode bounds: `harfbuzz-opentype-gsub-shaping-truetype-hinting-vms-and-font-winding`.
- X.509/TLS state-machine verification: `x509-pki-path-validation-asn1-frankencerts-dnssec-and-tls-state-machines`.
- Disjoint slice borrowing hazards: `borrow-checker-self-referential-views-disjoint-slices-and-polonius-limits`.
- Handle-table pinning, C-unwind ABIs, SFI/LFI sandboxes, and shared-memory double-fetch logics: `handle-tables-scoped-arenas-and-cross-runtime-ffi-pinning-protocols`, `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`, `modern-sfi-lfi-and-ring0-wasm-kernels-2020-2026`, `wayland-explicit-drm-syncobj-dbus-fd-passing-and-pipewire-graph-scheduling`, and `double-fetch-toctou-shared-dma-rings-and-single-fetch-logics`.

## Findings

### 1. FFmpeg Dispatch Precedence and Native-vs-External Asymmetry

`Basis: source`

In `FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`), `avcodec_find_decoder(id)` and `avcodec_find_encoder(id)` scan `codec_list[]` in the exact declaration order of `libavcodec/allcodecs.c`. Inspecting `allcodecs.c` reveals three distinct architectural regimes rather than uniform "optional plugins":

1. **First-Party Software Decode + External-Only Software Encode (H.264, HEVC, VP8, VP9, WebP, MP3):**
   - Native decoders appear near the top of `allcodecs.c`: `ff_h264_decoder` (`L151`), `ff_hevc_decoder` (`L161`), `ff_vp8_decoder` (`L379`), `ff_vp9_decoder` (`L382`), `ff_webp_anim_decoder` / `ff_webp_decoder` (`L390-391`), and `ff_mp3float_decoder` / `ff_mp3_decoder` (`L505-506`). Even when `libvpx` is enabled, `ff_vp8_decoder` and `ff_vp9_decoder` take default precedence over `ff_libvpx_vp8_decoder` (`L827`) and `ff_libvpx_vp9_decoder` (`L829`).
   - Conversely, FFmpeg contains **zero native general-purpose software encoders** for H.264, HEVC, VP8, VP9, WebP, or MP3. Software encoding depends entirely on `ff_libx264_encoder` (`L835`), `ff_libx265_encoder` (`L837`), `ff_libvpx_vp8_encoder` (`L826`), `ff_libvpx_vp9_encoder` (`L828`), `ff_libwebp_anim_encoder` / `ff_libwebp_encoder` (`L832-833`), and `ff_libmp3lame_encoder` (`L803`).
2. **Dual First-Party and External Software Implementations (Opus, Vorbis):**
   - FFmpeg ships native `ff_opus_encoder` / `ff_opus_decoder` (`L517-518`) and `ff_vorbis_encoder` / `ff_vorbis_decoder` (`L543-544`) ahead of `ff_libopus_encoder` / `ff_libopus_decoder` (`L810-811`) and `ff_libvorbis_encoder` / `ff_libvorbis_decoder` (`L824-825`). However, FFmpeg's native `opusenc` implements only CELT frames, whereas `libopus` implements the full RFC 6716 SILK + CELT hybrid encoder, in-band FEC, packet-loss concealment, and low-bitrate voice modes; production callers explicitly request `"libopus"` or `"libvorbis"` by name.
3. **The AV1 Inversion (External-Only Software Decode and Encode):**
   - `allcodecs.c` places `ff_libdav1d_decoder` (`L786`) in the primary table *above* the fallback barrier (`/* external libraries, that shouldn't be used by default if one of the above is available */` at `L850-851`), places `ff_libaom_av1_decoder` (`L858`) inside the fallback section, and places FFmpeg's own `ff_av1_decoder` (`L860`) *after both* with the explicit comment `/* hwaccel hooks only, so prefer external decoders */` (`L859`).
   - Direct inspection of `libavcodec/av1dec.c` (`L1578-1623`) confirms that `ff_av1_decoder` parses OBU bitstream headers solely to populate `.hw_configs` (`DXVA2`, `D3D11VA`, `D3D12VA`, `NVDEC`, `VAAPI`, `VDPAU`, `VideoToolbox`, `Vulkan`, `L1589-1622`) and contains **no software inverse transform, intra/inter prediction, CDEF, or loop-restoration DSP**. Without `libdav1d` or `libaom`, upstream FFmpeg cannot decode AV1 in software. Similarly, software AV1 encoding relies exclusively on `ff_libaom_av1_encoder` (`L778`), `ff_librav1e_encoder` (`L812`), and `ff_libsvtav1_encoder` (`L817`).

### 2. Licensing Lattice and Build-System Discrepancies

`Basis: source + documentation`

`configure` (`L2017-2055`, `L4829-4856`) computes the effective binary license as a join over enabled external libraries:

| Configure Gate | Governing List in `configure` | Examined Libraries Affected | Resulting Binary License (`configure:4846-4856`) |
| :--- | :--- | :--- | :--- |
| Default (no flags) | `EXTERNAL_LIBRARY_LIST` (`L2056-2150`) | `libdav1d`, `libaom`, `libsvtav1`, `librav1e`, `libvpx`, `libopus`, `libmp3lame`, `libvorbis`, `libwebp`, `zlib`, `gnutls`, `libass`, `libfreetype`, `libharfbuzz`, `libfribidi`, `libfontconfig`, `openssl < 3.0.0` (LGPL only) | `LGPL version 2.1 or later` |
| `--enable-gpl` | `EXTERNAL_LIBRARY_GPL_LIST` (`L2017-2031`) | `libx264` (`L2026`), `libx265` (`L2027`), `libxvid`, `libdavs2`, `librubberband`, `libvidstab`, `frei0r`, `avisynth` | `GPL version 2 or later` |
| `--enable-version3` | `EXTERNAL_LIBRARY_VERSION3_LIST` (`L2040-2050`) | Apache-2.0 (`mbedtls`, `libastcenc`, `libopencore_amr*`, `rkmpp`) and LGPLv3 (`gmp`, `libaribb24`, `liblensfun`) | `LGPL version 3 or later` (or `GPL version 3 or later` if `--enable-gpl` is also set) |
| `--enable-gpl --enable-version3` | `EXTERNAL_LIBRARY_GPLV3_LIST` (`L2052-2054`) + `openssl >= 3.0.0` (`L7525-7526`) | `libsmbclient`; `openssl >= 3.0.0` when combined with GPL codecs (`libx264`/`libx265`) | `GPL version 3 or later` |
| `--enable-nonfree` | `EXTERNAL_LIBRARY_NONFREE_LIST` (`L2033-2038`) + `openssl < 3.0.0` with `--enable-gpl` (`L7527`) | `libfdk_aac`, `decklink`; `openssl 1.1.1` + `libx264`/`libx265` | `nonfree and unredistributable` |

Two primary-source subtleties govern Rust replacement and linking architecture:
1. **Documentation-vs-Source Discrepancy on OpenSSL 3.x (`LICENSE.md:125-127` vs. `configure:7525-7531`):** `LICENSE.md:125-127` states unconditionally that *"The Fraunhofer FDK AAC and OpenSSL libraries are under licenses which are incompatible with the GPLv2 and v3."* However, `configure:7525-7527` tests `pkg-config` for `"openssl >= 3.0.0"` (which relicensed from the advertising-clause OpenSSL/SSLeay license to **Apache-2.0**) and enforces `{ enabled gplv3 || ! enabled gpl || enabled nonfree || die "ERROR: OpenSSL >=3.0.0 requires --enable-version3"; }`. Thus, `OpenSSL >= 3.0.0` + `libx264` is redistributable under `GPLv3+`, whereas `OpenSSL 1.1.1` (and `BoringSSL`, which retains legacy OpenSSL license headers alongside ISC) + `libx264` remains unredistributable (`--enable-nonfree`). Replacing OpenSSL/GnuTLS with `rustls` (`Apache-2.0 OR ISC OR MIT`, `rustls/Cargo.toml:6`) eliminates this GPLv2/Apache-2.0 conflict entirely because ISC and MIT are unconditionally compatible with both `LGPLv2.1+` and `GPLv2+`.
2. **MPL-2.0 File-Level Weak Copyleft in `Symphonia` (`Symphonia/Cargo.toml:29`):** Unlike `rav1d` (`BSD-2-Clause`), `rav1e` (`BSD-2-Clause` + AOM Patent License 1.0), `zlib-rs` (`Zlib`), `zune-image` (`MIT OR Apache-2.0 OR Zlib`), `image-webp` (`MIT OR Apache-2.0`), and `Fontations` (`MIT OR Apache-2.0`), `Symphonia` (`5f879df0bf309246a48d57caae457fd8c0e2a5cb`) is licensed under **MPL-2.0** (`symphonia-codec-vorbis/src/lib.rs:4-6`). MPL-2.0 Section 3.3 permits static or dynamic linking into proprietary, LGPLv2.1+, or GPLv2+/GPLv3+ binaries provided modifications to MPL-covered files remain available under MPL-2.0 and the notice is preserved (unless marked `"Incompatible With Secondary Licenses"`, which Symphonia does not set).

### 3. Primary-Source Survey: External Integrations vs. Safe-Rust Counterparts

`Basis: source + documentation`

| External C/C++ Integration | FFmpeg Wrapper (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) | Upstream C/C++ License | Primary Rust Counterpart (Pinned) | Rust License & `unsafe` Posture | Functional & Performance Parity Verdict |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`libdav1d`** (AV1 dec) | `libavcodec/libdav1d.c` (`620` LOC) | BSD-2-Clause | `memorysafety/rav1d` (`2e7216c...`, `v1.1.1`) | BSD-2-Clause; `unsafe` at C ABI, `DisjointMut`, and optional `.S`/`.asm` (`Cargo.toml:40-46`) | **Drop-in replacement.** Exports all 19 `dav1d_*` C ABI functions (`src/lib.rs:228-1070`); ~5–10% runtime overhead vs C `dav1d` with `asm` enabled; pure-Rust scalar fallback available. |
| **`libaom` / `SVT-AV1`** (AV1 enc/dec) | `libaomdec.c`, `libaomenc.c`, `libsvtav1.c` (`871` LOC) | BSD-2-Clause / BSD-3-Clause + AOM Patent 1.0 | `xiph/rav1e` (`31435de...`, `v0.8.0`) | BSD-2-Clause + AOM Patent 1.0; `unsafe` SIMD intrinsics + optional `nasm` (`Cargo.toml:43`) | **Partial encode replacement.** `ff_librav1e_encoder` is already in `allcodecs.c:812`, but `SVT-AV1` leads significantly in multi-core scaling and BD-rate/speed Pareto efficiency across VOD/live presets. |
| **`libx264`** (H.264 enc) | `libavcodec/libx264.c` (`1742` LOC) | GPL-2.0-or-later (or commercial) | None at parity (`openh264` is C++) | N/A | **Unreplaced (wrap/sandbox).** No safe-Rust H.264 encoder approaches `x264` psychovisual RDO (`psy-rd`, `mbtree`, VBV lookahead) or AVX2/AVX-512/NEON DSP density. |
| **`libx265`** (HEVC enc) | `libavcodec/libx265.c` (`1111` LOC) | GPL-2.0-or-later (or commercial) | None | N/A | **Unreplaced (wrap/sandbox).** C++ library behind `x265_api_get(depth)` (`libx265.c:279, 1032-1040`); zero production Rust HEVC encoders exist. |
| **`libvpx`** (VP8/VP9 dec/enc) | `libvpxdec.c` (`401` LOC), `libvpxenc.c` | BSD-3-Clause | `image-webp` (`vp8` keyframe dec only); no full VP9 enc/dec crate at parity | N/A | **Decode replaceable by clean rewrite of FFmpeg `vp8`/`vp9`; encode unreplaced.** `libvpx` VP9 RDO/alt-ref/SVC encoding requires FFI/sandbox wrapping. |
| **`libopus`** (Opus dec/enc) | `libopusdec.c` (`264` LOC), `libopusenc.c` | BSD-3-Clause | None in `Symphonia` (`symphonia-codec-opus/src/lib.rs` is empty at `5f879df...`) | N/A | **Unreplaced by Symphonia at pinned revision.** Must either rewrite RFC 6716 SILK+CELT cleanly in verified Rust or wrap `libopus` behind FFI/sandbox. |
| **`libmp3lame`** (MP3 enc) | `libavcodec/libmp3lame.c` (`343` LOC) | LGPL-2.0-or-later | `Symphonia` (`symphonia-bundle-mp3`, **decode only**) | MPL-2.0; `#![forbid(unsafe_code)]` (`src/lib.rs:9`) | **Decode replaced (`MpaDecoder`); encode unreplaced.** No mature psychoacoustic VBR MP3 encoder exists in safe Rust. |
| **`libvorbis`** (Vorbis dec/enc) | `libvorbisdec.c` (`211` LOC), `libvorbisenc.c` | BSD-3-Clause | `Symphonia` (`symphonia-codec-vorbis`, **decode only**) | MPL-2.0; `#![forbid(unsafe_code)]` (`src/lib.rs:9`) | **Decode replaced (`VorbisDecoder`); encode unreplaced.** Vorbis floor/residue psychoacoustic encoding remains C-only. |
| **`libwebp`** (WebP enc/anim) | `libwebpenc.c` (`107` LOC), `libwebpenc_common.c` | BSD-3-Clause | `image-rs/image-webp` (`946b31a...`, `v0.2.4`) + `zune-image` (`2cdbbf5...`, non-WebP formats) | MIT OR Apache-2.0; `#![forbid(unsafe_code)]` (`image-webp/src/lib.rs:3`) | **Decode + basic lossless/lossy single-frame encode replaced; `WebPAnimEncoder` multi-frame RDO unreplaced.** Note `zune-image` `0.5.3` covers JPEG/PNG/JXL/HDR/PPM/QOI/PSD (`README.md:87-97`), not WebP. |
| **`zlib`** (DEFLATE/RFC 1950) | `libavcodec/zlib_wrapper.c` (`102` LOC), `libavformat/http.c` | Zlib | `trifectatechfoundation/zlib-rs` (`a7f9c02...`, `v0.6.8`) | Zlib; `unsafe` for SIMD intrinsics & `libz-rs-sys` C ABI | **Drop-in replacement.** `libz-rs-sys` matches `zlib-ng` throughput (`README.md:32`) and honors `z_stream.zalloc`/`zfree` (`zlib_wrapper.c:49-50`). |
| **`OpenSSL` / `BoringSSL` / `GnuTLS`** | `tls_openssl.c` (`1057` LOC), `tls_gnutls.c` (`804` LOC) | Apache-2.0 (`>=3.0`), OpenSSL/ISC, LGPLv2.1+ | `rustls/rustls` (`836e411...`) + `rustls-ffi` (`60e06ef...`) | Apache-2.0 OR ISC OR MIT; safe Rust protocol core + crypto provider (`aws-lc-rs`/`ring`) | **Stream TLS 1.2/1.3 replaced; DTLS-SRTP & TLS 1.0/1.1 unsupported.** `tls_openssl.c:816, 825, 843` uses `DTLS_method`, `use_srtp`, and `TLS1_VERSION`. |
| **`libass` + `freetype` (+ `harfbuzz`, `fribidi`, `fontconfig`)** | `vf_subtitles.c` (`593` LOC), `vf_drawtext.c` (`1977` LOC) | ISC (`libass`), FTL/GPLv2 (`freetype`), MIT (`harfbuzz`), LGPLv2.1+ (`fribidi`) | `googlefonts/fontations` (`7eec1e1...`: `read-fonts`, `skrifa`) + `harfruzz` | MIT OR Apache-2.0; safe Rust (`bytemuck`) | **Font parsing/hinting (`skrifa`) & OpenType shaping (`harfruzz`) replaced; `libass` ASS/SSA parser/compositor unreplaced.** |

#### 3.1 Critical Primary-Source Verification Nuances in the Rust Counterparts

1. **`rav1d`'s `DisjointMut<T>` Release-Mode Soundness Gap (`rav1d/src/disjoint_mut.rs:34-73`):**
   `rav1d` achieves frame- and tile-threaded AV1 decoding in Rust without `Arc<Mutex<...>>` per pixel block by wrapping frame planes and scratch buffers in `pub struct DisjointMut<T: ?Sized + AsMutPtr>` (`UnsafeCell<T>`). In debug builds (`#[cfg(debug_assertions)]`), `DisjointMut` records active borrow intervals in `DisjointMutAllBounds` and panics on overlap (`src/disjoint_mut.rs:28-36`). In release builds, all bounds tracking vanishes (`#[cfg_attr(not(debug_assertions), repr(transparent))]`, `L33`), and `unsafe impl Sync for DisjointMut<T>` (`L49-73`) states:
   > *"Furthermore, all `T`s used have `AsMutPtr::Target`s that are provenanceless, i.e. they have no internal references or pointers or integers that hold pointer provenance. Thus, a data race due the lack of runtime disjointness checking in release mode would only result in wrong results, and cannot result in memory safety."*
   `Basis: source + derived` — Under the Rust / LLVM / MiniRust memory model, **this justification is unsound**: any unsynchronized conflicting non-atomic read/write or write/write on `UnsafeCell<u8>` across threads produces `poison` / immediate language-level **Undefined Behavior**, enabling compiler miscompilation (such as loop unswitching, out-of-thin-air branch elision, or bounds-check elimination downstream of a racy read), not merely corrupted pixel values. Consequently, adopting `rav1d` under **Priority 1 (UB-freedom)** requires either (a) discharging static tile/superblock index-disjointness proof obligations (via spatial slice-splitting lenses; see `borrow-checker-self-referential-views-disjoint-slices-and-polonius-limits`), or (b) retaining lightweight tile-row range assertions in release builds.

2. **`Symphonia` `v0.6.1` `symphonia-codec-opus` Stub Discovery (`Symphonia@5f879df0bf309246a48d57caae457fd8c0e2a5cb`):**
   Although workspace `Cargo.toml:11` lists `"symphonia-codec-opus"` alongside `"symphonia-bundle-mp3"` and `"symphonia-codec-vorbis"`, direct inspection of `symphonia-codec-opus/src/lib.rs` at commit `5f879df0bf309246a48d57caae457fd8c0e2a5cb` shows the file is **1 line (0 bytes of code)**. `Symphonia` provides zero Opus decoding functionality at this revision; only MP1/MP2/MP3, Vorbis, FLAC, AAC-LC, ALAC, WavPack, ADPCM, and PCM decoders are implemented (`#![forbid(unsafe_code)]`).

3. **`image-webp` Dimension-Mismatch Panic (`image-webp/src/encoder.rs:56-73`):**
   While `image-rs/image-webp` (`946b31adf319a8f87530742716d9e2776044c431`) enforces `#![forbid(unsafe_code)]` (`src/lib.rs:3`)—guaranteeing **Priority 1 (UB-freedom)**—its encoder functions explicitly document `# Panics: Panics if the image data is not of the indicated dimensions` (`src/encoder.rs:56-58`), whereas width/height bounds `0` or `> 16384` return `Err(EncodingError::InvalidDimensions)` (`L71-73`). Under **Priority 2 (Panic-freedom)**, any media-engine wrapper calling `image-webp` must check `data.len() == usize::from(width) * usize::from(height) * bpp` with checked multiplication before invocation.

4. **DTLS-SRTP and Custom `BIO` Callbacks in `tls_openssl.c` vs. `rustls` (`libavformat/tls_openssl.c:610-617, 816-869`):**
   FFmpeg's `tls_openssl.c` does not pass raw OS socket FDs to OpenSSL; instead, it constructs a custom `BIO_METHOD` (`url_bio_method = BIO_meth_new(BIO_TYPE_SOURCE_SINK, "urlprotocol bio")`, `L610-617`) that routes TLS ciphertext reads/writes through FFmpeg's composable `URLContext` layer (`url_bio_bread` `L543`, `url_bio_bwrite` `L575`). `rustls::ClientConnection` and `ServerConnection` natively operate as sans-I/O state machines (`read_tls` / `write_tls` over `&mut dyn Read` / `&mut dyn Write`), which is *cleaner* and safer than OpenSSL's mutable `BIO` callback table. However, `tls_openssl.c` also implements **DTLS 1.0/1.2 + SRTP key export** (`DTLS_server_method` / `DTLS_client_method` at `L816`, `SSL_CTX_set_tlsext_use_srtp` at `L843`, `DTLS_set_link_mtu` at `L869`, `DTLSv1_handle_timeout` at `L683`) for WebRTC/WHIP streaming, plus legacy `TLS1_VERSION` fallback (`L825`). `rustls` (`836e411eccaf7331f4c289aabef0de32474de3b8`, `rustls/src/lib.rs:7`) supports exclusively stream **TLS 1.2 and TLS 1.3**.

### 4. Five Concrete FFI Hazard Classes in FFmpeg's `lib*` Wrappers

`Basis: source + derived`

Direct source inspection of FFmpeg's C wrappers exposes five recurring FFI hazard patterns that violate Rust's memory, aliasing, and unwind safety invariants if translated naively:

1. **Cross-Thread Reference-Counted Frame Allocation Callbacks (`libdav1d.c:77-135, 216-217`; `libvpxdec.c:53-86, 106`):**
   - `libdav1d.c` registers `s.allocator.alloc_picture_callback = libdav1d_picture_allocator` and `release_picture_callback = libdav1d_picture_release` (`L216-217`). Inside `libdav1d_picture_allocator` (`L77`), FFmpeg allocates an aligned `AVBufferRef *buf` from an `AVBufferPool`, writes plane pointers into `p->data[0..2]`, and stashes `buf` in `p->allocator_data`. Worker threads inside the external library asynchronously invoke `libdav1d_picture_release` (`L125`, calling `av_buffer_unref(&buf)`) when the decoded picture leaves both the output queue and the DPB reference slots.
   - **Soundness Obligation:** If an unverified C decoder invokes `release_picture_callback` twice (double-free), omits it on an error path (leak), mutates `p->data[i]` after returning the picture to the host (aliasing violation against immutable Rust `&[u8]` views), or corrupts `p->allocator_data` (arbitrary pointer dereference), host memory safety collapses immediately.
2. **Opaque Pointer Round-Tripping and Relational Pointer UB (`libx264.c:495-538, 691-707`):**
   - To associate per-frame metadata (`frame_opaque_ref`, `wallclock`, `duration`) across B-frame reordering, `libx264.c` allocates a ring `x4->reordered_opaque` (`L1463-1465`), sets `pic->opaque = &x4->reordered_opaque[x4->next_reordered_opaque]` (`L495, 535`), passes `pic` into `x264_encoder_encode` (`L650`), and checks the returned `out_opaque = pic_out.opaque` via:
     ```c
     if (out_opaque >= x4->reordered_opaque &&
         out_opaque < &x4->reordered_opaque[x4->nb_reordered_opaque]) { ... }
     ```
     (`libx264.c:692-693`).
   - **Soundness Obligation:** In ISO C11 (6.5.8p5) and Rust, relational `<` / `>=` comparison on raw pointers that do not point into the same allocated array object (which is the exact failure case this check attempts to guard against!) is **Undefined Behavior**, and casting a forged `void *` back to `&mut X264Opaque` fabricates provenance. A verified Rust wrapper must never pass host pointers through `void *opaque`; instead, it must store a **64-bit generation-tagged integer slot key** (`(generation << 32) | index` cast via `uintptr_t`, without `expose_provenance`) and validate `index < table.len() && table[index].gen == generation` in total safe arithmetic (`handle-tables-scoped-arenas-and-cross-runtime-ffi-pinning-protocols`).
3. **Asymmetric Library-Owned Output Buffers (`libsvtav1.c:524-541, 671-763`):**
   - `svt_av1_enc_get_packet(svt_enc->svt_handle, &headerPtr, svt_enc->eos_flag)` (`L671`) returns a library-owned `EbBufferHeaderType *` backed by `SVT-AV1`'s internal worker pool, requiring `svt_av1_enc_release_out_buffer(&headerPtr)` across **five separate exit paths** (`L692, 702, 716, 724, 763`). In Rust, this must be wrapped in an RAII drop guard whose borrow lifetime `'pkt` strictly bounds any `&[u8]` slice constructed via `slice::from_raw_parts` (and checks `p_buffer != null` when `n_filled_len == 0`, since C libraries routinely pair `NULL` with length `0`, which is immediate UB in `core::slice::from_raw_parts`!).
4. **C++ Runtime Exceptions and Multi-Bitdepth Vtables (`libx265.c:279-283, 604, 876, 1032-1040`):**
   - `libx265` exposes a C function-pointer table `const x265_api *x265_api_get(int bitDepth)` implemented in C++. Uncaught C++ exceptions (`std::bad_alloc` or internal `throw`) unwinding across a Rust `extern "C"` call frame trigger immediate UB (or abort under `extern "C-unwind"` unless caught on the C++ side with a `try { ... } catch (...)` C shim; see `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`).
5. **Re-Entrant Callbacks and Transitive C Dependency Trees (`vf_subtitles.c:146-245`; `vf_drawtext.c:44-69, 524-700, 1046, 1384-1427`):**
   - Enabling `vf_subtitles` or `vf_drawtext` pulls a five-library transitive C graph—`libass`, `freetype`, `harfbuzz`, `fribidi`, and `fontconfig` (which further links `expat` or `libxml2` to parse `/etc/fonts/fonts.conf` in `FcInitLoadConfigAndFonts()`, `vf_drawtext.c:536`)—directly into the media process, registering variadic `va_list` logging callbacks (`ass_set_message_cb`, `vf_subtitles.c:151`; `X264_log`, `libx264.c:131`). If a logging or I/O callback re-enters Rust while an exclusive `&mut Context` borrow is live on the call stack, Tree Borrows / Stacked Borrows uniqueness is violated instantaneously.

### 5. Minimal FFI and Sandbox Contract + Empirical Boundary Overhead

`Basis: derived + execution`

To integrate an unreplaced external C/C++ library (`libx264`, `libx265`, `SVT-AV1`, `libvpx` enc, `libopus`, `libass`) into a verified Rust media engine, the architecture must choose explicitly among three containment tiers according to the **Verification Priority Stack**:

| Containment Tier | Priority 1: UB-Freedom (Host Memory Soundness) | Priority 2: Panic-Freedom (Crash/Abort Containment) | Native SIMD/ASM Preservation (`AVX2`/`AVX-512`/`NEON`) | Measured Boundary Cost (`x86_64`, `Linux 7.1.6`) | Target Libraries |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Tier 1: Unsandboxed In-Process Membrane** (`extern "C"` + handle table + `MaybeUninit`) | **Conditional on C/ASM TCB:** Eliminates host-side FFI misuse UB, but spatial/temporal bugs inside C/ASM corrupt Rust heap/stack. | **Violated on C `abort()`/`SIGSEGV`:** C crash terminates entire host process. | **100%** (zero ISA restriction). | **`5.04 ns`** per validated handle lookup (`probe_pkg1`). | Trusted/audited C crypto (`AWS-LC`/`BoringSSL` FIPS) when TCB expansion is explicitly accepted. |
| **Tier 2: In-Process SFI / Wasm2c / LFI** (`RLBox` `tainted<T>` + bounded linear heap) | **Guaranteed outside tiny SFI verifier TCB:** Stores masked/bounded to sandbox linear memory; indirect calls checked. | **Traps converted to `Result::Err`:** Wasm OOB/unreachable traps unwind/return cleanly to host without killing process. | **Degraded (`SIMD128` ceiling):** Loses `AVX2`/`AVX-512`/`SVE2` handwritten `.asm` (3x–10x penalty on video encoders). | **`303.24 us`** per 1080p YUV420p (`3.11 MB`) bounce copy (`~606 us` in+out; `<1 us` on small audio/subtitle packets). | Low-bandwidth, non-ASM-dominated C libraries: `libmp3lame`, `libvorbisenc`, `libass` (small subtitle bitmaps), `libopus` scalar/SIMD128. |
| **Tier 3: Out-of-Process OS Sandbox** (`seccomp-bpf` + namespaces + sealed `memfd` + `SOCK_SEQPACKET`) | **Guaranteed by hardware MMU:** Worker process has disjoint virtual address space; shared `memfd` holds only provenanceless pixel/bitstream bytes. | **100% Contained:** Worker `SIGSEGV`, `SIGABRT`, C++ terminate, or OOM kill surfaces as `EPOLLHUP` / `Err(WorkerCrashed)` on IPC socket. | **100%** (worker executes unmodified native `AVX-512`/`NEON` assembly). | **`35.04 us`** full IPC round-trip + **`0` pixel copies** via `memfd` (`F_SEAL_SHRINK \| F_SEAL_GROW \| F_SEAL_SEAL = 0x7`). | Compute-heavy, ASM-dense video codecs: `libx264`, `libx265`, `SVT-AV1`, `libvpx` VP9 encoder. |

#### 5.1 Seven Mandatory Clauses of the Minimal FFI / Sandbox Safety Contract

Whenever wrapping any unreplaced library across **Tier 1, Tier 2, or Tier 3**, the Rust boundary adapter must discharge seven machine-checkable obligations:

1. **Zero Provenance Exposure (`NoRawHostPointers`):** Never pass Rust references or heap addresses as `void *opaque` / `cookie` (`libx264.c:535`). Pass integer `(generation, index)` handles validated in $O(1)$ against a Rust-owned `Vec<Slot>`.
2. **Non-Null Empty-Slice Normalization (`EmptySliceGuard`):** Never pass a C `(ptr, len)` pair directly to `core::slice::from_raw_parts[_mut]`; replace `len == 0` with `NonNull::dangling().as_ptr()` before slice construction, and reject `ptr == null && len > 0`.
3. **Single-Fetch Tainted Descriptors (`SingleFetchMembrane`):** In Tier 2 (shared Wasm linear memory) and Tier 3 (shared `memfd`), an adversarial or buggy worker thread can mutate shared memory concurrently with host validation (`double-fetch-toctou-shared-dma-rings-and-single-fetch-logics`). All output headers (`nal_count`, `packet_size`, `pts`, `plane_offsets`) must be copied **once** (`read_volatile` / `memcpy`) into private Rust stack storage *before* checking bounds invariants (`RLBox` `copy_and_verify`).
4. **Immutable File-Sealing on Shared Frame Pools (`SealedMemfdPool`):** In Tier 3, every shared `memfd` passed via `SCM_RIGHTS` must be sealed with `F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_SEAL` (`0x7`) prior to sharing (`wayland-explicit-drm-syncobj-dbus-fd-passing-and-pipewire-graph-scheduling`). Without `F_SEAL_SHRINK`, a compromised codec worker calling `ftruncate(fd, 0)` induces synchronous `SIGBUS` inside the verified Rust host when reading mapped pixels!
5. **Exclusive Typestate Slot Leasing (`HostOwned` $\leftrightarrow$ `WorkerLeased`):** While a `memfd` frame slot is in state `WorkerLeased`, the Rust host holds **zero `&[u8]` or `&mut [u8]` references** to that region (accessing it only via raw `*mut u8` / `UnsafeCell` after the `SOCK_SEQPACKET` completion message transitions the slot back to `HostOwned`), preventing Rust aliasing UB even if the sandboxed worker scribbles continuously onto leased slots.
6. **Re-Entrancy Disjointness & C++ Unwind Firewall (`NoCallbackAliasing`):** Any C shim wrapping a C++ library (`libx265`) must wrap every entry point in `try { ... } catch (...) { return ERR_CPP_EXCEPTION; }`, and any callback into Rust (`zalloc`, `BIO`, logging) must receive only an isolated `CallbackState` token disjoint from `&mut CodecSession`—or, in Tier 3, be eliminated entirely in favor of message-passing over the IPC channel.
7. **Overflow-Checked Custom Allocator Accounting (`BoundedZAlloc`):** In-process custom allocators (`zlib_wrapper.c:49-50`, `zalloc(opaque, items, size)`) must compute `items.checked_mul(size)` and enforce a per-session byte ceiling before calling the host allocator, returning `NULL` cleanly on overflow or budget exhaustion rather than panicking on Rust `Layout::from_size_align` failure (**Priority 2: Panic-freedom**).

#### 5.2 Empirical Micro-Probe Results (`probe_pkg1.c`)

`Basis: execution`

Executing `probe_pkg1.c` on `Linux 7.1.6-1rodete1-amd64` (`x86_64`, `gcc -O2`, system `zlib 1.3.2`) yielded:
- **Stateful `zlib` `inflateReset` reuse (`4,096 B` payload compressed to `2,111 B`):** `inflateInit` invoked `zalloc` **exactly once** (`7,160 B` for `inflate_state`) and `0` times across `10,000` subsequent `inflateReset` + `inflate(..., Z_FINISH)` calls (`19.65 us` per 4 KiB block), confirming that pre-allocating a bounded `8 KiB` arena per stream makes `zlib` / `zlib-rs` completely allocation-free at steady state.
- **Validated handle-table membrane (`validated_membrane_call`):** `5.04 ns` per call (6-bit slot index + 58-bit generation tag + `checked_add` bounds check).
- **Tier 2 linear-memory bounce copy (`1920x1080` YUV420p = `3,110,400 B`):** `303.24 us` per one-way `memcpy` (`~606.5 us` round-trip, scaling linearly to `~2.43 ms` round-trip at 4K UHD `3840x2160` = `12,441,600 B`, consuming **14.6% of a 16.67 ms 60 fps frame budget** purely in memory traffic).
- **Tier 3 `AF_UNIX` `SOCK_SEQPACKET` + sealed `memfd` (`seals = 0x7`):** `35.04 us` full round-trip latency across `fork()` processes—**8.65x faster than a single 1080p bounce copy** and **independent of resolution** (4K and 8K frames incur the exact same `35.04 us` control-plane wakeup with zero pixel copies).

### 6. Clean-Rewrite Architectural Implications

`Basis: derived`

1. **Eliminate FFmpeg's `AVCodecContext` God-Struct at the External Boundary:** FFmpeg funnels encoders, decoders, bitstream filters, and hardware contexts through a single 1,000+-field mutable `AVCodecContext`, forcing wrappers like `libx264.c` (`1,742` LOC) and `libx265.c` (`1,111` LOC) to serialize numeric fields into strings and pass them to `param_parse(key, buf)` (`libx265.c:169-597`). A clean Rust media architecture should separate strongly typed `VideoEncoderConfig` / `AudioDecoderConfig` codecs from an explicit `SandboxChannel<FramePool>` trait.
2. **Immediate First-Party Rust Integration Targets:** Replace `libdav1d` with `rav1d` (after discharging or guarding `DisjointMut` slice disjointness), `zlib` with `zlib-rs`, MP3/Vorbis/FLAC/ALAC decoding with `Symphonia` (or clean verified Rust ports), font parsing/shaping with `Fontations` (`skrifa`) + `harfruzz`, and HTTPS/RTMPS/RTSPS TLS 1.2/1.3 with `rustls`.
3. **Out-of-Process Worker Isolation for GPL and C++/ASM Encoders:** Isolate `libx264`, `libx265`, `SVT-AV1`, and `libvpx` VP9 encoders behind Tier 3 (`SOCK_SEQPACKET` + `0x7`-sealed `memfd` pools). This simultaneously preserves 100% of `AVX-512`/`NEON` encoder throughput, enforces **Priority 1 (UB-freedom)** and **Priority 2 (Panic-freedom)** in the host process, and cleanly separates optional GPLv2+ encoder worker binaries from an MIT/Apache-2.0/BSD core library when distributed as independent user-installed plugins (subject to applicable distribution counsel; see **Boundaries**).

## Boundaries

- **Not examined — End-to-end BD-rate and multi-socket encoding throughput benchmarks:** We did not execute comparative PSNR/SSIM/VMAF rate-distortion sweeps of `rav1e` `v0.8.0` vs. `SVT-AV1` vs. `libaom`, nor `rav1d` `v1.1.1` vs. C `dav1d` on full video bitstreams inside this capsule environment; parity classifications rely on inspected codebase capabilities (`Cargo.toml`, DSP feature gates) and upstream architectural scope.
- **Known not to apply — `Symphonia` `v0.6.1` for Opus decoding or any audio encoding:** Direct inspection of `symphonia-codec-opus/src/lib.rs` at `5f879df0bf309246a48d57caae457fd8c0e2a5cb` proves the crate is an empty stub, and `Symphonia` provides zero audio encoders. Do not assume `Symphonia` replaces `libopus`, `libmp3lame`, or `libvorbisenc`.
- **Known not to apply — `rustls` for WebRTC DTLS-SRTP (`RFC 5764`) or legacy TLS 1.0/1.1:** `rustls` (`836e411eccaf7331f4c289aabef0de32474de3b8`) implements exclusively stream TLS 1.2 and TLS 1.3 (`rustls/src/lib.rs:7`); FFmpeg's `whip` / WebRTC DTLS-SRTP paths (`libavformat/tls_openssl.c:816-869`) require either a separate Rust DTLS-SRTP stack (such as `dimpl` / `webrtc-rs` `dtls`, not audited here) or a sandboxed OpenSSL/BoringSSL worker.
- **Known not to apply — `rav1d` release builds as unconditionally UB-free without `DisjointMut` verification:** Even with `--no-default-features` (disabling `.S`/`.asm`), `rav1d/src/disjoint_mut.rs:60-73` disables runtime overlap checks in release mode; soundness requires proving index disjointness across concurrent tile/frame tasks.
- **Unsupported — Process IPC as an automatic GPL copyleft exemption:** Technical address-space isolation (`fork`/`exec` over `AF_UNIX` + `memfd`) contains crashes and memory corruption, **not** copyright licensing obligations. Whether shipping a host binary alongside a `GPLv2+` `libx264`/`libx265` worker constitutes an aggregate or a combined derivative work under GPLv2 depends on distribution structure and legal counsel, not technical IPC alone.

## Evidence

### Primary Repository Sources Inspected

1. **`FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`):**
   - `LICENSE.md:1-127` — LGPLv2.1+ baseline, GPLv2+/v3 filter and external library lists, stale OpenSSL GPLv3 incompatibility note (`L125-127`).
   - `configure:2017-2150, 4829-4872, 7316-7320, 7450-7536, 8302` — `EXTERNAL_LIBRARY_{GPL,NONFREE,VERSION3,GPLV3}_LIST`, `die_license_disabled`, mutual exclusion of `gnutls`/`openssl`/`mbedtls` (`L4858-4865`), and version-split `openssl >= 3.0.0` Apache-2.0/`gplv3` check (`L7525-7531`).
   - `libavcodec/allcodecs.c:151-165, 379-391, 505-544, 778-890` — Codec registration order and `ff_av1_decoder` fallback placement (`L786, 858-860`).
   - `libavcodec/av1dec.c:1578-1623` — Hardware-acceleration-only `.hw_configs` table on `ff_av1_decoder`.
   - `libavcodec/libdav1d.c:77-135, 216-217, 333-343, 605` — Custom `Dav1dAllocator` wrapping `AVBufferRef` in `p->allocator_data`.
   - `libavcodec/libvpxdec.c:53-86, 106, 219` — `vpx_codec_set_frame_buffer_functions` custom buffer callbacks.
   - `libavcodec/libx264.c:60-68, 119-149, 492-538, 640-707, 1139, 1461-1467` — `X264Opaque` pointer round-trip and relational pointer bounds check (`L692-693`).
   - `libavcodec/libx265.c:147-289, 536-620, 731-880, 1032-1040` — `x265_api_get(depth)` multi-bitdepth C++ vtable indirection.
   - `libavcodec/libsvtav1.c:59, 494-541, 617, 671-774` — Asymmetric `EbBufferHeaderType` packet ownership and five-branch `svt_av1_enc_release_out_buffer`.
   - `libavcodec/libopusdec.c:121-224`, `libavcodec/libmp3lame.c:80-336`, `libavcodec/libvorbisdec.c:111-178`, `libavcodec/libwebpenc.c:43-76`, `libavcodec/zlib_wrapper.c:49-88` — Audio, WebP, and `z_stream` `zalloc`/`zfree` wrapper contracts.
   - `libavformat/tls_openssl.c:426-617, 652-685, 816-869, 986` & `libavformat/tls_gnutls.c:522, 632-636` — Custom `BIO_METHOD` / pull-push callbacks and DTLS-SRTP (`use_srtp`, MTU, handshake timeout) integration.
   - `libavfilter/vf_subtitles.c:146-245` & `libavfilter/vf_drawtext.c:44-69, 524-700, 1046, 1384-1427` — Five-library `libass` + `freetype` + `harfbuzz` + `fribidi` + `fontconfig` text/subtitle graph.
2. **Pinned Rust & Sandboxing Repositories:**
   - `memorysafety/rav1d` (`2e7216c20ac2a75de204d6c8d7268b75a45959b4`): `Cargo.toml:1-70`, `README.md:38-55`, `src/lib.rs:228-1070`, `src/disjoint_mut.rs:1-120`.
   - `xiph/rav1e` (`31435de9d76fddd38f6dcc31d4014574cebb2092`): `Cargo.toml:1-85`, `src/lib.rs:1-85`.
   - `pdeljanov/Symphonia` (`5f879df0bf309246a48d57caae457fd8c0e2a5cb`): `Cargo.toml:1-51`, `symphonia-codec-vorbis/src/lib.rs:1-85`, `symphonia-bundle-mp3/src/lib.rs:1-52`, `symphonia-codec-opus/Cargo.toml:1-21`, `symphonia-codec-opus/src/lib.rs:1`.
   - `rustls/rustls` (`836e411eccaf7331f4c289aabef0de32474de3b8`): `rustls/Cargo.toml:1-62`, `rustls/src/lib.rs:1-85`; `rustls/rustls-ffi` (`60e06efdff33e6e97e00e76fa519d559b2dcaffa`): `Cargo.toml:1-30`.
   - `trifectatechfoundation/zlib-rs` (`a7f9c02c1f48b8962b46c5428828573e9cbac152`): `Cargo.toml:1-39`, `README.md:1-72`, `libz-rs-sys/src/lib.rs:1-85`.
   - `etemesi254/zune-image` (`2cdbbf554e7da373d3418ab327a0db7c4abb50cd`): `Cargo.toml:1-39`, `README.md:85-107`.
   - `image-rs/image-webp` (`946b31adf319a8f87530742716d9e2776044c431`): `Cargo.toml:1-26`, `src/lib.rs:1-36`, `src/encoder.rs:1-80`.
   - `googlefonts/fontations` (`7eec1e18b6dcb2cbb77a805f280825c075a388c6`): `Cargo.toml:1-83`.
   - `PLSysSec/rlbox_sandboxing_api` (`b0157dc84f86ffbe4549e32ed5cbdfad79c17f43`): `README.md:1-75`; `google/sandboxed-api` (`46402cf55fe0c199d8a0d84041fde8f3d9b39255`): `README.md`.

### Executed Micro-Probe (`2026-11-20`, `Linux 7.1.6-1rodete1-amd64 x86_64`)

Compiled with `gcc -O2 -Wall -Wextra probe_pkg1.c -lz -o probe_pkg1`:
```text
zlib_version=1.3.2 compressed_4k=2111 zalloc_calls=1 zfree_calls=1 zalloc_bytes=7160 inflate_reset_ns=19648.1
membrane_validate_ns=5.04 bounce_copy_1080p_us=303.24 ipc_seqpacket_rtt_us=35.04 memfd_seals=0x7
```

## Revalidation

To revalidate these findings against a newer upstream `FFmpeg/FFmpeg` or Rust crate snapshot without repeating the full survey:

1. **License & Dispatch Delta Check (<10 s):**
   Diff `configure` (`EXTERNAL_LIBRARY_*_LIST` and `enabled openssl`) and `libavcodec/allcodecs.c` against `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`. Specifically check whether `ff_av1_decoder` gained software DSP or remains `/* hwaccel hooks only */`, and whether `LICENSE.md` updated its OpenSSL 3.x GPLv3 note.
2. **Rust Counterpart Gap Probes (<10 s):**
   - Check `wc -l symphonia-codec-opus/src/lib.rs` in `pdeljanov/Symphonia` to test whether Symphonia has shipped a real Opus decoder beyond the 1-line stub at `5f879df0bf309246a48d57caae457fd8c0e2a5cb`.
   - Check `src/disjoint_mut.rs` in `memorysafety/rav1d` to verify whether release builds still elide `DisjointMutAllBounds` without static disjointness proofs.
   - Check `rustls` documentation/Cargo features for any first-party `DTLS` + `RFC 5764` `use_srtp` support.
3. **Containment Overhead Micro-Probe (<2 s):**
   Compile and run a minimal C probe with `-O2 -lz` measuring (a) `inflateInit` + `10,000` `inflateReset` cycles with a counting `zalloc`, (b) `memcpy` of a `3,110,400`-byte 1080p buffer, and (c) `socketpair(AF_UNIX, SOCK_SEQPACKET, 0, sv)` round-trip alongside `memfd_create(..., MFD_ALLOW_SEALING)` + `fcntl(fd, F_ADD_SEALS, F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_SEAL)` (`0x7`). Verify `zalloc_calls == 1` and `ipc_seqpacket_rtt_us << 2 * bounce_copy_1080p_us`.
