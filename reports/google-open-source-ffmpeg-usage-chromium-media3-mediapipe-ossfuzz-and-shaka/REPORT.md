# Public Google-Affiliated Open-Source FFmpeg Integrations: Build Profiles, C-ABI Surfaces, Sandboxing Boundaries, and Fuzzing Harnesses

## Summary

A primary-source audit of 18 publicly accessible open-source repositories affiliated with Google (`chromium/chromium` and its `third_party/ffmpeg` fork, `WebRTC`, `AndroidX Media3`, `Fuchsia` and its `third_party/ffmpeg` fork, `YouTube Cobalt`, `OpenScreen`, `OSS-Fuzz` + upstream `FFmpeg`, `MediaPipe`, `TensorFlow I/O`, `TensorFlow Datasets`, `Shaka static-ffmpeg-binaries` & `Shaka Packager`, `Android Emulator QEMU`, `ChromiumOS overlay`, and `Sandboxed API` / `Sandbox2`) establishes five structural realities governing how production systems consume, isolate, and replace FFmpeg:

1. **Extreme C-ABI and component narrowing in security-critical clients.** Chromium exports **exactly 54 C functions** across all of FFmpeg (`chromium/ffmpeg.sigs:8-68`: `21` `libavcodec`, `10` `libavformat`, `23` `libavutil`, and **zero** from `libswscale`, `libswresample`, `libavfilter`, or `libavdevice`), compiles **zero encoders, zero muxers, zero bitstream filters, and zero network protocols** (`--disable-everything --disable-all --disable-network --disable-error-resilience`), restricts FFmpeg video decoding solely to **H.264** (`media/filters/ffmpeg_video_decoder.cc:120-123`), and already intercepts FLAC, MP3, Vorbis, and 13 PCM variants in pure safe Rust via `SymphoniaAudioDecoder` (`media/filters/symphonia_audio_decoder.cc:48-95`). Similarly, Fuchsia's isolated `codec_runner_sw_ffmpeg` component registers **only `AV_CODEC_ID_H264`** (`avcodec_context.cc:17`), and AndroidX Media3 disables `libavformat`, `libswscale`, `libavfilter`, and all video decoders (`build_ffmpeg.sh:37-48`).
2. **Multi-SONAME dynamic loading exists solely to survive Linux distro ABI churn.** Because Linux distributions ship incompatible `libavcodec.so.{54,56,57,58,59,60,61}` struct layouts, `YouTube Cobalt` vendors **seven separate FFmpeg/Libav header trees** (`third_party/ffmpeg_includes`) and instantiates per-ABI C++ template specializations dispatched via `dlopen(..., RTLD_NOW | RTLD_GLOBAL)` + `dlsym` (`starboard/shared/ffmpeg/ffmpeg_dynamic_load_dispatch_impl.cc:184-358`). Any drop-in replacement targeting Linux TV/desktop ecosystems must preserve symbol-versioned SONAMEs and exact `AVCodecContext`/`AVFrame` field offsets per major ABI.
3. **FFmpeg's C-ABI ownership asymmetries repeatedly induce subtle memory and assertion bugs in C++ wrappers.** Direct source inspection uncovers: (a) a tautological bitwise-OR capability check `RTC_DCHECK(context->codec->capabilities | AV_CODEC_CAP_DR1)` in WebRTC (`h264_decoder_impl.cc:95`), which always evaluates true even when `AV_CODEC_CAP_DR1` is absent; (b) `av_packet_unref` instead of `av_packet_free` inside AOSP QEMU's `AVDeleter<AVPacket>` (`AVScopedPtr.h:57-62`), leaking heap `AVPacket` structs allocated by `av_packet_alloc()`; (c) manual `av_free(p->buffer)` before `avio_context_free(&p)` in `TensorFlow I/O` (`ffmpeg_kernels.cc:94-99`), violating Chromium's documented invariant (`ffmpeg_glue.cc:95-97`) that FFmpeg may reallocate `AVIOContext::buffer` internally; and (d) silent decoder deadlocks in FFmpeg's VP8 frame-threading implementation when `thread_count >= 10` (`OpenScreen` `decoder.cc:166-170`) and broken `avcodec_flush_buffers` state resets on TrueHD audio (`Media3` `ffmpeg_jni.cc:196-210`).
4. **Shared-memory sandboxing requires explicit single-copy packet ingestion to prevent double-fetch TOCTOU.** Fuchsia runs FFmpeg in a dedicated low-privilege Zircon component (`codec_runner_sw_ffmpeg`) and intentionally leaves `AVPacket::buf = nullptr` when reading from client-shared Zircon VMOs so `avcodec_send_packet()` $\to$ `av_packet_ref()` copies compressed NAL bytes once into FFmpeg-private padded heap memory before parsing (`avcodec_context.cc:85-93`). Meanwhile, `google/sandboxed-api` (`SAPI`) does **not** ship an auto-generated RPC stub wrapper for `libavcodec` because FFmpeg's heavy reliance on synchronous reverse callbacks (`get_buffer2`, `get_format`, `AVIOReadOperation`) and cyclic `AVFormatContext` pointer graphs defeats automatic libclang pointer marshalling without custom shared-memory framing.
5. **OSS-Fuzz leaves 100% of external NASM/GAS SIMD assembly unexercised.** In `google/oss-fuzz` (`projects/ffmpeg/build.sh:161-170`), `FFMPEG_BUILD_ARGS` unconditionally sets `--disable-asm` on **both `x86_64` and `i386`** across all engines (`libfuzzer`, `afl`, `honggfuzz`) and sanitizers (`address`, `memory`, `undefined`). Furthermore, numerous production builds disable x86 assembly due to PIC text-relocation or toolchain errors (`Media3` Android `x86`/`x86_64`, `Shaka` macOS `x86_64`, `ChromiumOS` 32-bit `x86` PIC and `x32`, and `Chromium` Linux MSan).

## Applicability

Every repository, commit revision, build script, and source file analyzed in this report is publicly hosted on GitHub or Google's public Gitiles servers (`*.googlesource.com`). No closed-source or internal systems are examined or referenced.

The 18 pinned subjects in `REPORT.json` form five functional groups:
- **Browser, OS, and Cast runtimes with first-party FFmpeg GN builds:** `chromium/chromium` (`648b13abcacc62aac505c43912eccb0ee61fd3e7`) + `chromium.googlesource.com/chromium/third_party/ffmpeg` (`09dee08662c5d06155391829174a8fd2e8c0556d`), `webrtc.googlesource.com/src` (`abd0f2fdedae0ad4f582b9932887fee9ab6f8741`, mirrored at `chromium.googlesource.com/external/webrtc`), `fuchsia.googlesource.com/fuchsia` (`ad6d7483fedc4fc4175815f368b14d22fa3755d2`) + `fuchsia.googlesource.com/third_party/ffmpeg` (`affc7077aaa2d3b32e1127a741bd8b8166259b97`), `chromium.googlesource.com/openscreen` (`c0ffd4c7b1535d6c4db05a517d7d9c3cc64e761c`), and `chromium.googlesource.com/chromiumos/overlays/chromiumos-overlay` (`87341f8268c9b055c6e78a09a8b638c664f099d3`).
- **Mobile, Smart-TV, and Emulator C/JNI wrappers:** `androidx/media` (`8c6678b657ede1e7883fc164ef73ed483c7796c3`), `youtube/cobalt` (`8eb3fbbbe657b9244eaca91ff6cb2680e87c1b42`), and `android.googlesource.com/platform/external/qemu` (`ae9d18d2b6261179fbd57fffec720a04f7bfb053`).
- **ML data ingestion pipelines:** `google-ai-edge/mediapipe` (`4a9d08e7469d839e398feb61a9f652b1998e79b6`), `tensorflow/io` (`874651829d08ebe5079427c99ad8f0f241ef9336`), and `tensorflow/datasets` (`252301af4a62f264bddf16491fd0bfe57db8140f`).
- **Cloud packaging and static CLI distribution:** `shaka-project/static-ffmpeg-binaries` (`10f9959c1ad5afee3030123d15276d505ef3bb0b`) contrasted against `shaka-project/shaka-packager` (`323ac9edf1720356e5f5da8bca4f8a9801635fcd`).
- **Fuzzing and Linux sandboxing infrastructure:** `google/oss-fuzz` (`cdd107021c20428647db0699c33d6cb1f717474a`), `FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`), and `google/sandboxed-api` (`46402cf55fe0c199d8a0d84041fde8f3d9b39255`).

This report builds upon existing corpus analyses of browser/IPC membranes (`browser-site-isolation-v8-heap-sandboxes-and-webidl-membrane-security`), shared-memory double-fetch logics (`double-fetch-toctou-shared-dma-rings-and-single-fetch-logics`), FFI strangulation (`incremental-c2rust-lifting-mvee-shadow-execution-and-ffi-strangulation`), and Rust media codec rewrites (`rust-media-codec-rewrites-perf-and-safety-rav1d-symphonia-wuffs-zune-nihav`).

## Findings

### 1. Build Configuration, Component Allowlists, and Assembly Policy Matrix

`Basis: source`

Across the audited projects that compile FFmpeg from source (rather than linking a system package), build configurations split starkly between **minimalist in-process decoder builds** and **full-pipeline static CLI/fuzz builds**:

| Project & Script | Base Policy Flags | Enabled Libraries | Enabled Codecs & Demuxers | Assembly & Linker Flags |
| :--- | :--- | :--- | :--- | :--- |
| **Chromium** (`Chrome/linux/x64/config.h`, `BUILD.gn:29-85`, `ffmpeg_options.gni:10-70`) | `--disable-everything --disable-all --disable-network --disable-error-resilience --disable-symver --disable-autodetect --enable-lto --optflags="-O2"` | `avcodec`, `avformat`, `avutil` (`libopus` external) | **15 decoders:** `h264`, `aac` (`Chrome` branding only), `vorbis`, `libopus`, `flac`, `mp3`, `9` PCM variants. **7 demuxers:** `ogg`, `matroska`, `wav`, `flac`, `mp3`, `mov`, `aac`. **7 parsers:** `aac`, `flac`, `h264`, `mpegaudio`, `opus`, `vorbis`, `vp9`. **0 encoders/muxers.** | NASM (`-W+error=all`) on `x86`/`x64` except `linux-noasm` (MSan); `-Wl,-z,notext` required on 32-bit `x86` with `lld`/`mold` due to `x86inc.asm` textrels (`BUILD.gn:22-31, 81`) |
| **AndroidX Media3** (`libraries/decoder_ffmpeg/src/main/jni/build_ffmpeg.sh:31-132`, `CMakeLists.txt:29-64`) | `--target-os=android --enable-static --disable-shared --disable-everything --disable-symver` | `avutil`, `avcodec`, `swresample` (`avformat`, `swscale`, `avfilter`, `avdevice`, `postproc` all **disabled**) | Caller-passed `ENABLED_DECODERS` audio list (e.g., `vorbis opus flac` or `aac ac3 eac3 dca mlp truehd mp3 alac pcm_mulaw pcm_alaw`); **0 video decoders, 0 demuxers** | ARMv7 (`-march=armv7-a -mfloat-abi=softfp -Wl,--fix-cortex-a8`) & AArch64 (`-Wl,-Bsymbolic` in `CMakeLists.txt:62-64`) keep GAS asm; **`--disable-asm` forced on Android `x86` and `x86_64`** (`lines 114, 128`) |
| **Fuchsia** (`third_party/ffmpeg/BUILD.gn:20-245`, `fuchsia/.../avcodec_context.cc:17`) | Custom GN `shared_library("ffmpeg")` per `$ffmpeg_profile/$current_cpu`; `-std=c99 -fno-tree-vectorize -fomit-frame-pointer` | `avcodec`, `avformat`, `avutil` (`opus` dep) | `codec_runner_sw_ffmpeg` exposes **only `video/h264` (`AV_CODEC_ID_H264`)** (`avcodec_context.cc:17`) | YASM (`-w`) on `x64`, GAS `.S` on `arm64`; `-Wl,-Bsymbolic` to avoid PIC relocation errors from assembly (`BUILD.gn:236-237`); `-fno-tree-vectorize` explicitly passed (`line 232`) |
| **OSS-Fuzz** (`projects/ffmpeg/build.sh:160-385`) | **Two-pass build:** `--enable-ossfuzz --optflags=-O1 --enable-gpl --enable-nonfree --disable-muxers --disable-protocols --disable-demuxer=rtp,rtsp,sdp --disable-devices --disable-shared` | Static `libav*` + static `bzip2`, `zlib`, `libxml2`, `freetype`, `fribidi`, `harfbuzz`, `fontconfig`, `libass`, `fdk-aac`, `libvpx`, `ogg`, `opus`, `theora`, `vorbis` | **Pass 1:** All built-in + external decoders, encoders, BSFs, `sws`, `swr`, `dem`, `io_dem`. **Pass 2 (`lines 327-359`):** `make distclean`, then `--disable-decoders --disable-encoders --disable-parsers --disable-bsfs --disable-filters` to build smaller per-demuxer fuzzers | **`--disable-asm` unconditionally on `x86_64` (`line 165`)**; `--disable-inline-asm --disable-asm` on `i386` (`line 163`); `-fno-sanitize=vptr` globally (`line 19`); `-fno-sanitize=shift-base,signed-integer-overflow` on `fdk-aac` (`line 102`) |
| **Shaka Static Binaries** (`build-scripts/90-ffmpeg.sh:25-95`, `build-matrix.json:3-88`) | `--pkg-config-flags="--static" --disable-ffplay --enable-runtime-cpudetect --enable-gpl --enable-version3 --enable-static` | Full `ffmpeg` + `ffprobe` CLI linking `libvpx`, `libsvtav1`, `libx264`, `libx265`, `libmp3lame`, `libopus`, `mbedtls` | Default full upstream codecs/muxers/demuxers/filters; Alpine `3.20` (`-static` musl, no hwaccel) vs. Ubuntu `22.04`/`24.04`/`26.04` (`--enable-vaapi --enable-nvenc` + `ffmpeg-nvenc-jammy.patch`), macOS (`--enable-videotoolbox`), Windows (`--target-os=mingw64`) | **`--disable-x86asm --disable-inline-asm` forced on macOS `x86_64`** due to 32-bit absolute addressing relocation errors (`90-ffmpeg.sh:55-60`); `--enable-pic` required on macOS `arm64` to prevent runtime crashes (`line 62`) |
| **ChromiumOS Overlay** (`media-video/ffmpeg/ffmpeg-6.1.1.ebuild:74-578`) | Gentoo multilib ebuild (`FFMPEG_SUBSLOT=58.60.60`), `--enable-static --disable-shared --enable-avfilter --disable-optimizations --disable-libcelt` | System `/usr/local` static libs + optional `emake libffmpeg` when `USE=chromium` (`lines 393-394, 555-556`) | USE-flag parameterized (`+dav1d`, `rav1e`, `svt-av1`, `vpx`, `opus`, `vaapi`, `v4l2`, `vulkan`, etc.); applies **6 custom patches** (`lines 355-362`) including `chromium-r2.patch`, `ffmpeg-6.0-fix-lto-type-mismatch.patch`, `HWACCEL_CAP_RESET_WITHOUT_UNINIT`, and `ffmpeg-vp8-dim-reset.patch` | `--disable-asm` forced when `USE=pic` on 32-bit `x86` (`line 467`: `"the provided asm decidedly is not PIC for x86"`) and on `x32` (`line 469`); LTO disabled on 32-bit `x86` (`line 483`) |

---

### 2. Chromium's 54-Function C-ABI Surface and Active Rust/C Strangulation

`Basis: source`

Inspecting `chromium/chromium` (`648b13abcacc62aac505c43912eccb0ee61fd3e7`) alongside its pinned `third_party/ffmpeg` repository (`09dee08662c5d06155391829174a8fd2e8c0556d`) provides an exact blueprint for incremental FFmpeg replacement:

1. **Exhaustive 54-Function C-ABI Allowlist (`chromium/ffmpeg.sigs:8-68`):**
   When Chromium builds FFmpeg as a shared component (`is_component_ffmpeg`, `ffmpeg_options.gni:31`), Windows `.def` symbol export generation (`BUILD.gn:94-116`) restricts the entire browser's linkable FFmpeg surface to **54 functions**:
   - **`libavcodec` (21 functions, `lines 8-28`):** `avcodec_alloc_context3`, `avcodec_free_context`, `avcodec_find_decoder`, `av_new_packet`, `avcodec_open2`, `avcodec_get_name`, `av_packet_unref`, `av_init_packet`, `avcodec_flush_buffers`, `avcodec_align_dimensions`, `av_packet_get_side_data`, `av_packet_copy_props`, `avcodec_descriptor_next`, `avcodec_descriptor_get`, `avcodec_parameters_to_context`, `avcodec_send_packet`, `avcodec_receive_frame`, `av_packet_alloc`, `av_packet_free`, `avcodec_align_dimensions2` (plus legacy declarations).
   - **`libavformat` (10 functions, `lines 32-41`):** `avformat_close_input`, `avformat_find_stream_info`, `avformat_open_input`, `av_read_frame`, `av_seek_frame`, `avformat_alloc_context`, `avformat_free_context`, `avio_alloc_context`, `avio_close`, `av_stream_get_first_dts`.
   - **`libavutil` (23 functions, `lines 46-68`):** `av_get_bytes_per_sample`, `av_rescale_q`, `av_malloc`, `av_free`, `av_log_set_level`, `av_dict_set`, `av_dict_free`, `av_dict_count`, `av_dict_get`, `av_dynamic_hdr_smpte2094_app5_to_t35`, `av_samples_get_buffer_size`, `av_image_check_size`, `av_buffer_create`, `av_buffer_get_opaque`, `av_get_cpu_flags`, `av_force_cpu_flags`, `av_max_alloc`, `av_strdup`, `av_strerror`, `av_frame_clone`, `av_frame_unref`, `av_frame_free`, `av_frame_alloc`.

2. **Defense-in-Depth Demuxer Hardening (`media/filters/ffmpeg_glue.cc:86-160`):**
   Even though unsupported codecs and demuxers are compiled out of Chromium's bundled `third_party/ffmpeg`, Linux distribution packagers sometimes substitute system `libffmpeg.so` (`ffmpeg_options.gni:26-30`). To neutralize that supply-chain expansion of attack surface, `FFmpegGlue::FFmpegGlue` enforces runtime allowlists (`format_context_->codec_whitelist = av_strdup(GetAllowedAudioDecoders())` and `format_context_->format_whitelist = av_strdup("ogg,matroska,wav,flac,mp3,mov[,aac]")`, `lines 88-93, 140-141`), sets `AVFMT_FLAG_CUSTOM_IO | AVFMT_FLAG_FAST_SEEK | AVFMT_FLAG_NOH264PARSE` (`lines 113-120`, bypassing FFmpeg's H.264 parser during demuxing in favor of Chromium's own parser), and sets `format_context_->error_recognition |= AV_EF_EXPLODE` (`line 124`) to abort immediately on container syntax errors.

3. **Unsynchronized Threading Hazard in `AVCodecContext` (`media/filters/ffmpeg_video_decoder.cc:131-166`):**
   Inside `FFmpegVideoDecoder::GetVideoBuffer` (`get_buffer2` callback), Chromium explicitly forbids reading `codec_context->width`, `codec_context->height`, or `codec_context->pix_fmt` (`lines 134-142`: `"With threaded decoding, it will contain unsynchronized width/height/pix_fmt values... in a 'missing memory barriers' kind of way"`), reading `frame->format`, `frame->width`, and `frame->height` exclusively and validating via `avcodec_align_dimensions2` + `av_image_check_size`.

4. **Active Strangulation by Specialized C and Safe-Rust Decoders (`media/renderers/default_decoder_factory.cc:89-165`):**
   - **Video (`lines 131-164`):** Hardware GPU decoders run first, followed by `OffloadingVpxVideoDecoder` (`libvpx` for VP8/VP9), `OffloadingDav1dVideoDecoder` (`dav1d` at `4e3ab21fbbf84a4bd283ea27f96287fcd7c228c1`—note this revision string is recorded in `DEPS`, with `FFmpegVideoDecoder` placed **last** and restricted exclusively to `VideoCodec::kH264`, `ffmpeg_video_decoder.cc:72-88, 120-123`).
   - **Audio (`lines 89-106` and `ffmpeg_audio_decoder.cc:89-99, 147-152`):** `DefaultDecoderFactory::CreateAudioDecoders` registers `SymphoniaAudioDecoder` (`third_party/rust/symphonia*`, handling FLAC, MP3, Vorbis, and all 13 PCM formats via CXX bridge `symphonia_decoder_bridge.rs.h`, `symphonia_audio_decoder.cc:42-95`), `IamfAudioDecoder`, and `OpusAudioDecoder` **before** `FFmpegAudioDecoder`—and `FFmpegAudioDecoder::Initialize` (`ffmpeg_audio_decoder.cc:148`) actively rejects any codec handled by `SymphoniaAudioDecoder` or `OpusAudioDecoder`, shrinking FFmpeg's in-renderer audio decoding footprint in Chrome builds down to **AAC alone**!

---

### 3. Mobile, Embedded, and Multi-SONAME Dynamic-Dispatch Wrappers

`Basis: source`

1. **AndroidX Media3 (`androidx/media` at `8c6678b657ede1e7883fc164ef73ed483c7796c3`):**
   - Because ExoPlayer/Media3 performs all container demuxing in Java/Kotlin (`Extractor` implementations) and video decoding via Android `MediaCodec`, `libraries/decoder_ffmpeg` links **only** static `libavutil.a`, `libswresample.a`, and `libavcodec.a` into `libffmpegJNI.so` (`CMakeLists.txt:29-58`).
   - `ffmpeg_jni.cc:144-157` uses JNI `GetDirectBufferAddress` on Java direct `ByteBuffer`s (`inputData`, `outputData`) to feed `AVPacket::data` without copying from the JVM heap (requiring the Java caller to query `ffmpegGetInputBufferPaddingSize()` = `AV_INPUT_BUFFER_PADDING_SIZE`, `lines 105-107`, and pre-pad the direct buffer!).
   - `ffmpeg_jni.cc:305-330` stashes `SwrContext*` inside `AVCodecContext::opaque` to interleave/convert planar decoded `AVFrame` audio into `AV_SAMPLE_FMT_S16` or `AV_SAMPLE_FMT_FLT`, dynamically growing the Java output buffer via JNI upcall `growOutputBufferMethod` (`lines 160-169, 341`).
   - **Documented upstream FFmpeg stateful reset bug (`lines 195-210`):** `ffmpegReset` cannot call `avcodec_flush_buffers(context)` when `codec_id == AV_CODEC_ID_TRUEHD`; instead it must destroy and recreate the entire `AVCodecContext` (`// Release and recreate the context if the codec is TrueHD. TODO: Figure out why flushing doesn't work for this codec`).

2. **YouTube Cobalt's 7-ABI `FFMPEGDispatch` Layer (`youtube/cobalt` at `8eb3fbbbe657b9244eaca91ff6cb2680e87c1b42`):**
   - Cobalt (`third_party/ffmpeg_includes`) checks in trimmed C header snapshots for **seven historical and modern ABIs**: `libav.54.35.1`, `libav.56.1.0`, `ffmpeg.57.107.100`, `ffmpeg.58.35.100`, `ffmpeg.59.37.100`, `ffmpeg.60.31.102`, and `ffmpeg-7.1.1` (`libavcodec` major `61`, `libavformat` `61`, `libavutil` `59`).
   - At startup, `FFMPEGDispatchImpl::OpenLibraries` (`starboard/shared/ffmpeg/ffmpeg_dynamic_load_dispatch_impl.cc:184-252`) iterates registered `(avutil, avcodec, avformat)` major-version triples from newest to oldest, calling `dlopen("libavutil.so.<V>", RTLD_NOW | RTLD_GLOBAL)` and resolving **only ~22 C symbols** via `dlsym` (`lines 265-333`), dynamically branching between legacy `avcodec_decode_audio4`/`avcodec_decode_video2` (`< kAVCodecHasUniformDecodeAPI`) and modern `avcodec_send_packet`/`avcodec_receive_frame` (`lines 311-317`). It computes `specialization_version() = (avcodec_version() >> 16) * 10 + ((avcodec_version() & 0xFF) >= 100)` (`line 357`, using micro version $\ge 100$ to distinguish FFmpeg from the defunct Libav fork!) to dispatch to the matching C++ struct-offset template specialization.

3. **MediaPipe (`google-ai-edge/mediapipe` at `4a9d08e7469d839e398feb61a9f652b1998e79b6`) and TensorFlow I/O (`tensorflow/io` at `874651829d08ebe5079427c99ad8f0f241ef9336`):**
   - `MediaPipe` (`third_party/ffmpeg_linux.BUILD:19-27`) links directly against host `-l:libavcodec.so`, `-l:libavformat.so`, and `-l:libavutil.so` to power `mediapipe/util/audio_decoder.cc` (which implements explicit 33-bit MPEG-TS PTS epoch rollover compensation `kMpegPtsEpoch = 1LL << 33`, `lines 68-71`), while video calculators delegate via OpenCV (`opencv_linux.BUILD`).
   - `TensorFlow I/O` (`tensorflow_io/core/kernels/ffmpeg_kernels.cc:1-210`) compiles custom TensorFlow `OpKernel` readers over `SizedRandomAccessFile` backed by a 4,096-byte `avio_alloc_context` (`line 119`), guarding FFmpeg 3.x vs. 4.x+ struct breaks via `#if LIBAVCODEC_VERSION_MAJOR > 56` (`streams[i]->codecpar` vs. `streams[i]->codec`, `lines 95, 162, 186, 197`)—note that calling removed `av_register_all()` unconditionally at `line 70` breaks compilation against FFmpeg $\ge 5.0$ (`LIBAVFORMAT_VERSION_MAJOR >= 59`), explaining `ffmpeg_kernels_deprecated.cc` in the same directory.

---

### 4. Real-Time Streaming & Emulator C-ABI Ownership Hazards and Bugs

`Basis: source`

Auditing `WebRTC`, `OpenScreen`, `TensorFlow I/O`, and `AOSP QEMU` side by side reveals four concrete C-ABI contract hazards that plague C++ consumers of FFmpeg:

1. **Tautological Bitwise-OR Capability Check in WebRTC (`modules/video_coding/codecs/h264/h264_decoder_impl.cc:95` at `abd0f2fdedae0ad4f582b9932887fee9ab6f8741`):**
   In `H264DecoderImpl::AVGetBuffer2`, line 95 asserts:
   ```cpp
   // Necessary capability to be allowed to provide our own buffers.
   RTC_DCHECK(context->codec->capabilities | AV_CODEC_CAP_DR1);
   ```
   Because `|` is bitwise OR rather than bitwise AND `&` (`AV_CODEC_CAP_DR1 = 1 << 1`), the expression evaluates to a non-zero integer (`true`) **for every possible value of `capabilities`**, rendering the debug check a dead tautology (contrast Fuchsia's correct `ZX_ASSERT(avcodec_context->codec->capabilities & AV_CODEC_CAP_DR1)` at `avcodec_context.cc:44` and OSS-Fuzz's `ctx->codec->capabilities & AV_CODEC_CAP_DR1` at `target_dec_fuzzer.c:167`).
   WebRTC's `H264DecoderImpl` also documents three additional FFmpeg H.264 invariants:
   - **Zero-initialization requirement (`lines 135-138`):** `ffmpeg_buffer_pool_(true)` zero-initializes every newly allocated YUV frame buffer because FFmpeg H.264 error-concealment/padding paths read uninitialized border pixels (`http://crbug.com/390941`).
   - **Contiguous 3-plane allocation (`lines 246-267`):** `AVGetBuffer2` packs Y, U, and V contiguously into a single `AVBufferRef` (`av_frame->buf[0] = av_buffer_create(..., AVFreeBuffer2, ...)`), transferring ownership of a heap `std::unique_ptr<VideoFrame>` through `void* opaque`.
   - **Single-threaded slice mode (`lines 318-321`):** `av_context_->thread_count = 1; av_context_->thread_type = FF_THREAD_SLICE;` because `ffmpeg_buffer_pool_` has a single-thread sequence checker that multi-threaded `get_buffer2` callbacks (`thread_safe_callbacks`) would trip.

2. **FFmpeg VP8 Multi-Thread Deadlock Workaround in OpenScreen (`cast/standalone_receiver/decoder.cc:150-175` at `c0ffd4c7b1535d6c4db05a517d7d9c3cc64e761c`):**
   OpenScreen's Cast Streaming receiver feeds RTP-reassembled frames (pre-padded with `AV_INPUT_BUFFER_PADDING_SIZE` zero bytes in `Decoder::Buffer::Resize`, `lines 27-36`) through `av_parser_parse2` (`PARSER_FLAG_COMPLETE_FRAMES`, `line 152`) into `avcodec_send_packet` with `AV_CODEC_FLAG_LOW_DELAY` (`line 174`) and `FF_THREAD_SLICE | FF_THREAD_FRAME` (`line 173`), but explicitly clamps `context_->thread_count` to `<= 8` because `"FFMPEG's VP8 implementation actually silently freezes if this is 10 or more"` (`lines 166-170`).

3. **`AVPacket` Heap Struct Leak in AOSP QEMU (`android/android-emu/android/recording/AVScopedPtr.h:57-62` at `ae9d18d2b6261179fbd57fffec720a04f7bfb053`):**
   `AVScopedPtr.h` defines RAII deleters for `AVFrame` (`av_frame_free(&fp)`), `SwsContext` (`sws_freeContext`), `SwrContext` (`swr_free(&sp)`), `AVCodecContext` (`avcodec_free_context(&ptr)`), and `AVFormatContext` (`avformat_close_input(&ocp)` / `avio_closep` + `avformat_free_context`), **except** `AVDeleter<AVPacket>`:
   ```cpp
   template <>
   struct AVDeleter<AVPacket> : std::true_type {
       static void deleteFunc(void* pkt) {
           av_packet_unref(static_cast<AVPacket*>(pkt));
       };
   };
   ```
   `av_packet_unref` releases only the reference-counted payload buffer (`pkt->buf`) and resets fields, **leaking the `AVPacket` struct itself** whenever `makeAVScopedPtr(av_packet_alloc())` is used (whereas WebRTC's `ScopedPtrAVFreePacket` at `h264_decoder_impl.cc:75-77` correctly calls `av_packet_free(&packet)`).

4. **`AVIOContext::buffer` Reallocation & `avformat_open_input` Double-Free Traps (`tensorflow/io` `ffmpeg_kernels.cc:91-101, 142-150` vs. `Chromium` `ffmpeg_glue.cc:95-101, 147-160`):**
   - `avformat_open_input(&ps, ...)` **frees `*ps` on failure**, forcing both Chromium (`open_called_` state bit in `ffmpeg_glue.cc:147-149`) and TensorFlow I/O (`format_context_scope.release()` at `ffmpeg_kernels.cc:143`) to implement bespoke two-state destruction paths so C++ smart pointers do not double-free `AVFormatContext`.
   - Worse, FFmpeg's internal `avio` layer is permitted to `av_realloc` / replace `io_context->buffer` dynamically during reads (`ffmpeg_glue.cc:95-97`: `"Don't keep pointers to the buffer since FFmpeg may reallocate it on the fly"`). `TensorFlow I/O`'s deleter (`av_free(p->buffer); avio_context_free(&p);`, `ffmpeg_kernels.cc:94-97`) works *only* if `p->buffer` remains `av_malloc`-owned and non-null at teardown, whereas callers that cache the original `io_buffer` pointer suffer immediate use-after-free / double-free crashes on large reads.

---

### 5. Out-of-Process CLI Pipelines vs. Native Zero-FFmpeg Packaging

`Basis: source`

1. **Architectural Split in the Shaka Ecosystem (`shaka-packager` vs. `static-ffmpeg-binaries`):**
   - **`shaka-project/shaka-packager` (`323ac9edf1720356e5f5da8bca4f8a9801635fcd`) does NOT embed, link, or call FFmpeg.** Inspection of `CMakeLists.txt:1-37` and `packager/third_party/` (`abseil-cpp`, `c-ares`, `curl`, `googletest`, `json`, `libpng`, `libwebm`, `libxml2`, `mbedtls`, `mimalloc`, `mongoose`, `protobuf`, `zlib`) confirms that Shaka Packager implements ISO-BMFF, MPEG-2 TS, WebM (`libwebm`), Widevine/PlayReady/FairPlay CENC/SAMPLE-AES encryption, and HLS/DASH manifest generation natively in C++ without `libavformat` or `libavcodec`.
   - Instead, transcoding in Shaka workflows (`shaka-streamer` and integration tests) runs **`shaka-project/static-ffmpeg-binaries` (`10f9959c1ad5afee3030123d15276d505ef3bb0b`) out of process** as standalone `ffmpeg` and `ffprobe` executables across an 11-target CI matrix (`build-matrix.json:3-88`).
   - `build-scripts/99-check-static.sh:22-57` enforces strict dynamic-dependency hygiene: on Alpine Linux (`musl`), `ldd ffmpeg` **must fail** (proving a 100% static ELF executable with zero shared-library dependencies); on Windows, `ldd ffmpeg.exe` may reference only `/c/Windows/` system DLLs; on macOS, `otool -L` may reference only `/System/Library` and `/usr/lib`. On Ubuntu `22.04`/`24.04`/`26.04`, glibc prevents pure static linking when `--enable-vaapi --enable-nvenc` (`dlopen`ing host GPU drivers) is enabled, and `ffmpeg-nvenc-jammy.patch:1-48` patches FFmpeg 7.1's `configure` (`ffnvcodec >= 11.1.5.1`) and `libavutil/hwcontext_cuda.c:363-370` (`#ifndef JAMMY` around `cuCtxGetCurrent`) to build against Ubuntu 22.04's older NVENC headers.

2. **`TensorFlow Datasets` Subprocess Pipe Boundary (`tensorflow/datasets` at `252301af4a62f264bddf16491fd0bfe57db8140f`):**
   Unlike `tensorflow/io`'s fragile in-process C++ `OpKernel` linking, `tensorflow/datasets` (`core/utils/image_utils.py:81-120` and `core/features/video_feature.py:143-186`) isolates FFmpeg strictly behind `subprocess.run(['ffmpeg', ...], input=stdin, stdout=PIPE, stderr=PIPE, check=True)`, decoding dataset videos into temporary `%010d.png` image sequences (`video_feature.py:152-159`) and staging non-local `epath`/`GFile` URIs to local temporary files when container formats (such as non-fragmented MP4 `moov`-at-tail) cannot stream over `pipe:0` (`lines 42-45, 165-181`).

---

### 6. Process Sandboxing, Shared-Memory TOCTOU Defenses, and SAPI/Sandbox2 Constraints

`Basis: source + derived`

Comparing how Google open-source systems sandbox untrusted media parsing in FFmpeg reveals three distinct isolation architectures and a critical shared-memory vulnerability class:

1. **Fuchsia Component Isolation + VMO Double-Fetch TOCTOU Elimination (`fuchsia` `src/media/codec/codecs/sw/ffmpeg/avcodec_context.cc:73-104`):**
   Fuchsia isolates software H.264 decoding inside a dedicated Zircon process (`codec_runner_sw_ffmpeg`, `BUILD.gn:12-35`) speaking FIDL `fuchsia.mediacodec` over Zircon channels and shared Virtual Memory Objects (`VMO`s). Because a malicious client retaining a writable mapping to the input `VMO` could concurrently mutate compressed NAL bytes between FFmpeg's header length check and slice entropy decode (**shared-memory double-fetch TOCTOU**), `AvCodecContext::SendPacket` (`lines 85-93`) deliberately leaves `packet->buf = nullptr`:
   ```cpp
   // Because packet->buf is left as nullptr (av_packet_alloc() zero-initializes the struct),
   // avcodec_send_packet() -> av_packet_ref() allocates a new FFmpeg heap buffer of size
   // packet->size + AV_INPUT_BUFFER_PADDING_SIZE, zeroes the trailing AV_INPUT_BUFFER_PADDING_SIZE
   // bytes, and copies packet->size bytes from packet->data via a single memcpy() before any
   // bitstream filtering or decoding occurs. This ensures both the required FFmpeg input padding
   // and protection against TOCTOU if the client concurrently modifies the shared input VMO.
   ```
   If `ZX_ASSERT` (`lines 55-68, 113, 135-138`) or memory corruption trips on an adversarial stream, only the ephemeral `codec_runner_sw_ffmpeg` isolate aborts (`line 112`: `"If we can't allocate a frame, abort this isolate process"`).

2. **Chromium In-Renderer Seccomp-BPF + Site Isolation (`media/filters/`):**
   Chromium executes `FFmpegDemuxer` (`FFmpegGlue`), `FFmpegAudioDecoder`, and `FFmpegVideoDecoder` **inside the sandboxed Renderer process** (restricted by Linux seccomp-BPF + user/PID/network namespaces, Windows AppContainer/job tokens, or macOS Seatbelt, partitioned per site origin via Site Isolation), whereas hardware video accelerators run in the GPU/Utility process (`default_decoder_factory.cc:131-143`). Because a memory-corruption exploit in `libavformat` or `libavcodec` H.264 grants arbitrary code execution inside the site's Renderer process (exposing same-site cookies/DOM state and kernel/IPC attack surface), Chromium aggressively shrinks FFmpeg via `ffmpeg.sigs`, `AV_EF_EXPLODE`, `av_max_alloc`, and migration to `Symphonia`, `dav1d`, and `Wuffs` (used for GIF in Blink/Skia, `DEPS` `wuffs_revision`).

3. **`google/sandboxed-api` (`46402cf55fe0c199d8a0d84041fde8f3d9b39255`): Why `Sandbox2` Works for FFmpeg CLI While Auto-Generated `SAPI` Stubs Struggle with `libavcodec`:**
   - `Sandbox2` (`sandboxed_api/sandbox2/policybuilder.h:63-130` and `sandbox2/examples/tool/`) enforces fine-grainedBPF syscall policies (`AllowRead()`, `AllowWrite()`, `AllowSystemMalloc()`, `EnableLandlock()`, read-only bind mounts, zero network namespaces) around out-of-process binaries or custom forkserver workers communicating over `Sandbox2::Comms` sockets and `Sandbox2::Buffer` (`memfd`) shared memory. Wrapping an out-of-process `ffmpeg` worker or a narrow custom framing loop (analogous to Fuchsia's `codec_runner_sw_ffmpeg`) under `Sandbox2` is straightforward.
   - Conversely, SAPI's LLVM `libclang` stub generator (`tools/clang_generator/BUILD`, `README.md:92-93`) automatically wraps C libraries with flat, value/buffer-oriented APIs—such as `zlib`, `libpng`, `libtiff`, `openjpeg`, `libarchive` (`oss-internship-2020/`), and `stringop`/`sum` (`sandboxed_api/examples/`). `libavcodec` and `libavformat` resist naive mechanical SAPI stubbing because `AVFormatContext` and `AVCodecContext` expose deep cyclic struct pointers (`streams[i]->codecpar`, `extradata`), caller-supplied C function-pointer callbacks invoked synchronously mid-call (`AVCodecContext::get_buffer2`, `AVIOContext::read_packet`/`seek`), and multi-megabyte planar `AVFrame` pools where RPC serialization per packet/frame would destroy 4K60 throughput unless redesigned around explicit shared-memory descriptor rings.

---

### 7. OSS-Fuzz Harness Architecture and the `--disable-asm` Verification Blind Spot

`Basis: source`

Inspecting `google/oss-fuzz/projects/ffmpeg` (`cdd107021c20428647db0699c33d6cb1f717474a`) and `FFmpeg/FFmpeg/tools/target_dec_fuzzer.c` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) reveals both the remarkable breadth of FFmpeg's fuzzing matrix and a major structural blind spot:

1. **Automated Per-Component Target Explosion (`projects/ffmpeg/build.sh:233-385`):**
   `build.sh` parses `config_components.h` (`#define CONFIG_<X>_DECODER 1`, `_ENCODER 1`, `_BSF 1`, `_DEMUXER 1`) and compiles **hundreds of dedicated fuzz binaries** (`tools/target_dec_<symbol>_fuzzer`, `target_enc_<symbol>_fuzzer`, `target_bsf_<symbol>_fuzzer`, `target_dem_<symbol>_fuzzer`, plus `target_sws_fuzzer`, `target_swr_fuzzer`, `target_dem_fuzzer`, and `target_io_dem_fuzzer`, each capped at `max_len = 1000000` bytes, `lines 280-308`), executed under `afl`, `honggfuzz`, and `libfuzzer` with `address`, `memory`, and `undefined` sanitizers across `x86_64` and `i386` (`project.yaml:4-25`).

2. **In-Band 1,024-Byte Control Block (`tools/target_dec_fuzzer.c:104-110, 187-450`):**
   When fuzz input `size > 1024` (`line 395`), `LLVMFuzzerTestOneInput` strips the trailing `1024` bytes via `bytestream2_init(&gbc, data + size, 1024)` (`lines 402-403`) to fuzz configuration state alongside packet bytes (`FUZZ_TAG = 0x4741542D5A5A5546ULL` packet delimiter, `line 106`):
   - Mutates `width`, `height`, `bit_rate`, `bits_per_coded_sample`, `sample_rate`, `ch_layout.nb_channels % FF_SANE_NB_CHANNELS`, `block_align`, `codec_tag`, `idct_algo % 25`, `flushpattern`, `skip_frame`, and `extradata` (`lines 404-444`);
   - Toggles `av_parser_init` (`flags & 1`), `FF_COMPLIANCE_EXPERIMENTAL` (`flags & 2`), `AV_EF_AGGRESSIVE | AV_EF_COMPLIANT | AV_EF_CAREFUL | AV_EF_EXPLODE` (`flags & 4/8`), `AV_CODEC_FLAG2_FAST` (`flags & 0x10`, **explicitly skipped for `AV_CODEC_ID_H264` at `line 419`** because `FLAG2_FAST` intentionally permits unsafe/out-of-spec shortcuts in H.264!), motion-vector side-data export (`flags & 0x80`), and `av_force_cpu_flags(0)` (`flags & 0x40`, `line 425`);
   - Enforces `maxiteration = 8096` (`line 104`) and codec-specific `maxpixels` / `maxsamples` divisors (`lines 233-375`, e.g., dividing `maxpixels` by `256` for `H264`/`VP8`, `4096` for `VP9`, and `16384` for `HEVC`/`JPEG2000`) plus custom DR1 allocator `fuzz_video_get_buffer` (`lines 111-161`, using uninitialized `av_buffer_alloc` only for `FFV1` and zeroed `av_buffer_allocz` for all other codecs) to suppress false-positive OOMs and timeouts;
   - Asserts `av_assert0(ret != AVERROR_BUG)` on every `avcodec_receive_frame` and `avcodec_decode_subtitle2` call (`lines 88, 98`).

3. **The Unconditional `--disable-asm` Blind Spot (`projects/ffmpeg/build.sh:161-170`):**
   ```bash
   if [[ "$ARCHITECTURE" == i386 ]]; then
         FFMPEG_BUILD_ARGS='--arch="i386" --cpu="i386" --disable-inline-asm --disable-asm'
   else
         FFMPEG_BUILD_ARGS='--disable-asm'
   fi
   ```
   Because compiler-inserted ASan/MSan/UBSan shadow-memory and coverage instrumentation cannot instrument standalone NASM `.asm` files (causing false-positive MSan uninitialized-read reports and zero coverage guidance), OSS-Fuzz passes **`--disable-asm` unconditionally on `x86_64` as well as `i386`**. Even though `target_dec_fuzzer.c:424-425` contains `if (flags & 0x40) av_force_cpu_flags(0);` (designed to toggle between SIMD and scalar C!), in OSS-Fuzz builds **all external NASM/YASM SIMD kernels (`libavcodec/x86/*.asm`, `libswscale/x86/*.asm`, `libswresample/x86/*.asm`) are compiled out**, and ARM/AArch64/RISC-V `.S` assembly is never compiled at all (`project.yaml:4-6`). Moreover, `fdk-aac` explicitly disables `shift-base` and `signed-integer-overflow` UBSan checks (`build.sh:102`), and all Targets disable `-fsanitize=vptr` (`build.sh:19`). Consequently, **formal ISA verification of assembly kernels (and differential SIMD-vs-scalar equivalence proofs) covers the exact high-severity attack surface—hand-written SIMD overreads, negative-stride pointer arithmetic, and register/stack ABI clobbers—that continuous sanitizer fuzzing cannot see.**

---

### 8. Clean-Rewrite & Modularity Implications Across the Verification Priority Stack

`Basis: derived`

1. **Drop-In C-ABI Compatibility Surface Is Small and Tractable for Major Embedders:** Rather than needing all ~2,500+ public symbols across `libav*` on day one, supporting the **54-symbol Chromium `ffmpeg.sigs` subset** (plus `swr_alloc_set_opts2`/`swr_init`/`swr_convert`/`swr_free` for Media3 and `av_parser_parse2` for OpenScreen, ~62 C functions total) suffices to serve `Chromium`, `WebRTC`, `Fuchsia`, `Media3`, `Cobalt`, and `OpenScreen`!
2. **Eliminate Legacy Ownership Traps in Idiomatic Rust APIs while Preserving Exact C-ABI Shims:** Clean Rust APIs should separate immutable input slices (`&[u8]` without requiring caller-allocated `AV_INPUT_BUFFER_PADDING_SIZE` zero-slop), fallible `Result<Parser, Error>` constructors (eliminating `avformat_open_input`'s free-on-error pointer mutation), and typed RAII `Packet`/`Frame` handles (eliminating `av_packet_unref` vs. `av_packet_free` struct leaks), while the C-ABI compatibility shim faithfully emulates `avformat_open_input` `*ps = NULL` free-on-error semantics and `av_packet_ref` copy-with-padding TOCTOU protection (`Fuchsia` `avcodec_context.cc:85-93`).
3. **Formal Verification Directly Closes OSS-Fuzz's `--disable-asm` Gap:** Because sanitizer fuzzers blind themselves to external `.asm`/`.S` SIMD kernels (`--disable-asm`) and because 32-bit/macOS/Android-x86 builds repeatedly disable assembly over PIC textrel bugs, a clean-room rewrite that combines **machine-checked `x86_64`/`aarch64` assembly/intrinsics equivalence proofs** with **PIC-clean codegen** simultaneously upgrades Priority 1 (UB-freedom in SIMD), Priority 2 (panic-freedom), and Priority 3 (SIMD-vs-scalar equivalence).

## Boundaries

- **Strictly public scope:** This report examines **only** publicly accessible open-source repositories, build scripts, and documentation on `github.com` and `*.googlesource.com`. Any closed-source or non-public software is **not examined** and strictly outside scope.
- **Not examined:** Chromium's full set of historical C diffs listed in `chromium/patches/README` inside `chromium.googlesource.com/chromium/third_party/ffmpeg` and ChromiumOS's `chromium-r2.patch` (`media-video/ffmpeg/files/`) were inventoried at build/config level (`BUILD.gn`, `config.h`, `config_components.h`, `ffmpeg-6.1.1.ebuild`), not line-by-line across every upstream backport patch.
- **Known not to apply (`shaka-packager`):** Despite frequent conflation with FFmpeg-based packagers, `shaka-project/shaka-packager` (`323ac9edf1720356e5f5da8bca4f8a9801635fcd`) **does not link, vendor, or invoke FFmpeg**; FFmpeg in the Shaka project lives in the separate `shaka-project/static-ffmpeg-binaries` repository (`10f9959c1ad5afee3030123d15276d505ef3bb0b`) for out-of-process CLI transcoding.
- **Known not to apply (`google/sandboxed-api`):** `google/sandboxed-api` (`46402cf55fe0c199d8a0d84041fde8f3d9b39255`) **does not** contain an in-tree SAPI wrapper for FFmpeg (unlike `zlib`, `libpng`, `openjpeg`, and `libtiff` in `oss-internship-2020/`); applying SAPI's libclang RPC generator directly to `libavcodec`/`libavformat` does not work out of the box without refactoring synchronous callback pointers (`get_buffer2`, `avio_alloc_context`) and shared-memory frame buffers.
- **Known not to apply (Refuted Attractive Conclusion):** It is **false** that FFmpeg's multi-year OSS-Fuzz integration fuzzes FFmpeg's production SIMD assembly kernels. `projects/ffmpeg/build.sh:165` passes `--disable-asm` unconditionally on `x86_64`, and `project.yaml:4-6` builds only `x86_64` and `i386`.
- **Unsupported:** Building truly static (`-static`) Linux FFmpeg binaries with VAAPI or NVENC hardware acceleration enabled is unsupported under glibc (`shaka-project/static-ffmpeg-binaries/build-scripts/90-ffmpeg.sh:26-36`, `99-check-static.sh:23-32`), requiring dynamic glibc builds per Ubuntu release (`22.04`, `24.04`, `26.04`) whereas pure static builds on Alpine (`musl`) forfeit GPU hardware acceleration.

## Evidence

### Audited Public Open-Source Repositories and Pinned Revisions

| Subject | Public Repository | Immutable Revision (40-hex SHA) | Verified Files & Line Ranges |
| :--- | :--- | :--- | :--- |
| `Chromium` | `chromium/chromium` | `648b13abcacc62aac505c43912eccb0ee61fd3e7` | `DEPS` (`ffmpeg_revision`, `webrtc`, `openscreen`), `media/filters/ffmpeg_glue.cc:27-160`, `media/filters/ffmpeg_video_decoder.cc:38-170`, `media/filters/ffmpeg_audio_decoder.cc:33-160`, `media/filters/symphonia_audio_decoder.cc:48-120`, `media/renderers/default_decoder_factory.cc:20-177`, `third_party/rust/` |
| `Chromium FFmpeg` | `https://chromium.googlesource.com/chromium/third_party/ffmpeg` | `09dee08662c5d06155391829174a8fd2e8c0556d` | `BUILD.gn:1-200`, `ffmpeg_options.gni:1-70`, `chromium/ffmpeg.sigs:1-68`, `chromium/config/Chrome/linux/x64/config.h` (`FFMPEG_CONFIGURATION`), `chromium/config/Chrome/linux/x64/config_components.h` (29 enabled `CONFIG_*` macros) |
| `WebRTC` | `https://webrtc.googlesource.com/src` (`https://chromium.googlesource.com/external/webrtc`) | `abd0f2fdedae0ad4f582b9932887fee9ab6f8741` | `modules/video_coding/codecs/h264/h264_decoder_impl.cc:15-672` (`AVGetBuffer2` `line 95`, `Configure` `lines 290-354`, `Decode` `lines 368-644`) |
| `AndroidX Media3` | `androidx/media` | `8c6678b657ede1e7883fc164ef73ed483c7796c3` | `libraries/decoder_ffmpeg/README.md:1-133`, `libraries/decoder_ffmpeg/src/main/jni/build_ffmpeg.sh:19-132`, `CMakeLists.txt:17-65`, `ffmpeg_jni.cc:20-454` |
| `Fuchsia` | `https://fuchsia.googlesource.com/fuchsia` | `ad6d7483fedc4fc4175815f368b14d22fa3755d2` | `src/media/codec/codecs/sw/ffmpeg/BUILD.gn:1-35`, `src/media/codec/codecs/sw/ffmpeg/avcodec_context.cc:14-210` |
| `Fuchsia FFmpeg` | `https://fuchsia.googlesource.com/third_party/ffmpeg` | `affc7077aaa2d3b32e1127a741bd8b8166259b97` | `BUILD.gn:1-256` |
| `YouTube Cobalt` | `youtube/cobalt` | `8eb3fbbbe657b9244eaca91ff6cb2680e87c1b42` | `starboard/shared/ffmpeg/ffmpeg_dynamic_load_dispatch_impl.cc:28-360`, `third_party/ffmpeg_includes/` (`7` versioned header directories + `README.md:55-62`) |
| `OpenScreen` | `https://chromium.googlesource.com/openscreen` | `c0ffd4c7b1535d6c4db05a517d7d9c3cc64e761c` | `cast/standalone_receiver/decoder.cc:19-252` (`Resize` padding `lines 27-36`, VP8 thread cap `lines 166-175`) |
| `OSS-Fuzz` | `google/oss-fuzz` | `cdd107021c20428647db0699c33d6cb1f717474a` | `projects/ffmpeg/project.yaml:1-26`, `projects/ffmpeg/build.sh:18-388` |
| `FFmpeg` | `FFmpeg/FFmpeg` | `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` | `tools/target_dec_fuzzer.c:59-450`, `tools/target_dem_fuzzer.c` |
| `MediaPipe` | `google-ai-edge/mediapipe` | `4a9d08e7469d839e398feb61a9f652b1998e79b6` | `third_party/ffmpeg_linux.BUILD:19-27`, `mediapipe/util/audio_decoder.cc:46-130` |
| `TensorFlow I/O` | `tensorflow/io` | `874651829d08ebe5079427c99ad8f0f241ef9336` | `tensorflow_io/core/kernels/ffmpeg_kernels.cc:22-210` |
| `TensorFlow Datasets` | `tensorflow/datasets` | `252301af4a62f264bddf16491fd0bfe57db8140f` | `tensorflow_datasets/core/utils/image_utils.py:81-120`, `tensorflow_datasets/core/features/video_feature.py:37-187` |
| `Shaka Static FFmpeg` | `shaka-project/static-ffmpeg-binaries` | `10f9959c1ad5afee3030123d15276d505ef3bb0b` | `build.sh:1-84`, `build-matrix.json:1-93`, `build-scripts/90-ffmpeg.sh:1-96`, `build-scripts/99-check-static.sh:1-62`, `ffmpeg-nvenc-jammy.patch:1-48` |
| `Shaka Packager` | `shaka-project/shaka-packager` | `323ac9edf1720356e5f5da8bca4f8a9801635fcd` | `README.md:11-78`, `CMakeLists.txt:1-37`, `packager/third_party/` |
| `AOSP QEMU` | `https://android.googlesource.com/platform/external/qemu` | `ae9d18d2b6261179fbd57fffec720a04f7bfb053` | `android/android-emu/android/recording/AVScopedPtr.h:1-98`, `ffmpegdefs.h:1-30`, `AvFormat.h:1-29` |
| `ChromiumOS Overlay` | `https://chromium.googlesource.com/chromiumos/overlays/chromiumos-overlay` | `87341f8268c9b055c6e78a09a8b638c664f099d3` | `media-video/ffmpeg/ffmpeg-6.1.1.ebuild:1-585`, `media-video/ffmpeg/files/` |
| `Sandboxed API` | `google/sandboxed-api` | `46402cf55fe0c199d8a0d84041fde8f3d9b39255` | `README.md:10-96`, `sandboxed_api/sandbox2/policybuilder.h:44-130`, `sandboxed_api/examples/`, `oss-internship-2020/` |

## Revalidation

1. **Chromium C-ABI & Rust Strangulation Drift Check:** Fetch `chromium/ffmpeg.sigs` and `chromium/config/Chrome/linux/x64/config_components.h` from `https://chromium.googlesource.com/chromium/third_party/ffmpeg/+/HEAD/` (`?format=TEXT`) alongside `media/renderers/default_decoder_factory.cc` and `media/filters/ffmpeg_video_decoder.cc` in `chromium/chromium`. Count exported function declarations in `ffmpeg.sigs` (currently `54`) and `#define CONFIG_* 1` entries in `config_components.h` (currently `29`) to detect whether `FFmpegAudioDecoder` (AAC) or `FFmpegDemuxer` has been further narrowed or replaced by Rust crates under `third_party/rust/`.
2. **OSS-Fuzz Assembly Blind-Spot Check:** Fetch `https://raw.githubusercontent.com/google/oss-fuzz/master/projects/ffmpeg/build.sh` and `project.yaml`. Check lines around `FFMPEG_BUILD_ARGS` to determine whether `--disable-asm` is still unconditionally passed on `x86_64` or whether a separate `checkasm` / MSan-free SIMD fuzzing build has been added.
3. **WebRTC, Media3, and AOSP QEMU Bug Status Check:**
   - In `webrtc.googlesource.com/src` (`modules/video_coding/codecs/h264/h264_decoder_impl.cc`), grep for `AV_CODEC_CAP_DR1` to check whether `|` has been fixed to `&`.
   - In `androidx/media` (`libraries/decoder_ffmpeg/src/main/jni/ffmpeg_jni.cc` and `build_ffmpeg.sh`), check whether `AV_CODEC_ID_TRUEHD` still requires full context recreation in `ffmpegReset` and whether `x86_64` Android still passes `--disable-asm`.
   - In `android.googlesource.com/platform/external/qemu` (`android/android-emu/android/recording/AVScopedPtr.h`), check whether `AVDeleter<AVPacket>::deleteFunc` still calls `av_packet_unref` instead of `av_packet_free`.
