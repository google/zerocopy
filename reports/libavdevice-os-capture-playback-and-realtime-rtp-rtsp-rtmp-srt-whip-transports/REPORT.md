# OS Capture/Playback Drivers in libavdevice v63 and Live Streaming Transports Across RTP/RTSP, RTMP, SRT/RIST, HLS, and WHIP/WebRTC

## Summary

FFmpeg's device I/O library (`libavdevice` `63.6.100`, major ABI `63`) and live transport layer (`libavformat` `63.21.100`) expose two distinct boundary surfaces: OS kernel/IPC capture and playback drivers built as `AVFMT_NOFILE` extensions over `libavformat`, and 57 registered `URLProtocol` byte/packet schemes plus network muxer/demuxer state machines (`RTSP`, `RTP`/`RTCP`, `HLS`, `WHIP`). Direct inspection of pinned upstream FFmpeg (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) and clean-room Rust counterparts establishes five load-bearing architectural facts for a verified Rust reimplementation:

1. **Device Inventory and Native OS Gaps (`libavdevice` v63):** `libavdevice/alldevices.c` registers exactly **20 input drivers** and **10 output drivers**. Legacy `sdl2` and `opengl` output devices were removed prior to v63, and upstream FFmpeg v63 has **zero native PipeWire (`SPA_DATA_DmaBuf` / XDG Portal ScreenCast) or Windows WASAPI (`IAudioClient`) drivers**—forcing modern Linux audio/Wayland capture through PulseAudio/ALSA/JACK translation shims or root/DRM-master `kmsgrab`, and Windows capture through DirectShow COM graphs.
2. **Kernel Ring & DMA-BUF Zero-Copy Hazards (`libavdevice`):** Zero-copy OS drivers (`v4l2.c` `V4L2_MEMORY_MMAP`, `kmsgrab.c` `AV_PIX_FMT_DRM_PRIME`, `xcbgrab.c` MIT-SHM `AVBufferPool`) transfer kernel/server memory across `AVBufferRef` destructors (`mmap_release_buffer`, `kmsgrab_free_desc`, `free_shm_buffer`), while audio/V4L2 inputs use a 2nd-order Delay-Locked Loop (`TimeFilter`) to align hardware sample clocks against `CLOCK_MONOTONIC`. Upstream v63 exhibits a hard `av_assert0` abort when `v4l2` queued buffers drop to `0`, an unclamped `bytesused` packet copy on compressed V4L2 frames, 32-bit `height * pitch` wraparound and error-path PRIME FD leaks in `kmsgrab`, and `±1.5 ms` jitter-induced clock-frequency modulation in `TimeFilter` at `bw = 1.5 Hz`.
3. **57-`URLProtocol` Whitelist & Stateful Framing (`libavformat`):** All 57 `URLProtocol` symbols in `libavformat/protocols.c` rely on `ffurl_connect` substring whitelist propagation across nested schemes (`crypto+http`, `subfile`, `concat`). Upstream framing contains concrete memory-amplification, $O(N^2)$, and UB hazards: signed 32-bit `fifo_size * 188` overflow in `udp.c`; $O(N^2)$ singly-linked reorder traversal (`134.2M` pointer hops at `queue_size = 16384`, `360.7 ms` in C execution) in `rtpdec.c`; unbounded AV1 Temporal Unit `av_grow_packet` growth in `rtpdec_av1.c`; `65,599`-channel partial-packet memory amplification and signed 32-bit timestamp-delta UB in `rtmppkt.c`; and unvalidated `0x00..0xff` PKCS#7 padding subtraction (`outdata = -239` in C execution) in `crypto.c`.
4. **WHIP / SRTP / ICE Flaws (`whip.c`, `srtp.c`):** FFmpeg's `whip.c` muxer skips STUN `MESSAGE-INTEGRITY` / `USERNAME` checks on incoming Binding Requests, omits `XOR-MAPPED-ADDRESS` in responses, accepts unauthenticated `0x0101` STUN Binding Responses (ignoring Transaction ID, Magic Cookie, and HMAC), and pins `tls_openssl.c` to `SRTP_AES128_CM_SHA1_80`. Worse, `ff_srtp_decrypt` (`srtp.c:162-175`) computes the AES-CTR IV using rollover index `v = roc - 1` on straddling reordered packets while feeding unadjusted `roc` into HMAC-SHA1, dropping every rollover-straddling reordered packet.
5. **Pure-Rust vs Sandboxed BoringSSL/OpenSSL WebRTC Boundary:** Pure-Rust Sans-IO stacks (`algesten/dimpl` `0.9.0` with `--no-default-features --features rust-crypto` inside `algesten/str0m` `0.25.0`) provide `#![forbid(unsafe_code)]`, DTLS 1.2 + 1.3, Extended Master Secret, and RFC 7714 `SRTP_AEAD_AES_{128,256}_GCM`, whereas `webrtc-rs/webrtc` `0.21.1` defaults to `ring`/`aws-lc-sys` C/assembly. When FIPS-140-3 crypto policy mandates BoringSSL or OpenSSL, running DTLS out-of-process inside a `seccomp-bpf` worker while executing SRTP AEAD in-process in verified Rust eliminates per-packet IPC while keeping ~500k+ SLOC of C X.509/DTLS state machines outside the media process.

## Applicability

This technical reference applies directly to:
- **Pinned Upstream Codebases:** FFmpeg `libavdevice` `63.6.100` (`LIBAVDEVICE_VERSION_MAJOR = 63`) and `libavformat` `63.21.100` (`LIBAVFORMAT_VERSION_MAJOR = 63`) at commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, alongside `algesten/dimpl` (`0.9.0`, `e341a902854d96e1ab8aad910ef5ddea5c1598f8`), `algesten/str0m` (`0.25.0`, `54bf16ee84eca2bc39c8b59720338eb0bbd55538`), `webrtc-rs/webrtc` (`0.21.1`, `3c4584ae984a004def73168782fa86d59f12263a`), `webrtc-rs/dtls` (`0.5.4`, `119dc715440843c6a6e7a0fb955fc38d1e7f37ef`), `webrtc-rs/srtp` (`0.8.9`, `33121993cd21e2e75adc1559052bf6901eecd95b`), `Haivision/srt` (`98ac9998f9ba8db41e7118fa867180c1536d1b74`), `veovera/enhanced-rtmp` (`v2`, `40589eb9d38d6555e6cdbbfc5699312995203561`), `scottlamb/retina` (`0.4.22`, `2b6b7fe0a6f6a5bf69d5e9c8d4fd785ccd090873`), `google/boringssl` (`ddd732967025c608598b9984a1ada358fa82f6f0`), `openssl/openssl` (`159cdbc6006afe7676c5e699f624991ce40d911e`), `PipeWire/pipewire` (`415ac8e5b68607e95e57a12b926f9aa104e5ea7b`), `RustAudio/cpal` (`40ff3adea81757326debba6b2befb747a6699d50`), and VideoLAN `librist` (`v0.2.11`).
- **Companion Corpus Boundaries (Cross-Referenced, Not Repeated):** General FFmpeg library topology, CPU feature dispatch, and ABI struct/callback layouts are covered in `ffmpeg-codebase-architecture-cpuflags-dispatch-and-asm-corpus-census` and `ffmpeg-c-abi-libav-struct-layout-callbacks-and-rust-ffi-compatibility-layer`. CVE/OSS-Fuzz memory-safety taxonomies, `AVBufferRef` lifetimes, external codec/crypto replacement boundaries, and hardware-decode APIs (VA-API/NVDEC/Vulkan Video) are covered in `ffmpeg-cve-ub-memory-safety-taxonomy-and-oss-fuzz-failure-modes`, `libavfilter-graph-scheduling-frame-threading-and-avbufferref-lifetime-invariants`, `ffmpeg-external-codec-and-crypto-library-ecosystem-replacement-vs-ffi-contracts`, and `hardware-video-acceleration-apis-vaapi-nvdec-vulkan-video-videotoolbox-mediacodec`. Container mux/demux edge cases for HLS/MPEG-TS/FLV, PipeWire/DRM syncobj IPC internals, NetEq jitter buffering, and TOCTOU shared DMA-ring proofs are treated in `isobmff-mp4-matroska-mpegts-hls-dash-demuxer-muxer-edge-cases-and-fuzz-hazards`, `wayland-explicit-drm-syncobj-dbus-fd-passing-and-pipewire-graph-scheduling`, `webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows`, and `double-fetch-toctou-shared-dma-rings-and-single-fetch-logics`.
- **Execution Qualification:** Quantitative C probe measurements reported here characterize verbatim extracted algorithms (`TimeFilter`, `ff_srtp_decrypt` ROC estimation, `crypto.c` PKCS#7 padding removal, and `enqueue_packet` linked-list traversal) compiled natively on Linux `x86_64` with `gcc -O2`; full live OS hardware capture and unproxied WAN ingest benchmarks are outside this isolated environment's scope.

## Findings

### 1. `libavdevice` v63 (`63.6.100`) Architecture, 30-Driver Census, and Native PipeWire/WASAPI Gaps

Basis: source (`FFmpeg/FFmpeg` `libavdevice/version_major.h:28`, `libavdevice/version.h:32-43`, `libavdevice/avdevice.h:62-391`, `libavdevice/avdevice.c:26-129`, `libavdevice/alldevices.c:30-142`, `libavdevice/Makefile:16-58`, `configure:2048-4137`).

`libavdevice` is FFmpeg's seventh shared library (`LIBAVDEVICE_VERSION_MAJOR = 63`, `Lavd63.6.100`). Rather than introducing an independent packet/frame pipeline, every device driver implements an `FFInputFormat` (`indev_list`) or `FFOutputFormat` (`outdev_list`) flagged `AVFMT_NOFILE` so `avformat_open_input()` / `avformat_write_header()` delegate directly to OS device handles instead of `AVIOContext` (`libavdevice/avdevice.h:40-49`). `avdevice_register_all()` calls `avpriv_register_devices(outdev_list, indev_list)` (`alldevices.c:67-70`), and the library exports ten public C-ABI entry points:
- Metadata/Init: `avdevice_version()`, `avdevice_configuration()`, `avdevice_license()`, `avdevice_register_all()`.
- Category-Filtered Iterators: `av_input_audio_device_next()`, `av_input_video_device_next()`, `av_output_audio_device_next()`, `av_output_video_device_next()` (`alldevices.c:72-142`, filtering `priv_class->category` against `AV_CLASS_CATEGORY_DEVICE_{AUDIO,VIDEO}_{INPUT,OUTPUT}` or generic `DEVICE_{INPUT,OUTPUT}`).
- Control Messages: `avdevice_app_to_dev_control_message()` and `avdevice_dev_to_app_control_message()` (`avdevice.c:26-40`), passing `MKBETAG` FourCC enums (`AVAppToDevMessageType` `'GEOM'`, `'REPA'`, `'PAU '`, `'PLAY'`, `'PAUT'`, `'SVOL'`, `' MUT'`, `'UMUT'`, `'TMUT'`, `'GVOL'`, `'GMUT'`; `AVDevToAppMessageType` `'BCRE'`, `'BPRE'`, `'BDIS'`, `'BDES'`, `'BOFL'`, `'BUFL'`, `'BRD '`, `'BWR '`, `'CMUT'`, `'CVOL'`, `avdevice.h:125-300`).
- Device Enumeration: `avdevice_list_devices()`, `avdevice_list_input_sources()`, `avdevice_list_output_sinks()`, and `avdevice_free_list_devices()` (`avdevice.c:42-129`).

Cross-checking `libavdevice/alldevices.c:30-62` against `libavdevice/Makefile:16-54` yields the complete, exhaustive 30-driver census (20 inputs, 10 outputs):

| Driver Name | Direction (In / Out) | Primary Source Files | OS / Subsystem Target | Transfer / Sync Mechanism |
| :--- | :--- | :--- | :--- | :--- |
| `alsa` | In & Out | `alsa_dec.c`, `alsa_enc.c`, `alsa.c` | Linux ALSA (`libasound`) | Blocking/non-blocking `snd_pcm_readi`/`writei` + `TimeFilter` DLL |
| `android_camera` | In | `android_camera.c` | Android NDK `ACameraDevice` | `AImageReader` callback -> bounded `AVThreadMessageQueue` |
| `audiotoolbox` | Out | `audiotoolbox.m` | macOS/iOS AudioToolbox | 2-buffer `AudioQueueRef` + `queue_callback` ping-pong (`kAudioQueueProperty_CurrentDevice`) |
| `avfoundation` | In | `avfoundation.m` | macOS/iOS AVFoundation | `AVCaptureSession` delegates retaining `CMSampleBufferRef` + `CVPixelBufferLockBaseAddress` |
| `caca` | Out | `caca.c` | Cross-platform (`libcaca`) | ASCII/TTY dither canvas blit |
| `decklink` | In & Out | `decklink_dec.cpp`, `decklink_enc.cpp`, `decklink_common.cpp` | Blackmagic DesktopVideo SDK (C++ COM) | `IDeckLinkInputCallback` / scheduled frame queue + SMPTE 2038/EIA-708 VANC (`libklvanc`) |
| `dshow` | In | `dshow.c`, `dshow_pin.c`, `dshow_filter.c`, `dshow_crossbar.c` | Windows DirectShow (C COM vtables) | `IMemInputPin::Receive` (`dshow_pin.c:290`) copying `IMediaSample` into packet list |
| `fbdev` | In & Out | `fbdev_dec.c`, `fbdev_enc.c`, `fbdev_common.c` | Linux `/dev/fb*` framebuffer | `mmap()` framebuffer copy at timer cadence |
| `gdigrab` | In | `gdigrab.c` | Windows Win32 GDI | `BitBlt` from desktop/HWND `HDC` into DIB section |
| `iec61883` | In | `iec61883.c` | Linux IEEE-1394 FireWire (`libiec61883`) | Isochronous DV/HDV/MPEG-TS ring + packet queue |
| `jack` | In | `jack.c` | Linux/macOS JACK (`libjack`) | Real-time `jack_set_process_callback` -> lock-free `AVFifo` + `sem_t` + `TimeFilter` |
| `kmsgrab` | In | `kmsgrab.c` | Linux DRM/KMS (`libdrm`) | `drmModeGetFB2`/`GetFB` -> `drmPrimeHandleToFD` (`AV_PIX_FMT_DRM_PRIME` zero-copy FD) |
| `lavfi` | In | `lavfi.c` | Internal `libavfilter` graph bridge | `av_buffersink_get_frame_flags` wrapped as `AVFrame*` inside `AVPacket` (`AV_PKT_FLAG_TRUSTED`) |
| `libcdio` | In | `libcdio.c` | Optical CD-DA (`libcdio-paranoia`) | Sector read `2352 B` PCM frames |
| `libdc1394` | In | `libdc1394.c` | IEEE-1394 IIDC industrial cameras (`libdc1394`) | DMA capture ring dequeue/enqueue |
| `openal` | In | `openal-dec.c` | Cross-platform OpenAL (`alcCaptureSamples`) | Polling capture ring buffer |
| `oss` | In & Out | `oss_dec.c`, `oss_enc.c`, `oss.c` | BSD/Legacy Linux `/dev/dsp` (`ioctl` OSS) | Synchronous `read()`/`write()` + `SNDCTL_DSP_GETISPACE` |
| `pulse` | In & Out | `pulse_audio_dec.c`, `pulse_audio_enc.c`, `pulse_audio_common.c` | PulseAudio (`libpulse-simple` / async mainloop) | Threaded mainloop `pa_stream_peek`/`drop` + `TimeFilter` DLL |
| `sndio` | In & Out | `sndio_dec.c`, `sndio_enc.c`, `sndio.c` | OpenBSD/Unix `libsndio` | `sio_read`/`sio_write` + frame-pos wallclock callback |
| `v4l2` | In & Out | `v4l2.c`, `v4l2enc.c`, `v4l2-common.c` | Linux Video4Linux2 (`/dev/video*`) | `VIDIOC_REQBUFS`/`DQBUF`/`QBUF` `V4L2_MEMORY_MMAP` (`AVBufferRef` zero-copy) & `TimeFilter` |
| `vfwcap` | In | `vfwcap.c` | Windows Video for Windows (`capCreateCaptureWindow`) | Legacy `WM_CAP_SET_CALLBACK_VIDEOSTREAM` Win32 message pump |
| `xcbgrab` | In | `xcbgrab.c` | X11 (`libxcb`, `xcb-shm`, `xcb-xfixes`) | `xcb_shm_get_image` via `AVBufferPool` or `xcb_get_image` |
| `xv` | Out | `xv.c` | X11 XVideo extension (`libXv`) | YUV XvImage / XvShmPutImage window render |

Two critical negative-space findings emerge directly from `alldevices.c` and `configure`:
1. **No Native PipeWire Driver:** `libavdevice` v63 has no `pw`/`pipewire` demuxer or muxer. Desktop Linux audio on PipeWire systems passes through compatibility daemons (`pipewire-pulse`, `pipewire-alsa`, `pipewire-jack`), incurring extra IPC daemon hops, while unprivileged Wayland screen/window capture via `org.freedesktop.portal.ScreenCast` + PipeWire `SPA_DATA_DmaBuf`/`SPA_DATA_MemFd` (`PipeWire/pipewire` `spa/include/spa/buffer/buffer.h:34-100`) is absent—leaving Linux screen capture bifurcated between legacy XWayland/X11 (`xcbgrab`) and privileged `CAP_SYS_ADMIN` DRM master capture (`kmsgrab`).
2. **No Native WASAPI Driver:** `libavdevice` v63 has no Windows Core Audio (`IAudioClient`/`IAudioCaptureClient`) device. Windows audio capture relies on DirectShow (`dshow`), which imposes WDM/KS filter-graph latency and omits native WASAPI event-driven shared-mode loopback capture (`AUDCLNT_STREAMFLAGS_LOOPBACK`). By contrast, `RustAudio/cpal` (`src/host/wasapi/stream.rs:39-160`) demonstrates the exact concurrency contract required by WASAPI: `DefaultDeviceMonitor` registers an `IMMNotificationClient` COM callback that signals an auto-reset Win32 `HANDLE` via `SetEvent` and defers disconnect/default-change errors through an `Arc<AtomicBool>` (`pending_device_changed`), explicitly avoiding synchronous user-callback invocation during `Drop` where `UnregisterEndpointNotificationCallback` waits on in-flight notification threads (`stream.rs:91-98`).

### 2. OS Kernel/IPC Zero-Copy Ownership, DMA-BUF/SHM Lifetimes, TimeFilter DLLs, and Verified `libavdevice` Bugs

Basis: source + execution (`FFmpeg/FFmpeg` `libavdevice/v4l2.c:373-655`, `libavdevice/kmsgrab.c:110-364`, `libavdevice/xcbgrab.c:241-290`, `libavdevice/timefilter.c:34-95`, `libavdevice/alsa_dec.c:92-142`, `libavdevice/jack.c:80-191`, `libavdevice/avfoundation.m:151-315, 1342-1465`, `libavdevice/audiotoolbox.m:42-285`, `libavdevice/dshow_pin.c:290-366`, `libavdevice/decklink_dec.cpp:161-985`; `PipeWire/pipewire` `spa/include/spa/buffer/buffer.h:34-100`).

`libavdevice` drivers exhibit four distinct OS memory-ownership models, three of which harbor verified UB, fd-leak, or abort bugs in v63:

1. **Kernel `mmap` Ring + `AVBufferRef` Lease (`v4l2.c`):**
   At stream startup (`mmap_init`, `v4l2.c:373-449`), `VIDIOC_REQBUFS` allocates `s->buffers` kernel-mapped planes (`V4L2_MEMORY_MMAP`), stores `{start, len}` in `s->buf_data`, and tracks queued frames in `atomic_int buffers_queued`. On capture (`mmap_read_frame`, `v4l2.c:544-655`), `VIDIOC_DQBUF` decrements `buffers_queued` and, for `AV_CODEC_ID_RAWVIDEO` when `buffers_queued != max(buffers/8, 1)`, constructs a zero-copy `AVPacket` via `av_buffer_create(start, bytesused, mmap_release_buffer, buf_descriptor, 0)` whose custom destructor re-invokes `VIDIOC_QBUF` (`v4l2.c:466-481`). Four concrete defects exist in this path:
   - **Hard `abort()` on Pool Drain (`v4l2.c:580`):** `av_assert0(atomic_load(&s->buffers_queued) >= 1)` terminates the entire process if downstream consumers hold all `s->buffers - 1` `AVBufferRef`s concurrently or if the driver returns a stale state.
   - **Exact-Equality Pool Exhaustion Check (`v4l2.c:607`):** `atomic_load(&s->buffers_queued) == FFMAX(s->buffers / 8, 1)` triggers copy-fallback at one threshold integer (`==`), rather than `<=`, so jumping past the threshold under concurrent multi-frame dequeues falls back to zero-copy leasing until line 580 aborts.
   - **Unclamped `bytesused` on Compressed Streams (`v4l2.c:582, 598, 610-616`):** For non-raw streams (`MJPEG`/`H.264`), `s->frame_size` is `0`, skipping the equality check at line 598. `bytesused` from `v4l2_buffer` (controlled by virtual kernel drivers such as `v4l2loopback` or malformed USB UVC descriptors) is passed straight into `av_new_packet(pkt, bytesused)` and `memcpy(pkt->data, s->buf_data[buf.index].start, bytesused)` with **no check** that `bytesused <= s->buf_data[buf.index].len`, permitting heap/mmap out-of-bounds reads.
   - **Multiplanar Single-Plane Restriction (`v4l2.c:413-418`):** `V4L2_BUF_TYPE_VIDEO_CAPTURE_MPLANE` hard-fails with `AVERROR_PATCHWELCOME` whenever `buf.length != 1`, rejecting non-contiguous NV12/I420 capture devices (`NV12M`/`YUV420M`).

2. **DRM PRIME DMA-BUF FD Export (`kmsgrab.c`) vs PipeWire `spa_data`:**
   `kmsgrab_read_packet` (`kmsgrab.c:264-364`) queries active CRTC/plane framebuffers (`drmModeGetFB2` or `drmModeGetFB`), exports GEM handles via `drmPrimeHandleToFD(ctx->hwctx->fd, handle, O_RDONLY, &fd)`, packs an `AVDRMFrameDescriptor`, binds `kmsgrab_free_desc` to `frame->buf[0]`, and ships the `AVFrame*` inside `AVPacket` (`AV_PKT_FLAG_TRUSTED`). Two concrete bugs reside in `kmsgrab.c`:
   - **32-Bit Dimension Multiplication Wraparound & Chroma Over-Sizing (`kmsgrab.c:136, 209`):** `size = fb->offsets[i] + fb->height * fb->pitches[i]` multiplies two `uint32_t` fields (`height * pitches[i]`) in 32-bit unsigned arithmetic before widening to `size_t`, and charges full luma `fb->height` even to vertically subsampled chroma planes (`NV12`, `P010`).
   - **PRIME FD Leak on Multi-Plane Failure (`kmsgrab.c:230-260`):** In `kmsgrab_get_fb2`, if `drmPrimeHandleToFD` succeeds for plane `0` (`nb_objects == 1`) and fails for plane `1`, execution jumps to `fail:` (`drmModeFreeFB2(fb)`) and returns before `frame->buf[0]` attaches `kmsgrab_free_desc` (`kmsgrab.c:329`), leaking the already-opened kernel DMA-BUF file descriptor(s) in `desc->objects[0..nb_objects-1].fd`.
   - In contrast, PipeWire's `struct spa_data` / `struct spa_chunk` (`PipeWire/pipewire` `spa/include/spa/buffer/buffer.h:52-92`) transfers `SPA_DATA_MemFd` / `SPA_DATA_DmaBuf` descriptors alongside a shared-memory `spa_chunk` (`uint32_t offset`, `uint32_t size`, `int32_t stride`, `int32_t flags`). Because `spa_chunk` lives in memory writable by the producer daemon/client, PipeWire explicitly requires consumers to validate `offset % maxsize` and clamp `size <= maxsize` after a single volatile read (preventing TOCTOU double-fetch bounds bypasses).

3. **X11 MIT-SHM Pooled Readback (`xcbgrab.c`):**
   `xcbgrab.c:241-290` uses `AVBufferPool` (`allocate_shm_buffer`) backed by `shmget`/`shmat` + `xcb_shm_attach` so `xcb_shm_get_image` writes directly into pooled SHM segments recycled when downstream `AVPacket` refs drop to zero, falling back to socket-copied `xcb_get_image` when SHM is unavailable.

4. **Foreign Callback Threads and `TimeFilter` 2nd-Order DLL Clock Recovery (`timefilter.c`):**
   OS audio/SDI capture APIs deliver frames on real-time foreign threads (`jack_set_process_callback` in `jack.c`, Objective-C `captureOutput:didOutputSampleBuffer:` in `avfoundation.m:182, 284`, Win32 COM `IMemInputPin::Receive` in `dshow_pin.c:290`, C++ COM `IDeckLinkInputCallback` in `decklink_dec.cpp:161-985`, and AudioToolbox `queue_callback` in `audiotoolbox.m:63`). `avfoundation.m:265, 314` stores at most one video and one audio `CMSampleBufferRef` via `CFRetain` under a mutex/lock (`CVPixelBufferLockBaseAddress` at line 1355), dropping overrun frames; `jack.c` copies into a bounded `AVFifo` and posts a POSIX `sem_t`; `decklink_dec.cpp` transfers COM objects via `std::atomic<int> _refs` and `av_buffer_create(..., decklink_object_free, ...)`.

   To map hardware sample clocks onto `CLOCK_REALTIME`/`CLOCK_MONOTONIC` without drift or scheduling-jitter spikes, `alsa_dec.c`, `pulse_audio_dec.c`, `jack.c`, and `v4l2.c` share `TimeFilter` (`libavdevice/timefilter.c:34-95`, implementing Fons Adriaensen's 2nd-order Delay-Locked Loop):
   - Initialization (`ff_timefilter_new`, `timefilter.c:50-64`): For hardware `time_base` ($T_0$), nominal cycle `period` ($P$), and loop bandwidth `bandwidth` ($B_w$, Hz):
     $$\omega = 2\pi B_w P T_0, \quad q(x) = 1 - \frac{1}{1 + x\left(1 + \frac{x}{2}\left(1 + \frac{x}{3}\right)\right)}$$
     $$b_2 = q(\sqrt{2}\,\omega), \quad b_3 = \frac{q(\omega^2)}{P}$$
   - Per-cycle update (`ff_timefilter_update`, `timefilter.c:76-90`): On cycle $n \ge 2$, prediction error $e = t_{\text{sys}} - (t_{\text{cycle}} + \hat{T} P)$ drives:
     $$t_{\text{cycle}} \leftarrow (t_{\text{cycle}} + \hat{T} P) + \max\left(b_2, \frac{1}{n}\right) e, \quad \hat{T} \leftarrow \hat{T} + b_3 e$$
   - **Executed Probe Result (`repro_probes.c`):** Running the verbatim `timefilter.c` equations at $48\text{ kHz}$, $P = 512$ frames ($10.67\text{ ms}$), $B_w = 1.5\text{ Hz}$ (hardcoded in `jack.c:191`) under $+100\text{ ppm}$ hardware clock skew and $\pm 1.5\text{ ms}$ uniform scheduling jitter keeps post-settling timestamp error $\le 716.5\,\mu\text{s}$ across cycles 200–500, but modulates estimated clock skew to `est_ppm = +925.94` ($>9\times$ true drift) because $b_3 \approx 1.96 \times 10^{-5}$ maps $\pm 1.5\text{ ms}$ per-packet jitter directly into $\hat{T}$. Reducing $B_w$ to $0.1\text{–}0.3\text{ Hz}$ (as used in ALSA/Pulse defaults when configured cleanly) shrinks frequency modulation by $100\times$ ($\propto \omega^2$) at the cost of a $\sim 3\text{–}10\text{ s}$ initial settling transient.

### 3. `libavformat` v63 (`63.21.100`) Complete 57-`URLProtocol` Architecture and Security Boundary

Basis: source (`FFmpeg/FFmpeg` `libavformat/protocols.c:27-149`, `libavformat/url.h:32-100`, `libavformat/avio.c:212-265`, `libavformat/udp.c:149, 741`, `libavformat/Makefile`, `configure:4069-4137`).

`libavformat/protocols.c:27-83` declares exactly **57 `URLProtocol` descriptors** (51 explicit struct definitions across 33 `.c` files plus 6 `RTMP_PROTOCOL` macro expansions in `rtmpproto.c:3259-3267`). Every descriptor exposes unbuffered synchronous/poll-backed callbacks (`url_open`/`url_open2`, `url_accept`, `url_handshake`, `url_read`, `url_write`, `url_seek`, `url_close`, `url_get_file_handle`, `url_get_multi_file_handle`) and carries `URL_PROTOCOL_FLAG_NETWORK` (`0x2`), `URL_PROTOCOL_FLAG_NESTED_SCHEME` (`0x1`), and `default_whitelist`:

| Category (Count) | Exact Registered `URLProtocol` Symbols (`ff_*_protocol`) | Implementation File(s) | Scheme(s) & `default_whitelist` / Nesting Behavior |
| :--- | :--- | :--- | :--- |
| **Core Socket / Datagram / FEC (8)** | `udp`, `udplite`, `tcp`, `unix`, `sctp`, `rtp`, `srtp`, `prompeg` | `udp.c`, `tcp.c`, `unix.c`, `sctp.c`, `rtpproto.c`, `srtpproto.c`, `prompeg.c` | Network datagram/stream transports (`FLAG_NETWORK`). `prompeg` adds SMPTE 2022-1 / Pro-MPEG CoP #3 Release 2 2D column/row XOR FEC over UDP; `srtp` wraps `rtp://` via RFC 3711 AES-CM + HMAC-SHA1. |
| **TLS / DTLS Security (2)** | `tls`, `dtls` | `tls.c` + `tls_{openssl,gnutls,mbedtls,schannel,securetransport,libtls}.c` | `FLAG_NETWORK`; wraps `tcp` or `udp` via custom BIOs (`url_bio_method` in `tls_openssl.c:610-616`). Mutual compile-time conflicts enforced in `configure:4861-4865` between GnuTLS/OpenSSL/mbedTLS. |
| **HTTP / Legacy Web / P2P (12)** | `http`, `https`, `httpproxy`, `libcurl`, `icecast`, `mmsh`, `mmst`, `ftp`, `gopher`, `gophers`, `ipfs`, `ipns` | `http.c`, `libcurl.c`, `icecast.c`, `mmsh.c`, `mmst.c`, `ftp.c`, `gopher.c`, `ipfsgateway.c` | `http`/`https` restrict `default_whitelist` to `"http,https,tls,rtp,tcp,udp,crypto,httpproxy,data"`; `libcurl` mirrors HTTP(S) if `prefer_libcurl` is set; `ipfs`/`ipns` rewrite to configured HTTP gateways (`flags = 0`). |
| **RTMP Native + External (13)** | Native: `rtmp`, `rtmpe`, `rtmps`, `rtmpt`, `rtmpte`, `rtmpts`, `ffrtmpcrypt`, `ffrtmphttp`; External: `librtmp`, `librtmpe`, `librtmps`, `librtmpt`, `librtmpte` | `rtmpproto.c`, `rtmpcrypt.c`, `rtmphttp.c`, `librtmp.c` | Native and `librtmp` groups conflict in `configure:4086-4132`. `rtmp{e,s,t,te,ts}` layer over `tcp`, `tls`, `ffrtmpcrypt` (DH+RC4), or `ffrtmphttp` (HTTP polling tunnel). |
| **ARQ / Broker / Remote FS (6)** | `libsrt`, `librist`, `libamqp`, `libzmq`, `libssh`, `libsmbclient` | `libsrt.c`, `librist.c`, `libamqp.c`, `libzmq.c`, `libssh.c`, `libsmbclient.c` | All `FLAG_NETWORK`, wrapping external C/C++ libraries (`srt`, `rist`, `amqp`, `zmq`, `sftp`, `smb`). `libsrt` and `librist` expose socket/FIFO options via `AVOption`. |
| **Local / Combinator / Nested Crypto (16)** | `file`, `fd`, `pipe`, `android_content`, `windows_handle`, `bluray`, `cache`, `concat`, `concatf`, `crypto`, `data`, `md5`, `shared`, `subfile`, `tee`, `async` | `file.c`, `bluray.c`, `cache.c`, `concat.c`, `crypto.c`, `data_uri.c`, `md5proto.c`, `shared.c`, `subfile.c`, `teeproto.c`, `async.c` | `crypto` carries `URL_PROTOCOL_FLAG_NESTED_SCHEME` (`crypto+<url>`); `subfile`, `concat`, `tee`, `cache`, `async` stack child `URLContext`s and inherit `protocol_whitelist`/`blacklist`. |

Two architectural hazards govern `URLProtocol` safety:
1. **Whitelist Inheritance (`avio.c:212-259`):** `ffurl_connect` rejects any child scheme not matching `av_match_list(uc->prot->name, uc->protocol_whitelist, ',')` and falls back to `uc->prot->default_whitelist` when none was supplied. When higher-level demuxers (such as `hls.c:1718` constructing `crypto+https://...`) open dynamic nested URLs, missing or overly broad `protocol_whitelist` strings historically enabled local `file://`/`concat:` read primitives from remote playlists (SSRF).
2. **`udp.c` Signed `fifo_size` Overflow UB (`udp.c:149, 741`):** The `AVOption` `fifo_size` accepts `[0, INT_MAX]` (`int`, default `7 * 4096 = 28,672` 188-byte packets = `5,390,336 B`), and `udp_open` executes `s->circular_buffer_size *= 188;` in signed 32-bit `int` arithmetic—triggering signed integer overflow UB for any `fifo_size > 11,422,785` before allocating `av_fifo_alloc2(s->circular_buffer_size, 1, 0)` (`udp.c:927`). Note also that `udp.c:920-926` spawns a dedicated background `pthread` (`circular_buffer_task_rx`/`tx`) when `fifo_size > 0` on input or `bitrate > 0 && fifo_size > 0` on output.

### 4. RTSP/RTP/RTCP State Machines, Reorder/Jitter Bounds, and H.264/HEVC/AV1 Depacketizers

Basis: normative + source + execution (IETF RFC 3550, RFC 4585, RFC 6184, RFC 7798; AOMedia AV1-RTP v1.0; `FFmpeg/FFmpeg` `libavformat/rtsp.h:39-270`, `rtsp.c:1214-1270, 2140-2245`, `rtpdec.h:36-191`, `rtpdec.c:249-311, 439-531, 633-941`, `rtpdec_h264.c:210-360`, `rtpdec_hevc.c:178-340`, `rtpdec_av1.c:46-464`; `scottlamb/retina` `Cargo.toml:29-48`).

**RTSP Control & Framing:** FFmpeg's `RTSPState` tracks four client states (`RTSP_STATE_IDLE`, `RTSP_STATE_STREAMING`, `RTSP_STATE_PAUSED`, `RTSP_STATE_SEEKING`; `rtsp.h:202-206`) across lower transports (`UDP`, `TCP` `$`-interleaved 4-byte framing `[0x24, channel, len_be16]`, `UDP_MULTICAST`, `HTTP`/`HTTPS` tunneling; `rtsp.h:39-48`). Header line ingestion in `ff_rtsp_read_reply_internal` (`rtsp.c:1267`) issues 1-byte `ffurl_read_complete(rt->rtsp_hd, &ch, 1)` calls per byte on the control socket, whereas `scottlamb/retina` (`0.4.22`) parses RTSP messages and interleaved `$` frames directly from ring-buffered `bytes::BytesMut` slices via Tokio framing without single-byte syscall/wrapper round-trips.

**RFC 3550 Sequence Validation, Jitter Math, and $O(N^2)$ Reorder Queue:**
- *Sequence Validation (`rtpdec.c:249-293`):* Enforces RFC 3550 Appendix A.1 constants `MIN_SEQUENTIAL = 2`, `MAX_DROPOUT = 3000`, `MAX_MISORDER = 100`, tracking 16-bit sequence wraparound via `s->cycles += (1 << 16)` (`RTP_SEQ_MOD`) and two-packet resync (`s->bad_seq`) on large jumps.
- *Jitter & Time Correlation (`rtpdec.c:295-311, 652-679`):* Implements RFC 3550 Appendix A.8 Q4 fixed-point interarrival jitter `s->jitter += d - (int32_t)((s->jitter + 8) >> 4)`, emitting `(s->jitter >> 4)` in RTCP Receiver Reports (`rtpdec.c:373`) alongside RFC 4585 PLI (`RTCP_PSFB`) and 17-packet (`first_missing` + 16-bit `missing_mask`) Generic NACK (`RTCP_RTPFB`, `rtpdec.c:439-531`).
- *Verified $O(N^2)$ Reorder Bottleneck (`rtpdec.h:39`, `rtpdec.c:777-916`):* `RTP_REORDER_QUEUE_DEFAULT_SIZE` is `500` packets (`reorder_queue_size` option). Because `enqueue_packet()` inserts into a singly-linked list (`RTPPacket *queue`) from head to tail using wrap-safe `(int16_t)(seq - cur->seq) < 0` comparisons, a single lost sequence number forces every subsequent in-order arrival to traverse the entire queued prefix up to `queue_size - 1` before flushing when full. Our executed probe (`repro_probes.c`) measures `124,750` pointer traversals (`219.8 µs`) at `cap = 500`, `8,386,560` traversals (`25.00 ms`) at `cap = 4096`, and `134,209,536` traversals (**`360.69 ms`**) at `cap = 16384`, stalling a 60 fps pipeline by $>21$ frame durations in addition to `av_mallocz`/`av_freep` per packet. An indexed power-of-2 ring slot array (`seq & (cap - 1)`) achieves $O(1)$ insertion and zero per-packet heap allocation.

**Codec Payload Depacketizers & Verified Packet-Parsing Hazards:**

| Codec & Spec | Supported Packetization Types | Unsupported (`PATCHWELCOME`) / Edge Conditions | Verified Upstream Parsing Hazards (`FFmpeg/FFmpeg`) |
| :--- | :--- | :--- | :--- |
| **H.264** (`RFC 6184`, `rtpdec_h264.c`) | Single NAL (`1..23`), STAP-A (`24`), FU-A (`28`) | STAP-B (`25`), MTAP-16 (`26`), MTAP-24 (`27`), FU-B (`29`), `packetization-mode > 1` | **`ff_h264_handle_aggregated_packet` pointer OOB (`rtpdec_h264.c:232, 252-253`):** Checks `if (nal_size <= src_len)` before advancing `src += nal_size + skip_between; src_len -= nal_size + skip_between`. When `skip_between > 0` (HEVC DONL mode uses `skip_between = 1` for DOND), `nal_size == src_len` steps `src` 1 byte past the input buffer end (C pointer arithmetic UB). |
| **HEVC** (`RFC 7798`, `rtpdec_hevc.c`) | Single NAL (`0..47`), AP (`48`, optional DONL/DOND), FU (`49`) | `lid != 0` (multi-layer), PACI (`50`) | Rejects `tid == 0` (`rtpdec_hevc.c:221`) and simultaneous `S && E` bits (`317`), but shares `ff_h264_handle_aggregated_packet` (`264-267`) and passes `skip_between = 1` when `using_donl_field` is negotiated. |
| **AV1** (`AOMedia AV1-RTP v1.0`, `rtpdec_av1.c`) | 1-byte Aggr Header `Z\|Y\|W\|N\|000`, OBU elements (`W=0` all LEB-prefixed; `W=1..3` last implicit), TD (`0x12 0x00`) restoration, LEB128 OBU size insertion | Fragmented `OBU_TILE_LIST` (`rtpdec_av1.c:258`), 1-byte final fragment of extended-header OBU (`308-316`) | **Unbounded Temporal Unit heap growth (`rtpdec_av1.c:294`):** Calls `av_grow_packet(pkt, output_size)` across arbitrary `Z=1, Y=1` / non-Marker continuation packets with no upper Temporal Unit cap before `INT_MAX` overflow (`~2 GiB`). Note also dynamic LEB128 header `memmove` (`349-360`) when assembled OBU lengths cross `128`, `16,384`, or `2,097,152` bytes. |

### 5. RTMP and Enhanced-RTMP v2 Chunk-Stream Framing, Amplification, and Signed-Overflow Hazards

Basis: normative + source (`veovera/enhanced-rtmp` `docs/enhanced/enhanced-rtmp-v2.md:328-1755`; `FFmpeg/FFmpeg` `libavformat/rtmppkt.h:29-152`, `rtmppkt.c:138-297`, `rtmpproto.c:57-131, 336-395, 1267-1606`, `flv.h:106-158`, `flvdec.c:1250-1340`).

**Legacy RTMP Handshake & Chunk Multiplexing:**
1. **Handshake (`rtmpproto.c:1267-1420`):** C0/S0 (`1 B` version `3` or `6` for encrypted RTMPE), C1/S1 (`1536 B`: 4B epoch timestamp, 4B version/zero, 1528B random + HMAC-SHA256 digest when schema validation is used), C2/S2 (`1536 B` echo). Encrypted RTMPE (`rtmpcrypt.c`) uses 1024-bit Diffie-Hellman key exchange driving bidirectional RC4 streams.
2. **Chunk Header Compression (`rtmppkt.h:67-72`, `rtmppkt.c:171-297`):** Each chunk opens with a Basic Header encoding `fmt` (`0..3` -> 12/8/4/1-byte message header) and Chunk Stream ID (`csid`: 1 byte for `2..63`, 2 bytes for `64..319`, 3 bytes `AV_RL16(buf) + 64` up to `RTMP_CHANNELS = 65599` at `rtmppkt.h:30`). Messages larger than `in_chunk_size` (default `128 B`, updated via `RTMP_PT_CHUNK_SIZE = 1`, `rtmpproto.c:1575-1606`) interleave across channels at `chunk_size` boundaries.

**Two Verified RTMP Hazards in FFmpeg (`rtmppkt.c`):**
- **65,599-Channel Partial-Packet Memory Amplification (`rtmppkt.c:195-293`):** When a chunk starts a message of declared 24-bit length `size` (up to `16 MiB - 1`) and `size > chunk_size`, `rtmp_packet_read_one_chunk` allocates `ff_rtmp_packet_create(p, channel_id, type, timestamp, size)`, reads only `chunk_size` bytes (`1..128 B`), parks the partially filled `size`-byte buffer in `prev_pkt[channel_id].data`, and returns `AVERROR(EAGAIN)`. Because `ff_rtmp_check_alloc_array` allows up to `65,599` concurrent `csid` slots with zero aggregate byte cap, opening `1,000` channels with 12-byte chunk headers (`12 KB` wire input) allocates **`~16 GiB`** of zero-initialized heap (`>1,000,000x` amplification).
- **Signed 32-Bit Timestamp Delta Overflow UB (`rtmppkt.c:177, 235-236`):** `timestamp` is typed as signed `int` rather than `uint32_t`, so `timestamp += prev_pkt[channel_id].timestamp;` on `fmt != 0` chunks triggers C signed integer overflow UB after `2^31 - 1 ms` (`24.85 days`) of uninterrupted stream uptime or immediately upon an adversarial extended timestamp $\ge 2^{31}$.

**Enhanced-RTMP v1/v2 Wire Extensions (`enhanced-rtmp-v2.md`, `flv.h:106-158`, `rtmpproto.c:357-395`):**
- **Signaling Negotiation (`rtmpproto.c:357-395`):** `NetConnection.connect` encodes AMF0 `fourCcList` (`av01`, `hvc1`, `vp09`, `vvc1`, `Opus`, `fLaC`, `ac-3`, `ec-3`, `avc1`, `mp4a`, `.mp3`; v2 also specifies wildcard `"*"` and `capsEx` bitmask / FourCC-keyed capability flags).
- **Extended Tag Headers (`flv.h:106-158`, `enhanced-rtmp-v2.md:735-1456`):**
  - Video sets `IsExHeader = 1` (MSB `0x80` of `VideoTagHeader[0]`), interpreting bits `6..4` as `VideoFrameType` (`1=key`, `2=inter`, `3=disposable`, `5=command`) and bits `3..0` as `VideoPacketType`: `0=SequenceStart`, `1=CodedFrames` (with 24-bit signed `SI24` composition time offset), `2=SequenceEnd`, `3=CodedFramesX` (elides the 3-byte `CTS` when `PTS == DTS`), `4=Metadata` (AMF-encoded HDR10 `hdrCll`/`hdrMdcv` mastering display metadata parsed in `flvdec.c:1250-1340`), `5=MPEG2TSSequenceStart`, `6=Multitrack` (`OneTrack=0x00`, `ManyTracks=0x10`, `ManyTracksManyCodecs=0x20`), and `7=ModEx` (chains modifiers such as `TimestampOffsetNano`, parsed in `flvdec.c:1330-1340`).
  - Audio uses `SoundFormat == 9` (`FLV_CODECID_EX_HEADER`), interpreting the low nibble as `AudioPacketType`: `0=SequenceStart`, `1=CodedFrames`, `4=MultichannelConfig`, `5=Multitrack`, and `7=ModEx`.

### 6. Low-Latency ARQ Transports (SRT, RIST) and HLS AES-128 Segment Crypto

Basis: normative + source + execution (`Haivision/srt` `srtcore/buffer_rcv.h:45-180`, `srtcore/crypto.h:55-180`; VideoLAN `librist` `v0.2.11` & VSF TR-06-1/TR-06-2; IETF RFC 8216 §4.3.2.4; `FFmpeg/FFmpeg` `libavformat/libsrt.c:39-355`, `librist.c:40-269`, `crypto.c:32-402`, `hls.c:1093-1255, 1705-1732`).

- **Haivision SRT (`libsrt.c`, `Haivision/srt`):**
  Operates over UDP with `1316 B` live-mode default payloads ($7 \times 188\text{ B}$ TS packets, max `1456 B`, `libsrt.c:40-46`). Reliability relies on circular receiver buffering (`CRcvBuffer`, `srtcore/buffer_rcv.h:45-165`), periodic/immediate NAK retransmission lists, Timestamp-Based Packet Delivery (`TSBPD`, 32-bit wrap-aware microsecond playout deadlines), and Too-Late Packet Drop (`TLPKTDROP`) to bound end-to-end latency regardless of persistent loss. Encryption derives a KEK via PBKDF2-HMAC-SHA1 (`passphrase` 10–64 chars, `pbkeylen` $\in \{16,24,32\}$) to key-wrap the rotating 128/192/256-bit Stream Encrypting Key (SEK) via `KMREQ`/`KMRSP` (`kmrefreshrate`, `kmpreannounce`, `libsrt.c:115-120`). Crucially, `Haivision/srt` `srtcore/crypto.h:91-167` enforces bidirectional key separation (`SRT_OPT_SECDIST` / `ForcedRefreshState`) because reusing the same SEK and salt in both directions would leak identical AES-CTR/GCM keystreams under matching packet sequence numbers.
- **RIST (`librist.c`, VSF TR-06-1 / TR-06-2):**
  TR-06-1 Simple Profile uses standard RTP + RTCP (`SDES` + RFC 4585/extended bitmask NACKs + optional RTT echo) at `1316 B` default (`MAX_PAYLOAD_SIZE = 9972 B`, `librist.c:40`) over UDP, enabling standard network-equipment RTP inspection. TR-06-2 Main Profile adds GRE-multiplexed bidirectional tunnels, DTLS/PSK 128/256-bit encryption, and `rist_receiver_set_output_fifo_size` (`FIFO_SIZE_DEFAULT = 8192` in `librist.c:41`). Wrapping C++ `libsrt` or C `librist` inside a Rust binary retains wire compatibility with mature congestion/rate-control loops (`live`/`file` smoothers), whereas clean-room Rust ARQ engines eliminate ~75k SLOC of C++ locking/buffer code if only live-mode constant-bitrate TSBPD + NACK is needed.
- **HLS AES-128 Segment Crypto (`hls.c`, `crypto.c`, RFC 8216 §4.3.2.4):**
  When parsing `#EXT-X-KEY:METHOD=AES-128`, `hls.c:1162-1255` populates a 16-byte IV from explicit `IV=0x...` or falls back to the 64-bit big-endian media sequence number zero-padded in the upper 8 bytes (`memset(iv, 0, 16); AV_WB64(iv + 8, seq)`), then opens `"crypto+" + seg->url` (`hls.c:1714-1725`). Inside `crypto_read` (`crypto.c:186-234`), `MAX_BUFFER_BLOCKS = 257` retains at least 1 trailing 16-byte AES-128-CBC block until upstream EOF so `av_aes_crypt(..., decrypt=1)` strips PKCS#7 padding on the final block; `crypto_seek` (`236-328`) seeks to `(pos / 16 - 1) * 16` to prime the CBC chaining block.
  - **Verified PKCS#7 Underflow & Oracle Bug (`crypto.c:228-233`, Basis: source + execution):** At EOF, `crypto_read` unconditionally executes `int padding = c->outbuffer[c->outdata - 1]; c->outdata -= padding;` with **zero validation** that `1 <= padding && padding <= 16`, `padding <= c->outdata`, or that all `padding` trailing bytes equal `padding`. In our executed C probe (`repro_probes.c`), a single 16-byte block ending in `0xff` drives `c->outdata` from `16` to **`-239`**, causing either silent negative `size` returns/underflow or truncated plaintext without error; worse, unauthenticated CBC PKCS#7 parsing violates authenticated-encryption hygiene whenever segment servers or relays trigger differential retries.

### 7. WHIP / WebRTC (RFC 9725) ICE/STUN/DTLS-SRTP: FFmpeg vs Pure-Rust vs Sandboxed BoringSSL/OpenSSL

Basis: normative + source + execution (IETF RFC 9725, RFC 8445, RFC 8489, RFC 5764, RFC 7714, RFC 9147; `FFmpeg/FFmpeg` `libavformat/whip.c:140-202, 1080-1766`, `tls_openssl.c:468-869`, `srtp.c:66-326`; `algesten/dimpl` `Cargo.toml`, `README.md:10-159`; `algesten/str0m` `Cargo.toml`; `webrtc-rs/webrtc` `Cargo.toml`; `webrtc-rs/dtls` `Cargo.toml`; `webrtc-rs/srtp` `Cargo.toml`; `google/boringssl` `ssl/d1_srtp.cc:31-128`).

**FFmpeg `whip.c` + `tls_openssl.c` + `srtp.c` Anatomy & 5 Verified Flaws:**
FFmpeg's WHIP muxer drives an 11-state handshake (`WHIP_STATE_NONE -> INIT -> OFFER -> ANSWER -> NEGOTIATED -> UDP_CONNECTED -> ICE_CONNECTING -> ICE_CONNECTED -> DTLS_FINISHED -> SRTP_FINISHED -> READY`, `whip.c:174-202`): it POSTs an SDP offer with Bearer token (`exchange_sdp`), parses the remote `ice-ufrag`/`ice-pwd`, SHA-256 DTLS fingerprint, and single UDP candidate (`parse_answer`), demultiplexes STUN (`0x00..0x03`), DTLS (`20..63`), and RTP/RTCP (`128..191`) per RFC 7983, runs `dtls_handshake` via `tls_openssl.c` (using an in-memory `BIO_meth_new` wrapper over `ffurl_read`/`ffurl_write`), exports 60 bytes of `"EXTRACTOR-dtls_srtp"` material (`client_key[16] | server_key[16] | client_salt[14] | server_salt[14]`, `whip.c:1441-1459`), and buffers sent video packets in a modulo ring (`WHIP_RTP_HISTORY_DEFAULT = 512`, `whip.c:1515-1535`) for RTCP NACK/RTX retransmission. Five concrete flaws exist in upstream FFmpeg:
1. **Unauthenticated Incoming STUN Requests & Missing `XOR-MAPPED-ADDRESS` (`whip.c:1128-1260`):** `ice_handle_binding_request` replies whenever `AV_RB16(buf) == 0x0001`, without verifying `USERNAME`, `MESSAGE-INTEGRITY`, or `FINGERPRINT`, and `ice_create_response` omits the mandatory RFC 8489 `XOR-MAPPED-ADDRESS` (`0x0020`) attribute.
2. **Unauthenticated STUN Responses (`whip.c:1201-1204, 1368-1374`):** `ice_is_binding_response` checks only `size >= 20 && AV_RB16(b) == 0x0101` (failing to check the `0x2112A442` Magic Cookie, the 96-bit Transaction ID, or `MESSAGE-INTEGRITY`), allowing off-path UDP packets starting with `0x01 0x01` to spoof ICE connectivity and RFC 7675 consent freshness.
3. **SRTP Rollover Reorder Authentication Bug (`srtp.c:158-183`, Basis: source + execution):** During RTP decryption, `ff_srtp_decrypt` estimates candidate rollover `v`: when `s->seq_largest < 32768 && seq - s->seq_largest > 32768`, line 162 sets `v = roc - 1` (previous epoch) and `create_iv` derives the AES-CTR keystream using `index = seq + (v << 16)`. However, line 175 computes `AV_WB32(rocbuf, roc)` using **`roc` instead of `v`**. Our executed probe confirms that for `(roc = 1, seq_largest = 5, seq = 65530)`, `v = 0` while `hmac_roc = 1` (`mismatch = 1`), guaranteeing 100% false `HMAC mismatch` drops on every packet reordered across a 65,536-packet boundary (~10.9 minutes at 100 pkt/s, or minutes on 10–50 Mbps video). Furthermore, in epoch 0 (`roc = 0`), a late/injected packet with `seq > 32768` produces `v = 0xffffffff` (`cipher_idx = 0xffffffff_fffa`).
4. **Missing Replay Protection & Non-Constant-Time Auth (`srtp.c:136, 180`):** Explicitly annotated `// TODO: Missing replay protection`, and compares HMAC digests with `memcmp`.
5. **Legacy SRTP Cipher & Feature Lock-In (`tls_openssl.c:842`, `srtp.c:74-87`):** Hardcodes `"SRTP_AES128_CM_SHA1_80"` only—omitting `SRTP_AEAD_AES_128_GCM` / `SRTP_AEAD_AES_256_GCM` (RFC 7714), WHEP playback, Trickle ICE, and TURN relays.

**Architectural Comparison: Pure-Rust Stacks vs Sandboxed BoringSSL/OpenSSL Workers:**

| Stack / Architecture | Language / `unsafe` Posture | DTLS & SRTP Cipher Support | Integration & Runtime Model | TCB / Formal Verification Trade-Off |
| :--- | :--- | :--- | :--- | :--- |
| **`FFmpeg` `whip.c` + `tls_openssl.c` + `srtp.c`** | C + OpenSSL (~500k+ SLOC C/asm) | DTLS 1.2; `SRTP_AES128_CM_SHA1_80` only | Synchronous polling loop (`5ms x 10` sleep) inside muxer | Large C TLS TCB; STUN auth flaws, SRTP rollover HMAC bug, no replay window |
| **`str0m` `0.25.0` + `dimpl` `0.9.0` (`--no-default-features --features rust-crypto`)** | Pure Rust (`dimpl` `#![forbid(unsafe_code)]`; `nom`, RustCrypto `aes-gcm`/`p256`/`x25519-dalek`) | DTLS 1.2 + 1.3 (`RFC 9147`), EMS (`RFC 7627`), `SRTP_AEAD_AES_{128,256}_GCM`, `AES128_CM_SHA1_80` | **Sans-IO & Sync** (`handle_packet`, `poll_output`, `handle_timeout`); caller checks `Output::PeerCert` SDP fingerprint | Zero C FFI (note: default features enable `aws-lc-rs` + `rcgen` -> `aws-lc-sys` C/NASM); ideal Sans-IO determinism for differential/formal verification |
| **`webrtc-rs/webrtc` `0.21.1` (and legacy `dtls` `0.5.4` / `srtp` `0.8.9`)** | Rust + `ring` / `aws-lc-rs` C/asm defaults | DTLS 1.2 + SRTP GCM/CTR; `webrtc` `0.21.1` adds pluggable `CryptoProvider` & `Runtime` trait (`tokio`/`smol`/`MockRuntime`) over Sans-IO `rtc` | Runtime-abstracted async channels (`async-channel`, `quinn-udp`); legacy `webrtc-dtls` `0.5.4` pulls stale `ring 0.16.19` / `rustls 0.19` | Default `crypto-ring` / `crypto-aws-lc-rs` reintroduces C/Perl-asm crypto TCB; requires custom `CryptoProvider` for 100% pure-Rust |
| **Sandboxed BoringSSL / OpenSSL Worker + Verified Rust SRTP** | `seccomp-bpf` / Landlock C worker (DTLS only) + Pure-Rust AEAD-SRTP in media process | DTLS 1.2/1.3, BoringCrypto/FIPS-140-3, `SSL_CTX_set_tlsext_use_srtp` (note BoringSSL inverted `0`=ok return in `ssl/d1_srtp.cc:120-127`) | IPC `socketpair` carries only ~2–4 RTT DTLS handshake datagrams + 60B/92B RFC 5764 `EXTRACTOR-dtls_srtp` keys; media datagrams stay in-process | Isolates ~500k SLOC C X.509/ASN.1/DTLS parsers in disposable worker with **zero per-media-packet IPC overhead**; SRTP hot path (`5k–25k pkt/s`) stays 100% Rust-verified |

### 8. Clean-Room Anneal-Verified Rust Architecture Across the 4-Level Verification Priority Stack

Basis: derived (synthesized from verified upstream constraints in Sections 1–7).

1. **Priority 1 — UB-Freedom:**
   - Isolate irreducible `unsafe` OS boundaries (`ioctl` V4L2/DRM, `mmap`, `AudioQueue`, COM vtables for DirectShow/WASAPI/DeckLink, and optional `libsrt`/`librist` FFI) inside narrow capability wrappers. Replace raw `void *opaque` `AVBufferRef` callbacks with typestate/ghost ownership tokens (`KernelOwned` vs `UserspaceLeased`) guaranteeing at compile time that kernel `mmap` addresses outlive packets and `VIDIOC_QBUF` never aliases active user slices, while guaranteeing DMA-BUF FDs close deterministically on multi-plane `Drop` (eliminating `kmsgrab.c:230-260` FD leaks).
   - Apply volatile single-fetch copies from shared PipeWire `spa_chunk` and X11 MIT-SHM descriptors before slice construction, and enforce `extern "C"` panic-aborting trampolines on every foreign audio/video callback thread.
   - Enforce `#![forbid(unsafe_code)]` across 100% of wire protocol state machines (`RTSP`, `RTP/RTCP`, `RTMP/E-RTMP`, `HLS crypto`, `ICE/STUN`, `DTLS`, `SRTP`, `SRT/RIST`).
2. **Priority 2 — Panic-Freedom:**
   - Replace every C truncation/wrap hazard with checked arithmetic: `u64`/`usize` checked `fifo_size * 188` (`udp.c:741`), `bytesused <= buf_len` clamping (`v4l2.c:616`), 64-bit per-plane byte size checks (`kmsgrab.c:209`), wrapping `u32` RTMP delta timestamps (`rtmppkt.c:236`), and constant-time validated `1..=16` PKCS#7 padding removal (`crypto.c:230`).
   - Bound all attacker-controlled buffers: fixed-capacity pre-allocated $O(1)$ sequence-indexed circular RTP reorder slots (eliminating `rtpdec.c` $O(N^2)$ list walks and per-packet heap allocations), a global partial-message byte ceiling across RTMP's `65,599` chunk channels, and strict maximum Temporal Unit size limits in AV1/H.264/HEVC RTP reassembly.
3. **Priority 3 — Behavioral Equivalence & Differential Testing:**
   - Preserve C-ABI interoperability through a thin `libavdevice.so.63` shim exporting the 10 public `avdevice_*` functions, `AVFMT_NOFILE` demuxer/muxer tables, and `AVDeviceInfoList` / `AVAppToDevMessageType` structs, while substituting native PipeWire (Portal ScreenCast + audio) and WASAPI backends cleanly under modern OS desktops.
   - Use deterministic Sans-IO state machines (matching `dimpl`/`str0m` and `webrtc` `MockRuntime` patterns) to drive differential packet-trace testing against FFmpeg, `retina`, and `Haivision/srt`, explicitly whitelisting intentional safety divergences where FFmpeg's C implementation violates RFCs or triggers UB (SRTP rollover HMAC, PKCS#7 unvalidated strip, STUN unauthenticated responses).
4. **Priority 4 — Full Functional Spec Conformance:**
   - Implement complete RFC 3550/4585/6184/7798 + AOMedia AV1-RTP v1.0 depacketizers/packetizers (fixing `skip_between` aggregate bounds), full E-RTMP v2 (`FourCC`, `CodedFramesX`, `Metadata`, `Multitrack`, `ModEx`), RFC 8216 AES-128 with validated PKCS#7, VSF TR-06-1/2 RIST and SRT (`SRT_OPT_SECDIST` bidirectional key separation), and RFC 9725 WHIP + WHEP with full RFC 8489 `MESSAGE-INTEGRITY`/`XOR-MAPPED-ADDRESS`, RFC 7714 `SRTP_AEAD_AES_{128,256}_GCM`, and 128-bit sliding-window SRTP replay protection.

## Boundaries

- **Unsupported (in upstream `FFmpeg/FFmpeg` `v63`):** Native PipeWire (`SPA_DATA_DmaBuf` / XDG Portal ScreenCast) and Windows WASAPI `libavdevice` drivers; WHEP egress, Trickle ICE, TURN relays, DTLS 1.3, and `SRTP_AEAD_AES_{128,256}_GCM` in `whip.c`/`srtp.c`; H.264 interleaved RTP modes (`STAP-B`, `MTAP-16`, `MTAP-24`, `FU-B`) in `rtpdec_h264.c`; multi-layer HEVC (`lid != 0`) and `PACI` (`50`) packets in `rtpdec_hevc.c`; fragmented `OBU_TILE_LIST` in `rtpdec_av1.c`.
- **Not Examined:** Kernel-mode V4L2/DRM/ALSA driver internals inside Linux kernel trees; proprietary closed-source Blackmagic `DesktopVideo` SDK internals beyond FFmpeg's `decklink_{dec,enc}.cpp` C++ COM wrapper; live WAN congestion/FEC loss-recovery curves against external broadcast ingest servers (outbound non-GitHub network sockets are blocked in the evaluation environment).
- **Known Not to Apply:** Default Cargo feature sets of `dimpl` (`default = ["aws-lc-rs", "rcgen"]`) and `webrtc` (`default = ["runtime-tokio", "crypto-ring"]`) are **not** pure-Rust—both compile `aws-lc-sys` or `ring` C/assembly unless default features are disabled (`dimpl` requires `--no-default-features --features rust-crypto`; `webrtc` requires supplying a pure-Rust `CryptoProvider`). Likewise, `libavdevice` `AVPacket` payloads from `kmsgrab` and `lavfi` are **not** raw compressed/pixel byte buffers, but tagged `AV_PKT_FLAG_TRUSTED` structs containing `AVFrame*` / `AVDRMFrameDescriptor*` pointers.
- **Unknown:** Upstream FFmpeg release schedule or review disposition for external out-of-tree PipeWire or WASAPI `libavdevice` patches beyond commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`.

## Evidence

### Pinned GitHub Repositories and Inspected Files

| Subject | Commit SHA | Inspected Paths & Line Ranges |
| :--- | :--- | :--- |
| `FFmpeg/FFmpeg` | `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` | `configure:2048-4137, 4861-4865`; `libavdevice/{version_major.h:28, version.h:32-43, avdevice.h:40-391, avdevice.c:26-129, alldevices.c:30-142, Makefile:16-58, v4l2.c:373-655, kmsgrab.c:110-364, xcbgrab.c:241-290, timefilter.c:34-95, alsa_dec.c:92-142, pulse_audio_dec.c:277-361, jack.c:80-191, avfoundation.m:151-315, 1342-1465, audiotoolbox.m:42-285, dshow_pin.c:290-366, decklink_dec.cpp:161-985, lavfi.c:420-490}`; `libavformat/{protocols.c:27-149, url.h:32-402, avio.c:212-265, 579-655, udp.c:72-165, 529-1143, rtsp.h:39-270, rtsp.c:1214-1270, 2140-2245, rtpdec.h:36-191, rtpdec.c:249-941, rtpdec_h264.c:210-360, rtpdec_hevc.c:178-340, rtpdec_av1.c:46-464, rtmpproto.c:57-131, 336-395, 1267-1606, 3259-3267, rtmppkt.h:29-152, rtmppkt.c:138-297, flv.h:106-158, flvdec.c:1250-1340, libsrt.c:39-355, librist.c:40-269, crypto.c:32-402, hls.c:1093-1255, 1705-1732, srtp.c:66-326, tls_openssl.c:468-869, whip.c:140-202, 1080-1766}` |
| `algesten/dimpl` | `e341a902854d96e1ab8aad910ef5ddea5c1598f8` | `Cargo.toml:1-86`, `README.md:10-159` |
| `algesten/str0m` | `54bf16ee84eca2bc39c8b59720338eb0bbd55538` | `Cargo.toml:1-185` |
| `webrtc-rs/webrtc` | `3c4584ae984a004def73168782fa86d59f12263a` | `Cargo.toml:1-73` |
| `webrtc-rs/dtls` | `119dc715440843c6a6e7a0fb955fc38d1e7f37ef` | `Cargo.toml:1-50` |
| `webrtc-rs/srtp` | `33121993cd21e2e75adc1559052bf6901eecd95b` | `Cargo.toml:1-36` |
| `Haivision/srt` | `98ac9998f9ba8db41e7118fa867180c1536d1b74` | `srtcore/buffer_rcv.h:45-180`, `srtcore/crypto.h:55-180` |
| `veovera/enhanced-rtmp` | `40589eb9d38d6555e6cdbbfc5699312995203561` | `docs/enhanced/enhanced-rtmp-v2.md:328-1755` |
| `scottlamb/retina` | `2b6b7fe0a6f6a5bf69d5e9c8d4fd785ccd090873` | `Cargo.toml:1-64` |
| `google/boringssl` | `ddd732967025c608598b9984a1ada358fa82f6f0` | `ssl/d1_srtp.cc:31-128` |
| `openssl/openssl` | `159cdbc6006afe7676c5e699f624991ce40d911e` | Verified commit object; FFmpeg consumer interface inspected in `libavformat/tls_openssl.c` |
| `PipeWire/pipewire` | `415ac8e5b68607e95e57a12b926f9aa104e5ea7b` | `spa/include/spa/buffer/buffer.h:34-135` |
| `RustAudio/cpal` | `40ff3adea81757326debba6b2befb747a6699d50` | `src/host/wasapi/stream.rs:39-160` |

### Non-GitHub Standards & External Repositories
- VideoLAN `librist` `v0.2.11` (`https://code.videolan.org/rist/librist`), VSF Technical Recommendations `TR-06-1` (RIST Simple Profile) and `TR-06-2` (RIST Main Profile), inspected alongside FFmpeg's `libavformat/librist.c`.
- IETF `RFC 3550` (RTP/RTCP), `RFC 3711` (SRTP), `RFC 4585` (RTCP Feedback), `RFC 5764` (DTLS-SRTP), `RFC 6184` (RTP/H.264), `RFC 7627` (TLS Extended Master Secret), `RFC 7675` (ICE Consent Freshness), `RFC 7714` (AEAD-SRTP), `RFC 7798` (RTP/HEVC), `RFC 7983` (UDP Demultiplexing), `RFC 8216` (HLS), `RFC 8445` (ICE), `RFC 8489` (STUN), `RFC 9147` (DTLS 1.3), `RFC 9725` (WHIP), and AOMedia `RTP Payload Format For AV1 (v1.0)`.

### Executed Standalone C Verification Probe (`repro_probes.c`)

Observed `2026-11-20` on Linux `x86_64` compiled with `gcc -O2 -Wall -Wextra repro_probes.c -lm -o repro_probes && ./repro_probes`:

```c
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef struct TimeFilter {
    double cycle_time, feedback2_factor, feedback3_factor, clock_period;
    int count;
} TimeFilter;

static double qexpneg(double x) { return 1 - 1 / (1 + x * (1 + x / 2 * (1 + x / 3))); }

static TimeFilter tf_new(double time_base, double period, double bandwidth) {
    TimeFilter tf = {0};
    double o = 2 * M_PI * bandwidth * period * time_base;
    tf.clock_period = time_base;
    tf.feedback2_factor = qexpneg(M_SQRT2 * o);
    tf.feedback3_factor = qexpneg(o * o) / period;
    return tf;
}

static double tf_update(TimeFilter *self, double system_time, double period) {
    self->count++;
    if (self->count == 1) { self->cycle_time = system_time; }
    else {
        self->cycle_time += self->clock_period * period;
        double loop_error = system_time - self->cycle_time;
        double f2 = self->feedback2_factor > (1.0 / self->count) ? self->feedback2_factor : (1.0 / self->count);
        self->cycle_time += f2 * loop_error;
        self->clock_period += self->feedback3_factor * loop_error;
    }
    return self->cycle_time;
}

typedef struct SrtpRocState { int seq_initialized, seq_largest; uint32_t roc; } SrtpRocState;

static void srtp_roc_eval(SrtpRocState *s, uint16_t seq, uint64_t *out_idx, uint32_t *out_hmac_roc, uint32_t *out_v) {
    int seq_largest = s->seq_initialized ? s->seq_largest : seq;
    uint32_t roc = s->roc, v = roc;
    if (seq_largest < 32768) { if ((int)seq - seq_largest > 32768) v = roc - 1; }
    else { if (seq_largest - 32768 > (int)seq) v = roc + 1; }
    if (v == roc) { if ((int)seq > seq_largest) seq_largest = seq; }
    else if (v == roc + 1) { seq_largest = seq; roc = v; }
    *out_idx = (uint64_t)seq + (((uint64_t)v) << 16);
    *out_hmac_roc = roc; /* reproduces libavformat/srtp.c:175 mismatch */
    *out_v = v;
}

static int crypto_eof_strip(const uint8_t *outbuffer, int outdata) {
    int padding = outbuffer[outdata - 1];
    outdata -= padding;
    return outdata;
}

typedef struct RTPPkt { uint16_t seq; struct RTPPkt *next; } RTPPkt;

static uint64_t bench_reorder_insert(int queue_cap, RTPPkt *pool) {
    RTPPkt *queue = NULL;
    uint64_t steps = 0;
    for (int i = 0; i < queue_cap; i++) {
        uint16_t seq = (uint16_t)(1002 + i);
        RTPPkt **cur = &queue;
        while (*cur) {
            steps++;
            int16_t diff = (int16_t)(seq - (*cur)->seq);
            if (diff < 0) break;
            cur = &(*cur)->next;
        }
        pool[i].seq = seq; pool[i].next = *cur; *cur = &pool[i];
    }
    return steps;
}

int main(void) {
    TimeFilter tf = tf_new(1.0 / 48000.0, 512.0, 1.5);
    double true_period = (1.0 / 48000.0) * 1.000100, max_err = 0.0;
    uint32_t lcg = 123456789u;
    for (int n = 0; n < 500; n++) {
        lcg = lcg * 1664525u + 1013904223u;
        double jitter = ((double)(int32_t)lcg / 2147483648.0) * 0.0015;
        double true_t = n * 512.0 * true_period;
        double est_t = tf_update(&tf, true_t + jitter, 512.0);
        if (n >= 200 && fabs(est_t - true_t) > max_err) max_err = fabs(est_t - true_t);
    }
    printf("TimeFilter +100ppm/+/-1.5ms: est_ppm=%.2f max_err_us_after_200=%.1f\n",
           (tf.clock_period / (1.0 / 48000.0) - 1.0) * 1e6, max_err * 1e6);

    SrtpRocState st = {1, 5, 1}; uint64_t cidx = 0; uint32_t hroc = 0, v = 0;
    srtp_roc_eval(&st, 65530, &cidx, &hroc, &v);
    printf("SRTP rollover reorder (roc=1,seq_largest=5,seq=65530): v=%u cipher_idx=0x%llx hmac_roc=%u mismatch=%d\n",
           v, (unsigned long long)cidx, hroc, (hroc != v));

    SrtpRocState st0 = {1, 5, 0};
    srtp_roc_eval(&st0, 65530, &cidx, &hroc, &v);
    printf("SRTP epoch-0 reorder (roc=0,seq_largest=5,seq=65530): v=0x%x cipher_idx=0x%llx hmac_roc=%u\n",
           v, (unsigned long long)cidx, hroc);

    uint8_t blk[16] = {0}; blk[15] = 0xff;
    printf("crypto.c PKCS7 outdata=16 pad=0xff -> outdata=%d\n", crypto_eof_strip(blk, 16));

    int caps[3] = {500, 4096, 16384};
    RTPPkt *pool = calloc(16384, sizeof(RTPPkt));
    for (int k = 0; k < 3; k++) {
        struct timespec t0, t1;
        clock_gettime(CLOCK_MONOTONIC, &t0);
        uint64_t steps = bench_reorder_insert(caps[k], pool);
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double us = (t1.tv_sec - t0.tv_sec) * 1e6 + (t1.tv_nsec - t0.tv_nsec) / 1e3;
        printf("RTP enqueue_packet cap=%d: pointer_steps=%llu time_us=%.1f\n",
               caps[k], (unsigned long long)steps, us);
    }
    free(pool);
    return 0;
}
```

Exact stdout observed:

```text
TimeFilter +100ppm/+/-1.5ms: est_ppm=925.94 max_err_us_after_200=716.5
SRTP rollover reorder (roc=1,seq_largest=5,seq=65530): v=0 cipher_idx=0xfffa hmac_roc=1 mismatch=1
SRTP epoch-0 reorder (roc=0,seq_largest=5,seq=65530): v=0xffffffff cipher_idx=0xfffffffffffa hmac_roc=0
crypto.c PKCS7 outdata=16 pad=0xff -> outdata=-239
RTP enqueue_packet cap=500: pointer_steps=124750 time_us=219.8
RTP enqueue_packet cap=4096: pointer_steps=8386560 time_us=24997.4
RTP enqueue_packet cap=16384: pointer_steps=134209536 time_us=360689.0
```

## Revalidation

To verify whether these findings still hold on a newer upstream FFmpeg or Rust crate revision:
1. **Device and Protocol Census Diff:** Diff `libavdevice/alldevices.c` and `libavformat/protocols.c` against `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (check for newly added `ff_pipewire_*`, `ff_wasapi_*`, or `URLProtocol` entries).
2. **SRTP & Crypto Bug Fix Check:** Inspect `ff_srtp_decrypt` (`libavformat/srtp.c:175`) for whether `AV_WB32(rocbuf, v)` has replaced `AV_WB32(rocbuf, roc)`, and check `crypto_read` (`libavformat/crypto.c:228-233`) for `1 <= padding <= BLOCKSIZE` and constant-time padding verification.
3. **WHIP / AV1 / RTMP Hardening Check:** Inspect `whip.c` (`ice_is_binding_response` and `ice_handle_binding_request`) for HMAC-SHA1 `MESSAGE-INTEGRITY` checks, `rtpdec_av1.c:294` for a Temporal Unit byte cap, and `rtmppkt.c:177, 236` for `uint32_t timestamp` and per-connection channel memory caps.
4. **Rerun Reorder/DLL Probe:** Re-extract `repro_probes.c` from **Evidence** and compile/execute (`gcc -O2 -Wall -Wextra repro_probes.c -lm && ./repro_probes`) whenever `libavdevice/timefilter.c` or `libavformat/rtpdec.c` changes.
5. **Rust Dependency Audit:** Run `cargo tree --no-default-features --features rust-crypto` inside `algesten/dimpl` / `algesten/str0m` and check `webrtc-rs/webrtc` `CryptoProvider` defaults to confirm zero unexpected C/assembly (`aws-lc-sys`, `ring`) links.
