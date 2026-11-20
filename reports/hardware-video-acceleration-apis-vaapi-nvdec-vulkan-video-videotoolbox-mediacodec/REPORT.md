# Hardware Video Acceleration APIs (VA-API, NVDEC/NVENC, Vulkan Video, VideoToolbox, MediaCodec, D3D11/D3D12VA, V4L2, QSV): Zero-Copy Surface Lifetimes, Untrusted Driver/DMA Boundaries, and Sound Hardware Contracts

## Summary

Hardware video decoding and encoding in `FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) spans ten distinct vendor and OS APIs unified beneath `AVHWDeviceContext`, `AVHWFramesContext`, and the internal `HWContextType` vtable (`libavutil/hwcontext.h:27-165`, `libavutil/hwcontext_internal.h:60-155`). Despite this shared C facade, primary-source inspection shows that the underlying APIs divide into **four irreducibly different state and synchronization models**:

1. **Stateless Explicit Command-Queue + Explicit Fence APIs (`Vulkan Video` `VK_KHR_video_decode_queue` v8 / `VK_KHR_video_encode_queue` v12, `D3D12VA`):** Host software parses bitstream headers, maintains the Decoded Picture Buffer (DPB) slot automaton (`VkVideoBeginCodingInfoKHR`, `VUID-VkVideoBeginCodingInfoKHR-slotIndex-07245`), records memory/layout barriers, and synchronizes explicitly via timeline semaphores or `ID3D12Fence` (`libavcodec/vulkan_decode.c:201-585`, `libavcodec/d3d12va_decode.c:675-690`).
2. **Stateless Surface-Pool + Implicit/Call-Bound Sync APIs (`VA-API`, `D3D11VA`, `VDPAU`):** Host software parses headers and submits slice parameter buffers (`vaBeginPicture`/`vaRenderPicture`/`vaEndPicture`), while the kernel/UMD driver tracks surface busyness implicitly until `vaSyncSurface` or staging-texture `Map` (`libavcodec/vaapi_decode.c:191-238`, `libavutil/hwcontext_d3d11va.c:464-496`).
3. **Hybrid Fixed-Ring / Shared-Counter APIs (`NVDEC`/`NVENC` CUDA, `Intel QSV`/`oneVPL`):** Vendor user-mode drivers (`libnvcuvid`, `libnvidia-encode`, `libvpl`) expose fixed hardware surface ceilings (`NVDEC_MAX_DECODE_SURFACES = 32` in `libavcodec/nvdec.c:648-661`), thread-local context stacks (`cuCtxPushCurrent`), or driver-mutated userspace `mfxFrameSurface1.Data.Locked` fields (`libavutil/hwcontext_qsv.c:710-785`).
4. **Stateful Packet-In / Frame-Out OS Pipelines (`VideoToolbox`, `MediaCodec`, `V4L2 M2M`):** Firmware or OS media servers parse compressed bitstreams internally and exchange opaque kernel buffer handles (`CVPixelBufferRef`/`IOSurface`, `ANativeWindow`, `VIDIOC_QBUF`/`DQBUF` planes; `libavcodec/videotoolbox.c:760-1007`, `libavcodec/mediacodecdec_common.c:937-1075`, `libavcodec/v4l2_buffers.c:369-725`).

Direct inspection of FFmpeg's C implementations alongside Linux `include/uapi/linux/dma-buf.h` (`65e4fd942f72a9dba0e4e257290c4fa1aa756854`) exposes **four critical memory-safety and liveness hazards** that a verified Rust media framework must eliminate:
- **Unchecked `AVDRMPlaneDescriptor` pointer arithmetic (`libavutil/hwcontext_drm.c:178-181`):** `drm_map_frame` adds `layer->planes[p].offset` directly to `map->address[layer->planes[p].object_index]` without checking `object_index < desc->nb_objects` or `offset + (plane_h - 1) * pitch + row_bytes <= map->length[idx]`. A single-fetch checked validator (`probe_pkg2.c`) closes both out-of-bounds and TOCTOU hazards in **`85.12 ns`**.
- **Conflating cache coherency with mutual exclusion (`dma-buf.h:40-54` vs. `hwcontext_drm.c:113, 167-169`):** `DMA_BUF_IOCTL_SYNC` flushes CPU caches (and its errors are ignored in `hwcontext_drm.c:169`), but **does not block concurrent GPU/DMA writes**, violating Rust's `&[u8]` no-mutation invariant unless paired with fence completion.
- **Warn-only `DMA_BUF_IOCTL_IMPORT_SYNC_FILE` failure (`libavutil/hwcontext_vulkan.c:4614-4615`):** If importing Vulkan's write-completion `sync_fd` into an exported `DMA-BUF` fails, FFmpeg logs `AV_LOG_WARNING` and returns success, exporting an unsynchronized surface to downstream DRM/Wayland consumers.
- **Unbounded GPU hang waits and surface-pool deadlocks (`hwcontext_d3d12va.c:88, 103`; `hwcontext_d3d11va.c:261-263`; `nvdec.c:662`):** `WaitForSingleObjectEx(..., INFINITE, FALSE)` blocks host threads permanently on GPU TDR/hangs, while static `ArraySize` (`D3D11VA`) and `unsafe_output` (`NVDEC`) surface pools fail or deadlock when downstream filter graphs retain >$N$ frames.

## Applicability

This report covers hardware video acceleration across `FFmpeg/FFmpeg` at commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`libavutil/hwcontext*.{c,h}` and `libavcodec/{vaapi,vdpau,nvdec,nvenc,vulkan,videotoolbox,mediacodec,d3d11va,d3d12va,v4l2_*,qsv}*`), analyzed jointly with normative API definitions in `KhronosGroup/Vulkan-Headers` (`d277a0a3cda9c682708c93279f0c72cd6b0ae3f3`), `intel/libva` (`f052e984e0c8bf10784198cc311b23c567b1367f`), `FFmpeg/nv-codec-headers` (`f2053071ea93137255b6dcf42e9b4c9e0965a44e`), Linux kernel UAPI `torvalds/linux` (`65e4fd942f72a9dba0e4e257290c4fa1aa756854`, `include/uapi/linux/dma-buf.h`), and the Rust stateless hardware codec architecture in `chromeos/cros-codecs` (`a050c6cde530e563197ee9e3e72ab01f48a0c41f`, `v0.0.5`).

Execution evidence (`Basis: execution`) was gathered on `Linux 7.1.6-1rodete1-amd64` (`x86_64`, `gcc -O2`) against `/usr/include/linux/dma-buf.h`; no physical vendor GPU kernel nodes (`/dev/dri/renderD128` or `/dev/nvidia0`) were exercised inside the isolated build environment, and hardware throughput/latency trade-offs are grounded directly in inspected driver/API mechanics (`USWC` aperture behavior in `hwcontext_vaapi.c:874-882`, VRAM blit behavior in `nvdec.c:662, 965`, and `D3D11_USAGE_STAGING` copies in `hwcontext_d3d11va.c:464-496`).

This report cites and extends prior corpus analyses without repeating their derivations:
- Shared-DMA double-fetch Vulnerabilities and single-fetch logics: `double-fetch-toctou-shared-dma-rings-and-single-fetch-logics` and `isa-page-table-tlb-coherence-sail-trap-contracts-and-toctou-dma-fetch-oracles`.
- Vulkan/WebGPU explicit memory models, layout transitions, and shader sandboxing: `vulkan-webgpu-explicit-memory-models-spirv-uniformity-and-shader-sandboxing`.
- Explicit DRM syncobj, Wayland `DMA-BUF` passing, and `memfd` seals: `wayland-explicit-drm-syncobj-dbus-fd-passing-and-pipewire-graph-scheduling`.
- PCIe peer-to-peer DMA lifetimes and weak-memory peripheral verification: `tcp-msg-zerocopy-errqueue-lifetimes-pcie-p2pdma-and-nvlink-peer-ordering`, `rdma-weak-memory-iommu-ats-and-byzantine-peripheral-verification`, and `verified-software-hardware-ffi-mmio-dma-interconnects-and-reconfigurable-fabrics`.

## Findings

### 1. FFmpeg's Two-Tier Hardware Context Architecture and Type-Erasure Debt

`Basis: source`

FFmpeg models hardware acceleration through a reference-counted two-level hierarchy (`libavutil/hwcontext.h:46-165`, `libavutil/hwcontext_internal.h:60-155`):
1. **`AVHWDeviceContext` (`hwcontext.h:63-106`):** Represents device-global state independent of resolution or pixel format (e.g., `VADisplay`, `CUcontext`, `VkInstance`/`VkDevice`, `ID3D11Device`, DRM `fd`), wrapped in an `AVBufferRef` so child frame pools keep the parent device alive until all surfaces are destroyed (`L54-61, 96-98`).
2. **`AVHWFramesContext` / `FFHWFramesContext` (`hwcontext.h:118-165`, `hwcontext_internal.h:102-130`):** Represents a homogeneous pool of interchangeable hardware surfaces of fixed `format` (the opaque hardware `AVPixelFormat`, e.g., `AV_PIX_FMT_VAAPI`, `AV_PIX_FMT_CUDA`, `AV_PIX_FMT_VULKAN`, `AV_PIX_FMT_DRM_PRIME`), `sw_format` (the underlying sample layout, e.g., `AV_PIX_FMT_NV12`, `AV_PIX_FMT_P010`), `width`, and `height`, backed by `AVBufferPool *pool_internal` (`hwcontext_internal.h:110`).
3. **`HWContextType` Vtable (`hwcontext_internal.h:60-100`) and `HWMapDescriptor` (`L137-155`):** Each backend implements up to 13 operations covering device creation/derivation (`device_create`, `device_derive`), pool allocation (`frames_get_constraints`, `frames_init`, `frames_get_buffer`), copy transfers (`transfer_data_to`, `transfer_data_from`), and zero-copy cross-API or CPU views (`map_to`, `map_from`, `frames_derive_to`, `frames_derive_from`, tracked by `HWMapDescriptor` whose destructor `unmap` holds a strong `AVFrame *source` reference until the derived view drops).

**Historical C Accident vs. Clean-Rewrite Constraint (`Basis: source + derived`):**
To shoehorn opaque GPU handles into `AVFrame` without changing its C struct ABI, FFmpeg overloads `uint8_t *AVFrame.data[0..3]` via incompatible pointer/integer casts across backends:
- `VA-API`: `(VASurfaceID)(uintptr_t)src->data[3]` (`32`-bit integer ID stuffed into `uint8_t *`, `hwcontext_vaapi.c:1371`).
- `VDPAU`: `(VdpVideoSurface)(uintptr_t)src->data[3]` (`32`-bit integer handle in `data[3]`, `hwcontext_vdpau.c:339`).
- `D3D11VA`: `(ID3D11Texture2D *)frame->data[0]` COM pointer in `data[0]` paired with `(intptr_t)frame->data[1]` subresource array slice index in `data[1]` (`hwcontext_d3d11va.c:436-437`).
- `QSV`: `(mfxFrameSurface1 *)src->data[3]` mutable userspace struct pointer in `data[3]` (`hwcontext_qsv.c:1591`).
- `DRM PRIME`: `(AVDRMFrameDescriptor *)src->data[0]` struct pointer in `data[0]` (`hwcontext_drm.c:124`).
- `CUDA / NVDEC`: `(uint8_t *)(devptr + offset)` device virtual address cast to host `uint8_t *` in `data[0..2]` (`nvdec.c:948`).

In Rust, casting device addresses (`CUdeviceptr`) or integer handles (`VASurfaceID`, `ArraySlice` indices) to host `*mut u8` pointers conflates disjoint address spaces and fabricates pointer provenance (`minirust-representation-transfers-provenance-and-primitive-lowering`). A clean Rust rewrite must separate `FrameStorage::CpuPlanes(CpuFrame)` from `FrameStorage::GpuSurface(TypedSurfaceHandle)` at the type level, synthesizing C `AVFrame.data[]` layouts solely inside an optional outer C-ABI compatibility shim.

### 2. Cross-API Taxonomy Across All Ten Hardware Video Backends

`Basis: normative + source`

| Backend API | FFmpeg Modules (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) | Control Model (Bitstream Parsing & DPB) | Surface Pool & Memory Model | Synchronization & Zero-Copy Interop Mechanism | Primary Soundness / Liveness Hazards |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Vulkan Video** (`VK_KHR_video_decode_queue` v8, `encode_queue` v12) | `hwcontext_vulkan.c` (`5409` LOC), `vulkan_decode.c` (`1477` LOC), `vulkan_encode.c` (`1195` LOC) | **Stateless explicit:** Host parses headers + manages 3-mode DPB (`coincide`, `distinct` layered `VkImage` array, `distinct` per-slot `VkImage`; `vulkan_decode.c:201-235, 1046-1055, 1373`). | Explicit `VkDeviceMemory` + `VkImage` views; AV1 film grain forces distinct output + DPB (`vulkan_decode.c:1373`). | Timeline `VkSemaphore` + `VkImageMemoryBarrier2`; Linux `VK_EXT_external_memory_dma_buf` + `DMA_BUF_IOCTL_{EXPORT,IMPORT}_SYNC_FILE` (`hwcontext_vulkan.c:3887-3920, 4591-4620`). | VUID state violations (`VUID-...-07245`, `vulkan_decode.c:225`); warn-only `IMPORT_SYNC_FILE` failure (`L4614-4615`) leaks unsynchronized `DMA-BUF`. |
| **VA-API** (`libva`) | `hwcontext_vaapi.c` (`2106` LOC), `vaapi_decode.c` (`774` LOC), `vaapi_encode.c` | **Stateless surface-ID:** Host parses SPS/PPS/slice params into `vaCreateBuffer`; submits `vaBeginPicture` $\to$ `vaRenderPicture` $\to$ `vaEndPicture` (`vaapi_decode.c:57-238`). | Driver-managed `VASurfaceID` pool (dynamic or fixed per driver `constraints`). | `vaSyncSurface` / timeout-capable `vaSyncSurface2` (`va.h:4277-4407`); zero-copy `vaExportSurfaceHandle` (`DRM_PRIME_2`, `hwcontext_vaapi.c:1388`). | **USWC read cliff:** `vaDeriveImage` maps uncached aperture memory (`hwcontext_vaapi.c:874-882`); `vaMapBuffer` returns raw untrusted driver pointer. |
| **VDPAU** (`libvdpau`) | `hwcontext_vdpau.c` (`533` LOC), `vdpau.c` | **Stateless legacy:** Host parses headers + passes compressed slices to `VdpDecoderRender`. | Opaque X11/driver `VdpVideoSurface` pool (`hwcontext_vdpau.c:285`). | Copy-only `VdpVideoSurfaceGetBitsYCbCr` / `PutBitsYCbCr` (`hwcontext_vdpau.c:528-530`); **no `map_from`/`DMA-BUF` export**. | Legacy X11 display lifetime coupling; device loss on VT switch/reset. |
| **NVDEC / NVENC** (`CUDA` / `ffnvcodec`) | `hwcontext_cuda.c` (`1041` LOC), `nvdec.c` (`1217` LOC), `nvenc.c` (`3274` LOC) | **Stateless decode (`cuvidDecodePicture`) / firmware-assisted encode (`nvEncEncodePicture`):** `dlopen` vtables via `nv-codec-headers`. | Hard `NVDEC_MAX_DECODE_SURFACES = 32` (`nvdec.c:648-661`); 3 output modes: `ulNumOutputSurfaces=1` + copy, `unsafe_output <= 64`, or `CUarray` `opaque_output` (`L662-705`). | `CUstream` + `cuStreamSynchronize` (`hwcontext_cuda.c:707-725`); TLS `cuCtxPushCurrent` / `cuCtxPopCurrent` bracket required on every call. | Missing `cuCtxPopCurrent` corrupts caller thread TLS; `unsafe_output` starves `cuvidMapVideoFrame` (`dynlink_cuviddec.h:1212`); `hevc_nvenc` OOM quirk (`nvenc.c:2729`). |
| **D3D11VA** (Windows) | `hwcontext_d3d11va.c` (`750` LOC), `d3d11va.c` | **Stateless DXVA:** Host fills picture/slice/quantization buffers via `D3D11_VIDEO_DECODER_BUFFER_DESC`. | **Static monolithic `ID3D11Texture2D` array** (`ArraySize = initial_pool_size`, `hwcontext_d3d11va.c:304`); `DXGI_FORMAT_420_OPAQUE` forbids `BIND_SHADER_RESOURCE` (`L295-296`). | User-supplied global `device_hwctx->lock` mutex (`L451, 498`) serializing `CopySubresourceRegion` to `D3D11_USAGE_STAGING` texture (`L465-495`). | **Non-growable pool:** exceeding `ArraySize` fails hard (`L261-263`); forgetting `lock()` causes immediate multi-thread `ID3D11DeviceContext` corruption. |
| **D3D12VA** (Windows) | `hwcontext_d3d12va.c` (`826` LOC), `d3d12va_decode.c` (`706` LOC) | **Stateless explicit:** `ID3D12VideoDecodeCommandList_DecodeFrame` bracketed by explicit `ResourceBarrier` transitions (`d3d12va_decode.c:675-690`). | Independent committed `ID3D12Resource` textures (or optional `texture_array`, `hwcontext_d3d12va.c:354, 398`) + staging upload/download buffers (`L45-46`). | Per-frame `ID3D12Fence` (`L298, 360`) + Win32 `HANDLE` event waited via `WaitForSingleObjectEx` (`L98-105`). | **Unbounded hang:** `WaitForSingleObjectEx(..., INFINITE, FALSE)` (`L88, 103`) deadlocks host threads permanently on GPU TDR (`DXGI_ERROR_DEVICE_REMOVED`). |
| **VideoToolbox** (macOS / iOS) | `hwcontext_videotoolbox.c` (`857` LOC), `videotoolbox.c` (`1504` LOC) | **Stateful OS session:** `VTDecompressionSessionDecodeFrame` (`videotoolbox.c:760`) parses AVCC/HVCC/AV1 packets inside Apple's media daemon/ANE/GPU stack. | Reference-counted `CVPixelBufferRef` backed by Mach-port kernel `IOSurface`. | Zero-copy Metal/CoreAnimation via `IOSurface`; CPU read/write requires `CVPixelBufferLockBaseAddress` / `Unlock` (`hwcontext_videotoolbox.c:710`). | Accessing `CVPixelBufferGetBaseAddress` without `LockBaseAddress` races against Apple GPU/display engines on unified memory without cache coherency barriers. |
| **MediaCodec** (Android) | `hwcontext_mediacodec.c` (`121` LOC), `mediacodecdec_common.c` (`1181` LOC) | **Stateful Binder/NDK codec:** `AMediaCodec` (`dequeueInputBuffer` $\to$ `queueInputBuffer` $\to$ `dequeueOutputBuffer` $\to$ `releaseOutputBuffer`, `mediacodecdec_common.c:937-1075`). | Either zero-copy opaque `ANativeWindow` / `Surface` (`GraphicBuffer`/`AHardwareBuffer`, `hwcontext_mediacodec.c:66-85`) or CPU `ByteBuffer` copies; requires `--enable-jni` (`configure:7499`). | `releaseOutputBuffer(codec, index, render)` releases slot back to `BufferQueue`; `Surface` mode never exposes pixels to CPU. | Codec server process death (`MEDIA_ERROR_SERVER_DIED`), vendor stride/slice-height padding quirks on `ByteBuffer` output, and strict index-token linearity (double-release corrupts `AMediaCodec` slot state). |
| **V4L2 M2M** (Linux SoC) | `v4l2_m2m.c` (`353` LOC), `v4l2_buffers.c` (`732` LOC) | **Stateful kernel dual-queue** (in FFmpeg `v4l2_m2m`): `OUTPUT` bitstream queue + `CAPTURE` frame queue via `VIDIOC_QBUF`/`DQBUF` (`v4l2_buffers.c:725`). *(Note: Linux also defines Stateless V4L2 Request API, supported in `cros-codecs` `v4l2r`.)* | Kernel `vb2` buffers `mmap()`ed (`v4l2_buffers.c:688-695`) or exported as `DMA-BUF` FDs via `VIDIOC_EXPBUF`. | Queue ownership transfer: between `VIDIOC_QBUF` and `VIDIOC_DQBUF`, kernel/DMA owns the buffer; dynamic resolution changes fire `V4L2_EVENT_SOURCE_CHANGE` (`ff_v4l2_m2m_codec_reinit`, `v4l2_m2m.c:208`). | Driver-aligned `bytesperline` / storage height vs. visible crop geometry (`v4l2_buffer_swframe_to_single_buffer`, `v4l2_buffers.c:369-430`); CPU access while buffer is queued causes live DMA data race. |
| **Intel QSV / oneVPL** | `hwcontext_qsv.c` (`2644` LOC), `qsvdec.c` | **Hybrid session:** `MFXVideoDECODE_DecodeFrameAsync` parses bitstream or delegates to VA-API/D3D11 child device (`qsv_init_child_ctx`, `hwcontext_qsv.c:718, 754`). `libmfx` and `libvpl` are mutually exclusive (`configure:7335-7336`). | Array of `mfxFrameSurface1` structs (`s->surfaces_internal`, `hwcontext_qsv.c:741-770`) wrapping VA-API/DXVA handles. | Polling/timeout `MFXVideoCORE_SyncOperation(session, sync, 1000)` (`hwcontext_qsv.c:1882, 1980`) + asynchronous driver mutation of `surf->Data.Locked`. | **Aliasing UB:** C/C++ runtime asynchronously increments/decrements `mfxFrameSurface1.Data.Locked` in userspace memory; holding `&mfxFrameSurface1` in Rust is immediate UB without `UnsafeCell` / atomic field projection. |

### 3. Untrusted Driver, Kernel DMA-BUF, and TOCTOU Soundness Analysis

`Basis: normative + source + execution`

In a verified media engine, GPU kernel drivers (`i915`/`xe`, `amdgpu`, `nouveau`/`nvidia`, V4L2 SoC drivers), user-mode shader/video drivers (Mesaradv/anv, proprietary ICDs), and cross-process compositor/camera peers sit **outside the verified Rust software TCB**. Treating `DMA-BUF` descriptors, mapped aperture pointers, and synchronization ioctls as trusted C structs introduces four concrete vulnerabilities:

#### 3.1 Vulnerability Class 1: Unchecked `AVDRMFrameDescriptor` Plane Offset/Pitch Arithmetic and Double-Fetch TOCTOU

In `libavutil/hwcontext_drm.h:48-150`, a `DMA-BUF` frame (`AV_PIX_FMT_DRM_PRIME`) carries up to `AV_DRM_MAX_PLANES` (`4`) objects (`fd`, `size`, `format_modifier`) and layers containing planes (`object_index`, `offset`, `pitch`). Inspecting `drm_map_frame` in `libavutil/hwcontext_drm.c:151-185` reveals:
```c
av_assert0(desc->nb_objects <= AV_DRM_MAX_PLANES);
for (i = 0; i < desc->nb_objects; i++) {
    addr = mmap(NULL, desc->objects[i].size, mmap_prot, MAP_SHARED,
                desc->objects[i].fd, 0);
    ...
    map->address[i] = addr;
    map->length[i]  = desc->objects[i].size;
}
...
for (i = 0; i < desc->nb_layers; i++) {
    const AVDRMLayerDescriptor *layer = &desc->layers[i];
    for (p = 0; p < layer->nb_planes; p++) {
        dst->data[plane] =
            (uint8_t*)map->address[layer->planes[p].object_index] +
                                   layer->planes[p].offset;
        dst->linesize[plane] =     layer->planes[p].pitch;
        ++plane;
    }
}
```
Three distinct memory-safety defects occur here if `desc` originates from an untrusted driver, IPC message, or shared memory ring (`double-fetch-toctou-shared-dma-rings-and-single-fetch-logics`):
1. **Unchecked `object_index` (`L179`):** `layer->planes[p].object_index` is never checked against `0 <= object_index < desc->nb_objects`. Values `< 0` or `>= 4` read out-of-bounds stack/heap memory around `map->address[]`; values in `[desc->nb_objects, 3]` read `NULL` (`av_mallocz` at `L133`) and compute `(uint8_t *)NULL + offset` (instant pointer-arithmetic UB in C and Rust, followed by arbitrary virtual-address dereference if `offset` is attacker-chosen).
2. **Unchecked Plane Footprint vs. `objects[object_index].size` (`L179-180`):** Even when `0 <= object_index < desc->nb_objects`, `drm_map_frame` never checks that `offset >= 0`, `pitch >= row_bytes(format, plane, width)`, or `offset + (plane_height - 1) * pitch + row_bytes <= objects[object_index].size`, nor does it call `fstat` / `lseek(fd, 0, SEEK_END)` to confirm the actual kernel `dma_buf` inode size is at least `objects[i].size` (if `objects[i].size` exceeds the backing `dma_buf` page count, Linux `mmap` may succeed or fault later with `SIGBUS` on access past EOF!).
3. **Multi-Fetch Descriptor Race:** Reading `desc` fields repeatedly across loops without copying `AVDRMFrameDescriptor` (`528` bytes on LP64) into private stack memory allows a concurrent writer in shared IPC memory to mutate `nb_objects`, `object_index`, or `offset` between validation and pointer construction.

**Executed Micro-Probe Verification (`probe_pkg2.c`, `Basis: execution`):**
On `Linux 7.1.6-1rodete1-amd64` (`x86_64`), our single-fetch validator `validate_drm_nv12_single_fetch` snapshots the `528`-byte descriptor once via `memcpy` + compiler barrier and verifies checked 64-bit `mul`/`add` bounds for a `1920x1080` NV12 surface (`pitch = 2048`, macroblock-aligned `1088` Y rows + `540` UV rows requiring `3,342,336` bytes—notably catching a naive `2048 * 1536 = 3,145,728`-byte buffer under-allocation by `188,288` bytes!):
- Valid `3,342,336`-byte descriptor: `r_valid = 0` (`OK`).
- Out-of-bounds `object_index = 2` (`nb_objects = 1`): `r_bad_idx = -34` (`-ERANGE`).
- UV plane offset overflowing BO end by `2,048` bytes: `r_bad_span = -75` (`-EOVERFLOW`).
- Measured execution latency (`2,000,000` iterations, `gcc -O2`): **`85.12 ns`** per validation (**`0.00051%`** of a `16.67 ms` 60 fps frame interval).

#### 3.2 Vulnerability Class 2: `DMA_BUF_IOCTL_SYNC` Cache Coherency vs. Concurrent DMA Aliasing

Linux kernel UAPI `include/uapi/linux/dma-buf.h:40-48` (`65e4fd942f72a9dba0e4e257290c4fa1aa756854`, verified `sizeof(struct dma_buf_sync) == 8`, `DMA_BUF_IOCTL_SYNC == 0x40086200`) normatively specifies:
> *"The synchronization provided via `DMA_BUF_IOCTL_SYNC` only provides cache coherency. It does not prevent other processes or devices from accessing the memory at the same time. If synchronization with a GPU or other device driver is required, it is the client's responsibility to wait for buffer to be ready for reading or writing before calling this ioctl with `DMA_BUF_SYNC_START`."*

Two critical consequences follow for Rust memory safety:
1. **Unchecked `DMA_BUF_IOCTL_SYNC` in `hwcontext_drm.c:113, 167-169`:** FFmpeg ignores the return code of `ioctl(fd, DMA_BUF_IOCTL_SYNC, &sync_start)` (`L169`) and `&sync_end` (`L113`). While `-ENOTTY` / `-ENOSYS` on legacy dummy exporters may be benign on cache-coherent x86 PCIe, ignoring `-EINTR`, `-ENOMEM`, or `-EFAULT` on non-coherent ARM64 SoCs leaves dirty cache lines uninvalidation/unflushed, silently corrupting decoded pixels or bitstream uploads. A sound wrapper must retry on `EINTR` and fail closed on any error other than documented `ENOTTY` when coherency is guaranteed by platform attributes.
2. **Prohibition on Direct `&[u8]` / `&mut [u8]` Slices Over Live `mmap`ed `DMA-BUF`s:** Because an untrusted GPU engine, V4L2 DMA controller, or Wayland client holding a duplicate `fd` can write to the physical pages backing a `MAP_SHARED` `DMA-BUF` at any instant (`vulkan-webgpu-explicit-memory-models-spirv-uniformity-and-shader-sandboxing`), constructing a long-lived safe Rust `&[u8]` slice over `mmap`ed `DMA-BUF` memory is **unsound** unless (a) exclusive single-process ownership of the `fd` is established *and* (b) the producer's completion fence (`poll(POLLIN)` or `DMA_BUF_IOCTL_EXPORT_SYNC_FILE` `0xc0086202`) has signaled prior to `DMA_BUF_SYNC_START`. Whenever peer processes hold the `fd`, the CPU must access the mapping strictly through raw-pointer volatile/atomic bulk copy primitives (`copy_from_dma_untrusted`), never exposing `&[u8]` to LLVM's `readonly`/`noalias` optimizations!

#### 3.3 Vulnerability Class 3: Non-Atomic Explicit-to-Implicit Fence Bridging in `hwcontext_vulkan.c`

Linux `include/uapi/linux/dma-buf.h:102-118` defines the three-step explicit synchronization protocol for Vulkan (`DMA_BUF_IOCTL_EXPORT_SYNC_FILE = 0xc0086202` $\to$ Vulkan semaphore wait + submit $\to$ `DMA_BUF_IOCTL_IMPORT_SYNC_FILE = 0x40086203`), warning explicitly at `L113-118` that steps 1–3 are **not atomic** across concurrent userspace contexts.

Inspecting `libavutil/hwcontext_vulkan.c` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) reveals an asymmetry between import and export:
- On `DMA-BUF` $\to$ Vulkan import (`L3891-3899`), `ioctl(desc->objects[i].fd, DMA_BUF_IOCTL_EXPORT_SYNC_FILE, &implicit_fd_info)` failure properly aborts frame mapping and returns `AVERROR(errno)`.
- On Vulkan $\to$ `DMA-BUF` export (`L4607-4620`), however:
  ```c
  if (ioctl(drm_desc->objects[i].fd, DMA_BUF_IOCTL_IMPORT_SYNC_FILE, &import_info) < 0)
      av_log(hwfc, AV_LOG_WARNING, "DMA_BUF_IOCTL_IMPORT_SYNC_FILE failed: %s\n", ...);
  ```
  If `dup(sync_fd)` (`L4608`, e.g., `EMFILE` under file-descriptor exhaustion) or `DMA_BUF_IOCTL_IMPORT_SYNC_FILE` (`L4614`, e.g., `ENOMEM` allocating a `dma_fence_chain` node in the kernel) fails, FFmpeg **logs a warning and returns `0` (success)**! Downstream implicit-sync consumers (KMS atomic page-flip, Wayland compositors, V4L2 encoders, or `drm_map_frame`) then read the `DMA-BUF` before `vkCmdDecodeVideoKHR` finishes writing it, causing visual tearing or reading partially initialized frame data. A sound contract must **fail closed** (or fall back to synchronous host `vkWaitSemaphores` before returning the `DMA-BUF` `fd`) whenever `IMPORT_SYNC_FILE` fails.

#### 3.4 Vulnerability Class 4: Tiled `DRM_FORMAT_MOD_*` Layout Confusion and Uncached Aperture Performance Cliffs

1. **Opaque Vendor Tiling Modifiers:** `AVDRMObjectDescriptor.format_modifier` (`hwcontext_drm.h:65`) encodes vendor tiling and lossless framebuffer compression (`DRM_FORMAT_MOD_LINEAR = 0`, Intel Y/4-tile + CCS media compression, AMD DCC, NVIDIA `BLOCK_LINEAR`). Treating a non-linear `DMA-BUF` as pitch-linear row-major planes in `drm_map_frame` (`hwcontext_drm.c:178-181`) either reads scrambled macro-tile swizzles or overruns auxiliary compression control surfaces (`CCS`). Sound CPU mapping must reject `format_modifier != DRM_FORMAT_MOD_LINEAR` unless an explicit detiling kernel or driver transfer (`vaGetImage` in `hwcontext_vaapi.c:910`) is invoked.
2. **The `vaDeriveImage` USWC Read Cliff (`hwcontext_vaapi.c:874-920`):** On Intel integrated/discrete GPUs, `vaDeriveImage` + `vaMapBuffer2` exposes GPU surface memory via Uncacheable Speculative Write-Combining (`USWC`). Standard CPU scalar/AVX loads from `USWC` memory bypass CPU caches completely, collapsing 1080p frame readback from `>10 GB/s` to `<200 MB/s` (`15–30 ms` per frame—slower than pure software decoding!) unless SSE4.1 `MOVNTDQA` 64-byte streaming loads into WC-aligned scratch buffers are used. `hwcontext_vaapi.c:881-882` avoids this trap by refusing `vaDeriveImage` whenever `AV_HWFRAME_MAP_READ` is set without `AV_HWFRAME_MAP_DIRECT`, routing readbacks through `vaCreateImage` + `vaGetImage` (`L900-918`, GPU copy engine detile into cached WB RAM).
3. **NVDEC's Three-Way Output Surface Dilemma (`nvdec.c:661-705, 919-965`):**
   - **Default Safe Copy Mode (`opaque_output=0, unsafe_output=0`):** Sets `ulNumOutputSurfaces = 1` (`L662`), maps into a single temporary linear buffer via `cuvidMapVideoFrame` (`L919`), and **executes an extra device-to-device VRAM copy** on every frame via `av_frame_make_writable(frame)` (`L965`).
   - **`unsafe_output = 1` Mode (`L662, 962`):** Sets `ulNumOutputSurfaces = min(initial_pool_size, 64)` and skips `av_frame_make_writable`, returning the `cuvidMapVideoFrame` pointer directly. If downstream queues hold all mapped slots, `cuvidMapVideoFrame` fails (`dynlink_cuviddec.h:1212`).
   - **`CUarray` `opaque_output = 1` Mode (`L673-705`):** Registers `AVCUDAFramesContext` `CUarray` surfaces directly as NVDEC decode targets via `cuvidRegisterDecodeSurfaces` (`L693`), eliminating the extra VRAM blit while bounding capacity through the unified `AVBufferPool`.

### 4. Sound Hardware-Contract Architecture for a Clean Rust Media Engine

`Basis: source + derived`

Inspecting `chromeos/cros-codecs` (`a050c6cde530e563197ee9e3e72ab01f48a0c41f`, `Cargo.toml:10-29`, `README.md:13-28`) alongside FFmpeg's `vulkan_decode.c` and `vaapi_decode.c` demonstrates the clean-room modularization principle: **separate verified pure-Rust codec state machines from minimal unsafe hardware backend drivers**.

#### 4.1 Two-Layer Separation: Verified Codec Frontend vs. Minimal Backend Traits

1. **Verified Pure-Rust Stateless Codec Core (`#![forbid(unsafe_code)]`):**
   - Bitstream NAL/OBU framing, Golomb/arithmetic header parsing (SPS, PPS, VPS, Sequence Header, Frame Header, Slice Header), reference picture list construction, POC/order-hint wrapping arithmetic, and the **DPB slot allocation & eviction automaton** for H.264, HEVC, VP8, VP9, and AV1 are 100% pure algorithmic logic with **zero OS or GPU dependencies**.
   - In FFmpeg, this header/DPB preparation is entangled with mutable `H264Context` / `HEVCContext` / `AV1DecContext` C state and repeated across `vaapi_*.c`, `vulkan_*.c`, `nvdec_*.c`, `d3d12va_*.c`, and `vdpau_*.c`. Factoring it once into a verified Rust frontend allows **one set of UB-freedom, Panic-freedom, and ITU-T/AOM spec-conformance proofs** to drive *all* stateless backends (`Vulkan Video`, `VA-API`, `D3D11VA`, `D3D12VA`, `NVDEC`, and Linux Stateless `V4L2 Request`).
2. **Linear Typestate Surface & Fence Algebra:**
   Model every hardware frame slot as a move-only Rust linear/typestate token parameterized by a backend-specific handle (never raw `AVFrame.data[]` pointer casts):
   - `SurfaceToken<Free>` $\xrightarrow{\text{begin\_decode(dpb\_refs)}}$ `SurfaceToken<Decoding>` (carries `TimelineFence` + `Arc`-cloned read leases on all active DPB reference `SurfaceToken<DecodedGpu>` slots, statically preventing premature DPB slot reuse such as `VUID-VkVideoBeginCodingInfoKHR-slotIndex-07245`!).
   - `SurfaceToken<Decoding>` $\xrightarrow{\text{wait\_bounded(timeout)}}$ `Result<SurfaceToken<DecodedGpu>, HwError::{Timeout, DeviceLost, DecodeError}>` (enforcing **Priority 2: Panic-freedom & Hang-freedom** by requiring finite deadlines via `vkWaitSemaphores`, `vaSyncSurface2`, `poll(fd, timeout_ms)`, or `WaitForSingleObjectEx(event, timeout_ms, FALSE)`—banning `INFINITE` waits!).
   - `SurfaceToken<DecodedGpu>` supports three sound consumption transitions:
     1) **Zero-Copy GPU / Display Export (`export_dmabuf`):** Calls `vkGetMemoryFdKHR` + `DMA_BUF_IOCTL_IMPORT_SYNC_FILE` (falling back to synchronous `vkWaitSemaphores` if `IMPORT_SYNC_FILE` fails!) or `vaSyncSurface` + `vaExportSurfaceHandle`, returning an `OwnedFd`-backed `ValidatedDrmFrame` whose plane offsets/pitches have already passed `validate_drm_single_fetch`.
     2) **GPU-Detiled Cached CPU Download (`download_to_cpu`):** Uses `vaGetImage`, `cuMemcpy2DAsync` + `cuStreamSynchronize`, or `D3D12` staging readback into Rust-owned aligned `[u8]` buffers, avoiding `USWC` aperture stalls and concurrent DMA aliasing.
     3) **Direct Volatile Aperture Read (`map_direct_untrusted`):** Permitted only when `format_modifier == DRM_FORMAT_MOD_LINEAR`, fence completion is confirmed, `DMA_BUF_IOCTL_SYNC(START)` succeeds, and reads use volatile/MOVNTDQA copy-in rather than long-lived `&[u8]` borrows.

#### 4.2 Implications Across the Four-Level Verification Priority Stack

1. **Priority 1 — UB-Freedom:** Achieved across the Rust host by (a) replacing `AVFrame.data[0..3]` pointer-integer punning with typed handles (`VASurfaceID(u32)`, `CuDevicePtr(u64)`, `VkImage`, `OwnedFd`), (b) enforcing single-fetch overflow-checked bounds on every driver-returned `AVDRMFrameDescriptor` / `VAImage` (`offsets[i]`, `pitches[i]`), (c) wrapping QSV/V4L2/CUDA thread-local and shared-struct state in `UnsafeCell`/RAII context guards (`CudaContextPushGuard` guaranteeing `cuCtxPopCurrent` on every early return and unwind), and (d) never forming `&[u8]` over live peer-writable `DMA-BUF` mappings.
2. **Priority 2 — Panic-Freedom (and Liveness):** Achieved by bounded-timeout waits on every GPU/firmware fence, checked arithmetic on resolution/pitch/DPB sizing, explicit `Poll::Pending` / backpressure when fixed hardware pools (`NVDEC` `32` surfaces, `D3D11VA` `ArraySize`) are saturated by downstream consumers, and clean `HwError::DeviceLost` recovery on GPU TDR / `MEDIA_ERROR_SERVER_DIED`.
3. **Priority 3 — Behavioral Equivalence & Differential Oracles:** Unlike SIMD-vs-scalar software DSP kernels—which can be proved **bit-identical** in Lean against scalar Rust reference functions—hardware video engines contain closed silicon RTL and signed vendor firmware (`NVDEC` Falcon/GSP microcode, Intel HuC/GuC/Vdbox, Apple VideoToolbox, Qualcomm Iris).
   - For **decoders** of standards with bit-exact normative reconstruction (ITU-T H.264, ITU-T H.265/HEVC, AV1, VP9), compliant hardware *should* produce bit-identical YUV output to software reference decoders (`dav1d`/`rav1d`, `ff_h264`, `ff_hevc`), **except** on damaged/error-concealed streams or driver firmware bugs; verification therefore pairs **machine-checked proofs of the Rust bitstream/DPB frontend** with **hardware-in-the-loop conformance vector suites** (ITU-T JVT/JCT-VC/AOM vectors via `Fluster`, `cros-codecs/README.md:59-66`).
   - For **legacy non-bit-exact decoders** (MPEG-2 IEEE 1180 IDCT tolerances) and **all hardware encoders** (`NVENC`, `VA-API`, `Vulkan Encode`, `VideoToolbox`, `QSV`, where rate-control, motion estimation, and RDO reside in proprietary hardware/firmware), bit-exact equivalence to software encoders (`x264`/`rav1e`) **does not exist**; validation must check **bitstream syntactic/semantic conformance** (decoding hardware-encoded bitstreams with verified software decoders + checking PSNR/VMAF/HRD buffer invariants).
4. **Priority 4 — Full Functional Specification Conformance:** Hardware engines impose rigid profile/level/chroma/dimension envelopes (`AVHWFramesConstraints`, e.g., no 4:2:2 12-bit or >`8192x8192` on older silicon, max `16`–`32` DPB surfaces). A spec-conformant media engine must maintain an automatic, zero-panic **capability probe + transparent software fallback** path whenever stream parameters change mid-bitstream (e.g., an H.264 SPS switch from `High` 8-bit 4:2:0 to `High 4:4:4 Predictive` 10-bit).

## Boundaries

- **Not examined — Live GPU execution benchmarks and vendor silicon errata:** Because the isolated Linux build environment exposes no `/dev/dri/renderD*` or `/dev/nvidia*` hardware nodes, we did not execute live `vkCmdDecodeVideoKHR`, `vaEndPicture`, or `cuvidDecodePicture` throughput/power sweeps or vendor-specific firmware fuzzing; findings on GPU stalls (`USWC` `vaDeriveImage`, `NVDEC` `av_frame_make_writable`, `D3D12` `INFINITE` fence waits) derive directly from upstream FFmpeg source implementations and kernel UAPI contracts.
- **Not examined — Secondary platform-specific backends (`DXVA2`, `AMF`, `OpenCL`, `MMAL`, `RKMPP`, `OHCodec`):** `AVHWDeviceType` (`hwcontext.h:27-44`) and `configure` also include legacy Windows `DXVA2`, AMD `AMF`, `OpenCL`, Raspberry Pi `MMAL`, Rockchip `RKMPP`, and OpenHarmony `OHCodec`; these follow the same four taxonomic archetypes (stateless DXVA2, hybrid vendor SDK AMF/RKMPP, stateful OS OHCodec) but their wrapper files were not audited line-by-line here.
- **Known not to apply — Software TCB proofs over GPU silicon and signed codec firmware:** Formal verification of the Rust host and stateless header/DPB state machines guarantees host memory safety, absence of host panics/hangs, and valid API command submission, **not** functional correctness or absence of silicon/IOMMU bugs inside closed GPU microcode. Full system isolation against a malicious or compromised PCIe GPU requires IOMMU DMA remapping (`VT-d`/`SMMU` without unrestricted ATS bypass; see `rdma-weak-memory-iommu-ats-and-byzantine-peripheral-verification`).
- **Unsupported — Zero-copy `DMA-BUF` export in `VDPAU` and `MediaCodec` `Surface` CPU readback:** Upstream `hwcontext_vdpau.c:528-530` supports only copy transfers (`get_data`/`put_data`), and Android `AMediaCodec` bound to an opaque `Surface`/`ANativeWindow` does not expose decoded buffers to CPU `mmap` without routing through an `ImageReader` (`AHardwareBuffer`) or OpenGL/Vulkan external texture import.

## Evidence

### Primary Repository Sources Inspected

1. **`FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`):**
   - `libavutil/hwcontext.h:25-165` & `libavutil/hwcontext.c:334-860` — `AVHWDeviceType`, `AVHWDeviceContext`, `AVHWFramesContext`, `av_hwframe_ctx_init`, `av_hwframe_get_buffer`, `av_hwframe_transfer_data`, `av_hwframe_map`.
   - `libavutil/hwcontext_internal.h:60-155` — `HWContextType` 13-method vtable, `FFHWFramesContext`, `HWMapDescriptor`.
   - `libavutil/hwcontext_drm.h:42-168` & `libavutil/hwcontext_drm.c:96-195, 317-319` — `AVDRMFrameDescriptor` layout, unchecked `DMA_BUF_IOCTL_SYNC` (`L113, 169`), and unvalidated `object_index` / `offset` / `pitch` pointer arithmetic (`L178-181`).
   - `libavutil/hwcontext_vaapi.c:673-698, 855-955, 1360-1435` & `libavcodec/vaapi_decode.c:34-267, 705-755` — `vaSyncSurface`, `vaDeriveImage` `USWC` read avoidance (`L874-899`), `vaGetImage` fallback (`L900-920`), `vaExportSurfaceHandle` `DRM_PRIME_2` (`L1388-1425`), and `vaBeginPicture`/`vaRenderPicture`/`vaEndPicture` (`vaapi_decode.c:191-238`).
   - `libavutil/hwcontext_vdpau.c:91-104, 285, 335-400, 528-530` — Copy-only `VdpVideoSurface` transfers.
   - `libavutil/hwcontext_cuda.c:119-248, 707-725`, `libavcodec/nvdec.c:263, 645-715, 905-965, 1058-1063`, & `libavcodec/nvenc.c:387, 2315-2730` — `cuCtxPushCurrent` TLS Discipline, `NVDEC_MAX_DECODE_SURFACES` cap (`L648-661`), `ulNumOutputSurfaces` 3-way split (`L662, 673-705, 962-965`), and `nvEncRegisterResource`/`nvEncLockBitstream`.
   - `libavutil/hwcontext_vulkan.c:810, 2948-2985, 3247, 3631, 3776-3788, 3868-3920, 4585-4635`, `libavcodec/vulkan_decode.c:153-235, 379, 444-585, 1046-1060, 1373-1405`, & `libavcodec/vulkan_encode.c:182-245` — `VK_EXT_external_memory_dma_buf`, `DMA_BUF_IOCTL_EXPORT_SYNC_FILE` (`L3891`), warn-only `DMA_BUF_IOCTL_IMPORT_SYNC_FILE` (`L4614-4615`), `VUID-VkVideoBeginCodingInfoKHR-slotIndex-07245` (`vulkan_decode.c:225`), and 3-way DPB architecture.
   - `libavutil/hwcontext_videotoolbox.c:683-815` & `libavcodec/videotoolbox.c:760, 1007` — `CVPixelBufferLockBaseAddress` and `VTDecompressionSession`.
   - `libavutil/hwcontext_mediacodec.c:35-100`, `libavcodec/mediacodecdec_common.c:289-513, 937-1075`, & `configure:7499` — `ANativeWindow` persistent surface and `AMediaCodec` buffer queue calls.
   - `libavutil/hwcontext_d3d11va.c:250-340, 435-505` — Static `ArraySize` `ID3D11Texture2D` pool (`L261-263, 304`), `DXGI_FORMAT_420_OPAQUE` (`L295-296`), and locked staging texture transfer (`L451-498`).
   - `libavutil/hwcontext_d3d12va.c:45-46, 88-105, 298, 354-398, 585-610` & `libavcodec/d3d12va_decode.c:486-690` — `ID3D12VideoDecodeCommandList`, `ID3D12Fence`, and `WaitForSingleObjectEx(..., INFINITE, FALSE)` (`L88, 103`).
   - `libavcodec/v4l2_m2m.c:208-328` & `libavcodec/v4l2_buffers.c:350-430, 688-725` — `VIDIOC_QBUF`, `mmap`, and active-vs-storage stride validation (`v4l2_buffer_swframe_to_single_buffer`).
   - `libavutil/hwcontext_qsv.c:107-128, 710-785, 1882, 1980` & `configure:7335-7336` — `mfxFrameSurface1` pool, `MFXVideoCORE_SyncOperation`, and `libmfx`/`libvpl` mutual exclusion.
2. **Normative Specifications, Kernel UAPI, & Rust Precedent:**
   - `KhronosGroup/Vulkan-Headers` (`d277a0a3cda9c682708c93279f0c72cd6b0ae3f3`): `include/vulkan/vulkan_core.h:9391-9575, 12144` (`VkVideoSessionCreateInfoKHR`, `VkVideoBeginCodingInfoKHR`, `VK_KHR_VIDEO_DECODE_QUEUE_SPEC_VERSION = 8`, `VK_VIDEO_DECODE_CAPABILITY_DPB_AND_OUTPUT_{COINCIDE,DISTINCT}_BIT_KHR`, `VkVideoDecodeInfoKHR`, `VK_KHR_VIDEO_ENCODE_QUEUE_SPEC_VERSION = 12`).
   - `intel/libva` (`f052e984e0c8bf10784198cc311b23c567b1367f`): `va/va.h:3977-4900` (`vaMapBuffer`, `vaMapBuffer2`, `vaBeginPicture`, `vaRenderPicture`, `vaEndPicture`, `vaSyncSurface`, `vaSyncSurface2`, `vaDeriveImage`), `va/va_drmcommon.h:102-160` (`VADRMPRIMESurfaceDescriptor`).
   - `FFmpeg/nv-codec-headers` (`f2053071ea93137255b6dcf42e9b4c9e0965a44e`): `include/ffnvcodec/dynlink_cuviddec.h:279-340, 1212-1316` (`CUVIDDECODECREATEINFO`, `ulNumDecodeSurfaces`, `ulNumOutputSurfaces`, `cuvidMapVideoFrame64`).
   - `torvalds/linux` (`65e4fd942f72a9dba0e4e257290c4fa1aa756854`): `include/uapi/linux/dma-buf.h:27-132` (`struct dma_buf_sync`, `DMA_BUF_IOCTL_SYNC`, `struct dma_buf_export_sync_file`, non-atomicity and cache-coherency-only contract).
   - `chromeos/cros-codecs` (`a050c6cde530e563197ee9e3e72ab01f48a0c41f`): `Cargo.toml:1-50`, `README.md:1-71` (BSD-3-Clause Rust stateless decoder/encoder architecture over `cros-libva` and `v4l2r`).

### Executed Micro-Probe (`2026-11-20`, `Linux 7.1.6-1rodete1-amd64 x86_64`)

Compiled with `gcc -O2 -Wall -Wextra probe_pkg2.c -o probe_pkg2`:
```text
sizeof_dma_buf_sync=8 ioctl_SYNC=0x40086200 ioctl_EXPORT_SYNC_FILE=0xc0086202 ioctl_IMPORT_SYNC_FILE=0x40086203
r_valid=0 r_bad_idx=-34 r_bad_span=-75 single_fetch_validate_ns=85.12 sizeof_desc=528
```

## Revalidation

1. **FFmpeg `DMA-BUF` & Vulkan Sync Audit (<10 s):**
   Diff `libavutil/hwcontext_drm.c` (`drm_map_frame`) and `libavutil/hwcontext_vulkan.c` (`DMA_BUF_IOCTL_IMPORT_SYNC_FILE`) against `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` to check whether upstream added bounds checks on `layer->planes[p].object_index` / `offset` / `pitch` or promoted `DMA_BUF_IOCTL_IMPORT_SYNC_FILE` failure from `AV_LOG_WARNING` to a hard error.
2. **Vulkan Video & NVDEC Header Evolution Check (<10 s):**
   Check `VK_KHR_VIDEO_DECODE_QUEUE_SPEC_VERSION` and `VK_KHR_VIDEO_ENCODE_QUEUE_SPEC_VERSION` in `KhronosGroup/Vulkan-Headers` (`include/vulkan/vulkan_core.h`) for new capability flags (e.g., `VK_KHR_video_maintenance2` inline session parameters), and check `libavcodec/nvdec.c` for whether `CUarray` `opaque_output` superseded `ulNumOutputSurfaces = 1` as default.
3. **Single-Fetch UAPI Bounds Probe (<2 s):**
   Compile and run `probe_pkg2.c` against `<linux/dma-buf.h>` on the target Linux kernel to verify `DMA_BUF_IOCTL_SYNC` (`0x40086200`), `DMA_BUF_IOCTL_EXPORT_SYNC_FILE` (`0xc0086202`), and `DMA_BUF_IOCTL_IMPORT_SYNC_FILE` (`0x40086203`) ioctl encodings and confirm `r_valid == 0`, `r_bad_idx == -ERANGE`, and `r_bad_span == -EOVERFLOW`.
