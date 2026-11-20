# FFmpeg libav* Public C ABI Layout, Callback Contracts, and Soundness Obligations for a Clean Rust Compatibility Layer

## Summary

A drop-in C ABI compatibility layer over a clean-room Rust multimedia core cannot treat `FFmpeg/FFmpeg` public headers as passive Plain Old Data (POD) value types. Inspection of `FFmpeg/FFmpeg` at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` establishes six load-bearing invariants across the `libavutil`, `libavcodec`, and `libavformat` boundaries (`Basis: source + normative`):

1. **Public contexts are semi-opaque, append-only structs embedded at offset `0` of internal wrappers.** `AVCodecContext`, `AVFormatContext`, `AVFrame`, `AVIOContext`, `AVStream`, and `AVProgram` exclude `sizeof(...)` from the public ABI so minor releases can append fields; callers must heap-allocate them via `av*_alloc*()`. Internally, FFmpeg embeds the public struct as the first field (`pub`) of an internal container struct (`FFCodecContext` in `libavcodec/avcodec_internal.h:33-45`) and casts between them. Moving `AVFrame` by value in Rust is unsound whenever `extended_data == &frame.data[0]`, as confirmed in a standalone `gcc 15.2.0` + `rustc 1.98.0-nightly` micro-probe (`Basis: execution`).
2. **`AVClass` and `AVOption` rely on byte-offset struct reflection.** Every loggable or option-configured context places `const AVClass *` at byte offset `0`, and `av_opt_set*` / `av_opt_get*` compute `((uint8_t *)obj) + o->offset` directly (`libavutil/opt.c:221,904-954,1317-1487`), mutating integers, floats, rationals, `av_malloc`-allocated C strings, and `AVDictionary *` pointers in place without setter hooks.
3. **`AVBuffer` refcounting mixes relaxed increments with `acq_rel` decrements and non-atomic writability probes.** `av_buffer_ref` increments with `memory_order_relaxed` and `buffer_replace` decrements with `memory_order_acq_rel`, caching `!(b->flags_internal & BUFFER_FLAG_NO_FREE)` before calling `b->free(b->opaque, b->data)` because `free` may destroy the enclosing pool entry (`libavutil/buffer.c:113,130-137`). `av_buffer_is_writable` (`libavutil/buffer.c:148-154`) performs a standalone `atomic_load`, which cannot prevent Time-of-Check-to-Time-of-Use (TOCTOU) races if an external C caller clones or shares `AVBufferRef` across threads.
4. **Input buffers and plane allocations carry implicit alignment and over-read padding contracts.** `av_malloc` aligns to `16`, `32` (AVX), or `64` bytes (AVX-512) (`libavutil/mem.c:66,193-215`) and enforces a default `INT_MAX` cap (`max_alloc_size`, `mem.c:169`), while `AV_INPUT_BUFFER_PADDING_SIZE = 64` (`libavcodec/defs.h:40`) requires zeroed trailing padding so bitstream readers and SIMD kernels can safely over-read past `pkt->size`.
5. **Callback validation in upstream C is minimal, shifting full pointer/aliasing verification onto a Rust shim.** `validate_avframe_allocation` (`libavcodec/decode.c:1719-1738`) checks only that active `frame->data[i]` pointers are non-NULL (`av_assert0`) and zeroes unused plane pointers—it does not verify alignment, plane disjointness, stride sufficiency, or `AVBufferRef` backing. Similarly, `read_packet_wrapper` (`libavformat/aviobuf.c:501-510`) relies on caller callbacks returning `<= buf_size` bytes and `av_log_set_callback` stores a bare function pointer with `memory_order_relaxed` (`libavutil/log.c:497-500`) without locking around external callbacks.
6. **Quarantining FFI boundaries add sub-5-ns call overhead while preserving Rust core ergonomics.** In a 50M-iteration micro-probe on AMD EPYC 7B12 (`rustc 1.98.0-nightly -C opt-level=3`), wrapping a Rust slice kernel in an `extern "C"` boundary shim with null/alignment/stride-overflow checks and `std::panic::catch_unwind` added `1.100 ns/call` over a direct non-inlined Rust slice call (`3.888 ns` vs `2.788 ns/call`). Consequently, a clean Rust core should expose idiomatic `&[u8]` / typed-frame Rust APIs natively and isolate C ABI obligations—including `#[repr(C)]` shadow structs, `AVOption` field tables, and callback sanitization—inside a thin compatibility crate, following the ownership separation pioneered in `memorysafety/rav1d`.

## Applicability

These findings apply to the public C ABI surface of `FFmpeg/FFmpeg` at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (corresponding to `libavcodec` major `63`, `libavformat` major `63`, `libavdevice` major `63`, `libavutil` major `61`, `libavfilter` major `12`, `libswscale` major `10`, and `libswresample` major `7`) targeting LP64/LLP64 C toolchains and Rust `1.98.0-nightly` / Edition 2024 FFI semantics (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`).

The architectural analysis compares two designs against this contract:
- **Quarantined Shim Architecture:** A pure Rust multimedia core using safe Rust slices, enums, and owned buffers (`Box<[u8]>`, `Arc`, typed option structs), fronted by a thin `cdylib`/`staticlib` compatibility crate that exports `libav*` symbols, validates hostile/buggy C inputs, and translates C structs/callbacks at API boundaries (analogous to `memorysafety/rav1d@2e7216c20ac2a75de204d6c8d7268b75a45959b4`).
- **Native-C-Struct Core:** An architecture that uses `#[repr(C)]` `AVFrame`/`AVCodecContext`/`AVPacket` layouts directly inside internal decoders, muxers, and filters.

Related corpus reports cover general Rust ABI calling conventions and `C-unwind` (`rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`), `#[repr(C)]` layout rules (`rust-reference-layout-guarantees-target-abi-limits-and-semver-snares`), handle-table pinning (`handle-tables-scoped-arenas-and-cross-runtime-ffi-pinning-protocols`), FFI strangulation (`incremental-c2rust-lifting-mvee-shadow-execution-and-ffi-strangulation`), and byte-projection validity predicates (`zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics`); this report focuses specifically on FFmpeg-specific ABI surfaces and their verification obligations.

## Findings

### 1. Dynamic Symbol Versioning, `avpriv_*` Cross-Library Coupling, and Linker Semantics

`Basis: source`

FFmpeg separates its multimedia libraries into seven shared objects whose GNU `ld` version scripts (`libav*/libav*.v`) define exported symbol globs and SONAME namespaces. At `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, major versions and version-script export patterns are:

| Library | `VERSION_MAJOR` | Version Script Path | Global Globs Exported | Hidden |
| :--- | :--- | :--- | :--- | :--- |
| `libavutil` | `61` (`libavutil/version.h:81`) | `libavutil/libavutil.v` | `av*;` | `*` |
| `libavcodec` | `63` (`libavcodec/version_major.h:26`) | `libavcodec/libavcodec.v` | `av_*; avcodec_*; avpriv_*; avsubtitle_free;` | `*` |
| `libavformat` | `63` (`libavformat/version_major.h:26`) | `libavformat/libavformat.v` | `av*;` | `*` |
| `libavfilter` | `12` (`libavfilter/version_major.h:26`) | `libavfilter/libavfilter.v` | `avfilter_*; av_*;` | `*` |
| `libswscale` | `10` (`libswscale/version_major.h:26`) | `libswscale/libswscale.v` | `swscale_*; sws_*;` | `*` |
| `libswresample` | `7` (`libswresample/version_major.h:26`) | `libswresample/libswresample.v` | `swr_*; swresample_*;` | `*` |
| `libavdevice` | `63` (`libavdevice/version_major.h:26`) | `libavdevice/libavdevice.v` | `avdevice_*; av_*;` | `*` |

Two structural constraints emerge directly from these scripts and `configure`:
- **Cross-DSO `avpriv_*` private ABI:** `libavcodec.v` explicitly exports `avpriv_*`, and `libavutil.v` / `libavformat.v` / `libavfilter.v` / `libavdevice.v` match `av*;` (which includes `avpriv_*`). Upstream `libavcodec`, `libavformat`, and `libavfilter` invoke `avpriv_*` symbols across shared-library boundaries (`libavcodec/pthread_slice.c:76,96,141` calls `avpriv_slicethread_*` in `libavutil`, for example). Consequently, if an external binary links against a Rust `libavcodec.so` while retaining C `libavformat.so` (partial replacement), either `avpriv_*` compatibility must be maintained at exact internal binary layouts or all `libav*` DSOs must be replaced together as a coherent multi-crate workspace sharing one Rust core.
- **Allocator interposition blocked by `-Wl,-Bsymbolic`:** `configure:7961` passes `-Wl,-Bsymbolic` when supported by the linker, and `libavutil/mem.c:164-167` documents that overriding `av_malloc`/`av_free` via symbol interposition requires dynamic linking *without* `-Wl,-Bsymbolic`. A Rust `cdylib` replacement using `-Wl,-Bsymbolic` preserves identical intra-DSO symbol resolution performance while preventing partial symbol overrides from breaking internal allocator pairing.
- **Deprecation gates (`FF_API_*`):** Public headers gate legacy fields/APIs behind `(LIBAV*_VERSION_MAJOR < next)` macros (e.g., `FF_API_INIT_PACKET` in `libavcodec/version_major.h`, `FF_API_CPU_FLAG_FORCE` in `libavutil/version.h:108-112`, `FF_API_COMPUTE_PKT_FIELDS2` in `libavformat/version_major.h`). A drop-in shim must match the exact `FF_API_*` configuration of its targeted SONAME major release because removing a gated struct field shifts offsets of all subsequent fields.

### 2. Heap Allocation Guarantees, SIMD Alignment, and `AV_INPUT_BUFFER_PADDING_SIZE`

`Basis: source`

Upstream `av_malloc(size_t size)` (`libavutil/mem.c:193-215`) establishes three ABI contracts relied upon by C callers and codecs:

1. **Target-dependent power-of-two alignment:** `ALIGN` is defined at `libavutil/mem.c:66` as `HAVE_SIMD_ALIGN_64 ? 64 : (HAVE_SIMD_ALIGN_32 ? 32 : 16)`, driven by `configure:3020-3021,5712` (`simd_align_32` for AVX, `simd_align_64` for AVX-512). Allocations use `posix_memalign(&ptr, ALIGN, size)` or `_aligned_malloc(size, ALIGN)` (with an explicit ASan header wrapper on Windows at `mem.c:84-160`). Thus, C callers that construct `AVFrame` or `AVPacket` payloads via `av_malloc` / `av_mallocz` expect `av_free` / `av_freep` to accept that pointer regardless of which `libav*` module allocated it.
2. **Global atomic allocation ceiling and zero-size behavior:** `max_alloc_size` is a `static atomic_size_t` initialized to `INT_MAX` (`libavutil/mem.c:169-173`) and checked in `av_malloc` (`mem.c:197`) and `av_realloc` (`mem.c:608`). Additionally, `av_malloc(0)` delegates to `av_malloc(1)` via `av_realloc(NULL, 1)` (`mem.c:245-246`), returning a valid non-NULL pointer rather than `NULL`. Rust's global allocator returns dangling non-null ZST pointers for size `0` and relies on `std::alloc::Layout` with explicit alignment on `dealloc`; therefore, a compatibility shim implementing `av_malloc` / `av_realloc` / `av_free` must store allocation metadata (or route through `libc::posix_memalign`/`free` or a size/align prefix header) so `av_free(ptr)` does not require the caller to supply size or alignment—note that `av_realloc` on a `posix_memalign`-backed pointer cannot trivially use `std::alloc::realloc` unless the original alignment is tracked or `posix_memalign` + `memcpy` is used when alignment > `align_of::<max_align_t>()`.
3. **`AV_INPUT_BUFFER_PADDING_SIZE = 64` over-read contract:** `libavcodec/defs.h:40` defines `#define AV_INPUT_BUFFER_PADDING_SIZE 64` and documents that input bitstreams passed to decoders (and `AVCodecContext.extradata`) must have at least 64 additional zeroed bytes past the logical buffer end (`pkt->size`) so fast bitstream readers and SIMD loads can read up to 64 bytes ahead without branching on every byte.

**Clean Rust rewrite implication (`Basis: derived`):**
- **UB-freedom & Panic-freedom:** A clean Rust decoder core must *never* assume a caller-provided buffer actually has 64 readable bytes past `len` unless verified. When receiving an `AVPacket` over the C ABI:
  - *Fast zero-copy path:* If `pkt->buf != NULL` and `pkt->buf->size >= (pkt->data - pkt->buf->data) + pkt->size + 64` (checking no arithmetic overflow and verifying trailing 64 bytes or safely treating them as readable slice `[..pkt.size + 64]`), the shim can hand a `&[u8]` plus a `padded: bool` capability token to the Rust bitstream reader.
  - *Safe fallback path:* If `pkt->buf == NULL` (unmanaged legacy C pointer where buffer allocation size is unknown!) or trailing capacity `< 64`, reading past `pkt->data[pkt->size]` in Rust would be Undefined Behavior (out-of-bounds read). The shim must copy `pkt->size` bytes into a reusable `64`-byte-padded scratch buffer or route to a bounds-checked Rust slice reader, completely preventing heap out-of-bounds reads on buggy C callers without penalizing compliant `AVBufferRef` callers.

### 3. Semi-Opaque Struct Layouts, Self-Referential `AVFrame`, and `AVBuffer` Ownership

`Basis: source + execution`

Public headers explicitly forbid `sizeof(...)` outside `libav*` on core context and carrier structs (`libavcodec/avcodec.h:441`, `libavcodec/packet.h:578-581`, `libavutil/frame.h:331,473`, `libavutil/buffer.h:79`, `libavformat/avformat.h:768,974,1325,1394`, `libavformat/avio.h:153`).

#### Container-of Embedding vs. Handle-Backed Shadowing
Inside FFmpeg, `libavcodec/avcodec_internal.h:33-45` embeds `AVCodecContext pub` at byte offset `0` of `FFCodecContext`, and `libavcodec/options.c:149-158` allocates `FFCodecContext` via `av_mallocz(sizeof(*ffavc))` and returns `&ffavc->pub`. Any internal private state sits cleanly behind `pub` (or in `avctx->internal`). A Rust compatibility crate can adopt this exact `#[repr(C)]` header-prefix trick (`struct FFCodecContextShim { pub: AVCodecContext, rust_state: ... }`), provided the heap allocation is **never moved** (`Pin<Box<FFCodecContextShim>>` or `Box::into_raw`), because external C code holds raw `*mut AVCodecContext` pointers to offset `0`.

#### The `AVFrame.extended_data` Self-Referential Move Hazard
`AVFrame` (`libavutil/frame.h:479-838`) contains inline arrays `uint8_t *data[8]` (`AV_NUM_DATA_POINTERS = 8`, `L500`), `int linesize[8]` (`L524`), `AVBufferRef *buf[8]` (`L656`), and `uint8_t **extended_data` (`L540`). For video and for audio with `<= 8` channels, `av_frame_get_buffer` sets `frame->extended_data = frame->data`—a self-referential pointer into the `AVFrame` struct itself. For planar audio with `> 8` channels, `extended_data` points to an `av_malloc`-allocated heap array of `uint8_t *` pointers backed by `extended_buf` (`L659-663`).

Because `#[repr(C)]` Rust structs are movable by value (`mem::swap`, returning from functions, `Box::new(frame)` after stack construction), moving an `AVFrame` by value after `extended_data = data.as_mut_ptr()` immediately leaves `extended_data` dangling at the previous stack or heap address. In a standalone probe compiled on `x86_64-unknown-linux-gnu` (`gcc 15.2.0` + `rustc 1.98.0-nightly`, `Basis: execution`), moving a `FakeAVFrame` (`sizeof = 128`, `offsetof(extended_data) = 96` in both C and Rust) from a heap `Box` to a stack frame and passing it by value to `move_frame_by_value` shifted `&f.data[0]` from `0x563e8195cd50` to `0x7ffc5b421860` while `f.extended_data` remained `0x563e8195cd50` (`dangling = true`). In Rust, public `AVFrame` instances must therefore be heap-pinned behind raw pointers (`NonNull<AVFrame>`) and manipulated exclusively via reference-counted handles (`av_frame_alloc` / `av_frame_move_ref` / `av_frame_unref`), never moved by value across Rust APIs.

#### `AVBuffer`, `AVBufferRef`, and `AVBufferPool` Soundness vs. `rav1d`
Inspection of `libavutil/buffer_internal.h:35-98` and `libavutil/buffer.c:30-260` reveals subtle concurrency and aliasing obligations:
- **Refcount memory orderings (`buffer.c:113,130-137`):** `av_buffer_ref` increments `buf->buffer->refcount` with `atomic_fetch_add_explicit(..., 1, memory_order_relaxed)`, whereas `buffer_replace` decrements with `atomic_fetch_sub_explicit(..., 1, memory_order_acq_rel)`. Crucially, lines `131-136` read `int free_avbuffer = !(b->flags_internal & BUFFER_FLAG_NO_FREE);` *before* invoking `b->free(b->opaque, b->data)`, because `BufferPoolEntry` embeds `AVBuffer buffer` inline (`buffer_internal.h:68`) and `pool_release_buffer` may destroy `b` during `b->free(...)`.
- **Single-writer vs. shared aliasing (`buffer.c:148-154`):** `av_buffer_is_writable(buf)` checks `!(buf->buffer->flags & AV_BUFFER_FLAG_READONLY) && atomic_load(&buf->buffer->refcount) == 1`. While `acq_rel` on `fetch_sub` synchronizes-with prior reference releases once `refcount == 1` is observed, this invariant holds **only** under FFmpeg's undocumented ownership protocol that no external thread concurrently holds and clones/mutates that same `AVBufferRef *` or aliases the underlying `data` slice! In Rust, creating `&mut [u8]` solely from `av_buffer_is_writable` is **unsound** against hostile or buggy C callers that retain an alias to `buf->data` or share an `AVBufferRef *` pointer concurrently.
- **Comparison with `memorysafety/rav1d` (`2e7216c20ac2a75de204d6c8d7268b75a45959b4`):** `rav1d` solves this cleanly across two layers:
  1. `CBox<T>` and `CArc<T>` (`src/c_box.rs:15-190`, `src/c_arc.rs:1-145`) wrap opaque C-allocated or custom-freed buffers with `SendSyncNonNull<c_void>` cookies and `FnFree = unsafe extern "C" fn(ptr: *const u8, cookie: Option<SendSyncNonNull<c_void>>)`, guaranteeing thread-safe destruction semantics and pointer provenance without exposing mutable `&mut` aliases.
  2. `DisjointMut<T>` (`src/disjoint_mut.rs:34-95`) wraps slice payloads in `UnsafeCell<T>` (zero-cost `#[repr(transparent)]` in release builds, `L33`), checking disjoint region borrows at runtime under `cfg(debug_assertions)` and restricting `AsMutPtr::Target` to provenanceless pixel primitives (`L67-72`). For an FFmpeg C-ABI compatibility layer, decoded frames and reference buffers shared across threads or loaned to `AVBufferRef` should expose interior-mutable or handle-checked slice access (or copy-on-write isolation when external refcount `> 1` or untrusted custom allocators are present) rather than constructing raw `&mut [u8]` over externally visible C pointers.

### 4. `AVClass` Offset-0 Vtable, `AVOption` Pointer Reflection, and `AVDictionary` Ownership

`Basis: source`

FFmpeg's metadata and runtime configuration system couples struct layout tightly to dynamic byte-offset reflection:

- **`AVClass` header invariant (`libavutil/log.h:76-165`, `libavutil/log.c:465-475`):** Any struct passed to `av_log()`, `av_opt_set*()`, or `av_opt_get*()` must store `const AVClass *` at byte offset `0`. `av_vlog` dereferences `AVClass *avc = avcl ? *(AVClass **)avcl : NULL` (`log.c:467`) and, when `avc->version >= (50 << 16 | 15 << 8 | 2)`, reads `int` at `((uint8_t *)avcl) + avc->log_level_offset_offset` (`log.c:470-472`) and traverses parent contexts via `parent_log_context_offset` (`log.h:124`) and child contexts via `child_next` (`log.h:150`).
- **`AVOption` raw pointer mutation (`libavutil/opt.h:250-470`, `libavutil/opt.c:221,234-360,904-954,1311-1487`):** `AVOption` descriptors store an `int offset` (`opt.h:443`) computed via `offsetof(Struct, field)` (e.g., `libavcodec/options_table.h`). `av_opt_set*` and `av_opt_get*` locate the target field via `dst = ((uint8_t *)target_obj) + o->offset` (`opt.c:221,1317,1357,1487`) and directly read/write typed C values (`int`, `unsigned int`, `int64_t`, `uint64_t`, `float`, `double`, `AVRational`, `enum AVPixelFormat`, `enum AVSampleFormat`, `AVDictionary *`, heap strings via `av_strdup`/`av_free`).
- **Why pure Rust structs cannot directly host `AVOption`:** First, Rust does not allow `offsetof!`-driven unguarded pointer writes into fields of a live struct without violating `&mut` / `&` aliasing rules or bypassing enum/range validity invariants (e.g., writing arbitrary `int` values into a Rust `enum` with invalid discriminants is immediate UB!). Second, C callers expect to mutate public struct fields *either* directly via C field assignment (`avctx->bit_rate = 128000;`) *or* via `av_opt_set(avctx, "b", "128000", 0)`. Therefore, a pure Rust core must keep its idiomatic typed configuration structs separate from the C-ABI `AVCodecContext`/`AVFormatContext` structs: the C shim either (a) synchronizes dirty/public fields between the `#[repr(C)]` C shadow struct and the Rust config struct on boundary transitions (`avcodec_open2`, `avcodec_send_packet`, `avformat_open_input`), or (b) routes `av_opt_*` calls through a declarative Rust property-descriptor table that validates invariants and updates both the C shadow struct and the Rust core config atomically.
- **`AVDictionary` ownership and allocator traps (`libavutil/dict.h:74-200`, `libavutil/dict.c:32-178`):**
  - `AVDictionary` is genuinely opaque (`dict.h:95`), initialized by caller as `AVDictionary *d = NULL`, and dynamically allocated on first `av_dict_set(&d, ...)` (`dict.c:122-123`). Deleting or overwriting an entry swaps the last entry (`*tag = m->elems[--m->count]`, `dict.c:146`), so iteration order is unstable under mutation.
  - Flags `AV_DICT_DONT_STRDUP_KEY` (`4`) and `AV_DICT_DONT_STRDUP_VAL` (`8`) transfer ownership of caller-allocated C strings into `AVDictionary`. Crucially, `av_dict_set` calls `av_free(copy_key)` and `av_free(copy_value)` on *all* error paths and no-op branches—including `key == NULL` (`AVERROR(EINVAL)`, `dict.c:99-101,170-177`), `AV_DICT_DONT_OVERWRITE` (`L128-131`), and `AV_DICT_DEDUP` (`L115-118`). Passing a Rust `CString::into_raw()` pointer (allocated by Rust's global allocator) with `AV_DICT_DONT_STRDUP_*` causes allocator-mismatch UB when FFmpeg frees it with `av_free` (`posix_memalign`/`free` vs `jemalloc`/system allocator), and passing a C string allocated with `av_malloc` works *only* if `av_free` shares the same underlying `free` domain. A Rust `av_dict_set` shim must clearly segregate `av_malloc`-allocated C allocations or intercept `AV_DICT_DONT_STRDUP_*` safely.

### 5. Callback Contracts, Re-Entrancy, `va_list` Variadics, and Unwind Safety

`Basis: source + normative`

FFmpeg embeds user-supplied C function pointers inside contexts and global state. Wrapping a clean Rust core beneath this callback ABI introduces five concrete soundness hazards:

| Callback / Hook | Upstream Location | Upstream Validation / Serialization | Hazards from Buggy or Hostile C Callers | Required Rust FFI Shim Obligation |
| :--- | :--- | :--- | :--- | :--- |
| `AVCodecContext.get_buffer2` | `avcodec.h:1223`, `decode.c:1719-1738,1861-1865`, `pthread_frame.c:1049-1052` | Serialized per context by `buffer_mutex` under `FF_THREAD_FRAME`; `validate_avframe_allocation` checks only non-NULL `data[i]` and zeroes unused `data[]`. | Returns unaligned `data[i]`, insufficient `linesize[i]` or `linesize < 0` with `data[i]` pointing before allocation start, overlapping/aliasing planes, missing `buf[i]` backing, uninitialized/tainted bytes, or re-entrantly mutates `avctx` during callback. | Validate `buf[i]` bounds against `height * abs(linesize[i]) + tail_padding`, check alignment (`16/32/64`) or copy/realign, reject overlapping mutable plane slices, release/re-lock context guard around callback to prevent deadlock/re-entrancy UB. |
| `AVCodecContext.get_format` | `avcodec.h:777`, `decode.c:1248-1305` | Invoked synchronously mid-decode when pixel format list changes; checks return is in offered list or `AV_PIX_FMT_NONE`. | Re-entrantly calls `avcodec_flush_buffers`/`avcodec_close`, mutates `hw_frames_ctx` inconsistently, or returns format absent from `fmt[]`. | Snapshot state before invoking callback, re-validate `AVPixelFormat` membership in `fmt[]`, reject re-entrant context close/mutation via re-entrancy token. |
| `AVCodecContext.execute` / `execute2` | `avcodec.h:1619,1638`, `pthread_slice.c:81-152` | Passes `void *arg2` and `count` jobs to user thread pool; requires `threadnr < c->thread_count` distinct for concurrent workers. | User pool runs jobs concurrently with non-distinct `threadnr`, skips jobs, invokes `func` past `count`, or mutates `ret[]` out-of-bounds. | Pass a `Send + Sync` job descriptor holding atomic completion bitmap + per-job slot bounds; verify `0 <= jobnr < count` and atomic single-claim per job before executing Rust slice worker. |
| `AVIOContext` (`read_packet`, `write_packet`, `seek`) | `avio.h:234-235,416-417`, `aviobuf.c:501-570` | `read_packet_wrapper` calls `s->read_packet(s->opaque, buf, size)` and asserts `ret \|\| s->max_packet_size`. | Returns `ret > size` (buffer overflow / uninitialized tail exposure!), returns `0` without `AVERROR_EOF` (infinite loop), or mutates `s->buffer` / `s->buf_ptr` inside callback. | Clamp/check `0 < ret <= size` (`AVERROR_BUG` / `AVERROR(EIO)` if `ret > size`), treat `ret == 0` gracefully or per EOF policy, pass isolated staging slice rather than raw internal Rust Vec buffer. |
| `av_log` / `av_vlog` / `av_log_set_callback` | `log.h:268,307,337`, `log.c:446-500` | `av_log_callback` is `_Atomic` stored with `memory_order_relaxed`; internal `mutex` protects only `av_log_default_callback`, *not* custom callbacks. | Concurrent worker threads race inside non-thread-safe user callback; C-variadic format string mismatch or invalid `%s` pointer; `va_list` ABI difference across platforms. | Export `extern "C" fn av_log(..., ...)` via a tiny C trampoline calling `av_vlog` (or Edition 2024 `VaList` on supported targets) and guard custom callback dispatch or document `Send+Sync` requirement; never expose Rust `format_args!` across `va_list`. |

**Unwind safety across C-ABI boundaries (`Basis: normative`, `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/items/functions.md:238-263`, `src/items/external-blocks.md:104-116,218-236`):**
- Rust `extern "C"` functions are *non-unwinding* ABI boundaries: if compiled with `panic=unwind`, a Rust panic attempting to cross an `extern "C"` boundary aborts the process (and whether `Drop` runs before abort is explicitly unspecified, `functions.md:261`), whereas a foreign exception or `longjmp` (forced unwinding) crossing a non-unwinding `"C"` boundary is **Undefined Behavior** (`functions.md:256-259`).
- Therefore: (1) every exported `extern "C"` compatibility symbol should wrap its body in `std::panic::catch_unwind` (returning `AVERROR_BUG` if a panic ever escapes, though the core itself targets panic-freedom), and (2) calling user-supplied C callbacks (`get_buffer2`, `read_packet`, `av_log_callback`) should use `extern "C-unwind"` declarations if C++ callers might throw exceptions through callbacks—while recognizing that C `setjmp`/`longjmp` (used in `libjpeg` or legacy C error handlers) across Rust stack frames remains **undefined behavior** regardless of `-unwind` ABI because it skips Rust destructors and borrows (`functions.md:251`).

### 6. `AVERROR` Error Space, `FFERRTAG` Sign Hazards, and `NonZeroI32` Representation

`Basis: source + execution`

`libavutil/error.h:41-84` defines FFmpeg's negative error return convention:
- **POSIX errno negation:** On Unix-like systems where `EDOM > 0`, `AVERROR(e)` expands to `(-(e))`; on Haiku/BeOS where POSIX `errno` values are already negative, `AVERROR(e)` expands to `(e)` (`error.h:41-47`). Crucially, `EAGAIN` is `11` on Linux x86_64 (`AVERROR(EAGAIN) == -11`) but `35` on macOS/FreeBSD (`AVERROR(EAGAIN) == -35`), so a Rust FFI crate must derive POSIX error codes from `libc::E*` at compile time rather than hardcoding Linux integers.
- **FourCC negative tags (`FFERRTAG`):** `FFERRTAG(a, b, c, d)` is defined as `(-(int)MKTAG(a, b, c, d))` (`error.h:49`), where `MKTAG` packs bytes little-endian (`a | (b<<8) | (c<<16) | ((unsigned)d<<24)`). Notably, many error tags pass `0xF8` as the first byte (e.g., `AVERROR_BSF_NOT_FOUND = FFERRTAG(0xF8,'B','S','F')`), making `(int)MKTAG(...)` positive (`0x465342f8`) and its negation negative (`-1179861752`).
- **Measured exact values (`abi_probe` execution, `Basis: execution`):** Verified identically between `gcc 15.2.0` (`-O2`) and `rustc 1.98.0-nightly` (`const fn fferrtag` using `.wrapping_neg()`):
  - `AVERROR_EOF` (`FFERRTAG('E','O','F',' ')`): `-541478725` (`0xdfb9b0bb`)
  - `AVERROR_INVALIDDATA` (`FFERRTAG('I','N','D','A')`): `-1094995529`
  - `AVERROR_BSF_NOT_FOUND` (`FFERRTAG(0xF8,'B','S','F')`): `-1179861752`
  - `AVERROR(EAGAIN)` on `x86_64-linux-gnu`: `-11`; `AVERROR(ENOMEM)`: `-12`.
- **Rust representation:** Every `AVERROR` code is strictly negative (`< 0`), enabling `Result<NonNegativeCInt, NonZeroI32>` (or `NonNegativeI32` + `AvError(NonZeroI32)`) in Rust with niche optimization, converting cleanly to `c_int` at the C boundary without ambiguity over `0` vs `< 0` vs `>= 0` (many FFmpeg functions return `>= 0` byte counts or flags on success and `< 0` on error).

### 7. Architectural Comparison & Verification Priority Stack Implications

`Basis: derived + execution`

Evaluating a **pure Rust core + thin quarantining C-ABI shim** against a **C-struct-native Rust core** along the four-tier verification priority stack exposes sharp trade-offs:

| Criterion | Pure Rust Core + Thin C-ABI Compatibility Shim | C-Struct-Native Rust Core (`#[repr(C)]` Everywhere) |
| :--- | :--- | :--- |
| **1. UB-freedom** | High: `unsafe` confined to thin shim (~5–10% of codebase); core operates on safe `&[u8]`, `&mut [u8]`, enums, and `DisjointMut`-style bounds. | Low/Fragile: raw pointers, `offsetof` mutation (`AVOption`), self-referential `AVFrame.extended_data`, and aliasing `AVBufferRef` leak throughout decoders/filters. |
| **2. Panic-freedom** | High: explicit `checked_*` slice indexing and typed `Result<T, AvError>` inside core; shim wraps entrypoints in `catch_unwind` as defense-in-depth. | Harder: C-mirror integer fields (`int width`, `int linesize[]`) require repeated signed-to-`usize` validation inside every hot inner loop. |
| **3. Behavioral Equivalence** | High: identical Rust decode/demux semantics whether called from pure Rust API or C ABI; padding fallback preserves exact bytes even for unpadded C callers. | Same functional behavior, but higher risk of optimization-sensitive UB divergence between debug and release builds. |
| **4. Ergonomics & Overhead** | Idiomatic Rust crate API (`Decoder::send_packet(&[u8])`) with zero C pointer boilerplate; shim validation overhead measured at **~1.10 ns/call** (`3.888 ns` vs `2.788 ns`) on AMD EPYC 7B12 (`Basis: execution`). | Forces Rust callers to manage `AVFrame`/`AVPacket`/`AVDictionary` raw pointers, manual `av_frame_unref`, and C-null-terminated strings. |

**Measured micro-probe overhead (`Basis: execution`, `abi_probe_v2.rs`, AMD EPYC 7B12, `rustc 1.98.0-nightly -C opt-level=3`, 50,000,000 iterations):**
- Direct `#[inline(never)]` Rust slice kernel (`direct_rust_core`): `139.393 ms` total (**`2.788 ns/call`**).
- `extern "C"` boundary shim validating `NULL`, `extended_data`, positive `width`/`height`/`linesize`, `32`-byte alignment, and `checked_mul` byte length before calling `direct_rust_core` (`rust_ffi_no_catch_shim`): `181.429 ms` total (**`3.629 ns/call`**, `+0.841 ns/call`).
- Same `extern "C"` boundary shim plus `std::panic::catch_unwind` (`rust_ffi_validate_shim`): `194.410 ms` total (**`3.888 ns/call`**, `+1.100 ns/call` over direct Rust).

Even at 1,000 frame/packet boundary crossings per second, `~1.1 ns/call` adds `~1.1 microseconds/s` (`0.00011%` CPU), confirming that full boundary validation + unwind isolation is negligible compared to codec/filter computation—while keeping the core free of raw C ABI layout coupling. Note that `AVOption` shadow-struct reflection and copying unpadded legacy `AVPacket` payloads scale with field/byte count and remain outside this constant per-call frame check.

## Boundaries

- **Hardware-acceleration context internals (`not examined`):** Specific opaque native handle contracts inside `AVHWDeviceContext`, `AVHWFramesContext`, `AVVAAPIDisplay`, `AVVulkanDeviceContext`, and `AVD3D11VAContext` (`libavutil/hwcontext_*.h`) were not audited at the field level in this study.
- **Full `rustc` + `FFmpeg` linked ABI test (`not examined`):** No full `libavcodec.so` / `libavformat.so` binary was compiled or linked locally via `clang`/`bindgen`; layout and error-tag probes used a minimal standalone `FakeAVFrame` + `FFERRTAG` C/Rust harness (`abi_probe.c` / `abi_probe_v2.rs`).
- **Windows LLP64, `stdcall`, and 32-bit targets (`not examined`):** All executed probes ran on `x86_64-unknown-linux-gnu` (System V AMD64 ABI, LP64, `long` = 8 bytes). Enum underlying integer width (`c_int` vs `c_uint`) and `va_list` register-save-area differences on Windows x64, `aarch64`, and `i686` were verified by specification reading (`rust-lang/reference`) rather than local execution.
- **`longjmp` unwinding through Rust frames (`known not to apply` / `unsupported`):** Switching FFI declarations from `extern "C"` to `extern "C-unwind"` makes C++ exceptions safe to propagate across compatible targets, but **does not** make C `setjmp`/`longjmp` across Rust stack frames sound (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/items/functions.md:251-259`).
- **Static zero-copy guarantees for unowned `AVPacket` pointers (`unsupported`):** When a C caller supplies an `AVPacket` with `pkt->buf == NULL`, the C ABI provides no allocation size beyond `pkt->size`; a Rust shim cannot safely construct a `&[u8; pkt->size + 64]` slice without copying unless the caller guarantees `AV_INPUT_BUFFER_PADDING_SIZE` allocation.

## Evidence

### Primary Upstream Repositories & Line Citations

1. **`FFmpeg/FFmpeg` at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (observed `2026-11-20`):**
   - Symbol version scripts & major versions: `libavutil/libavutil.v`, `libavcodec/libavcodec.v`, `libavformat/libavformat.v`, `libavfilter/libavfilter.v`, `libswscale/libswscale.v`, `libswresample/libswresample.v`, `libavdevice/libavdevice.v`; `libavutil/version.h:81,108-112`, `libavcodec/version_major.h:26`, `libavformat/version_major.h:26`, `libavfilter/version_major.h:26`, `libswscale/version_major.h:26`, `libswresample/version_major.h:26`, `libavdevice/version_major.h:26`; `configure:2426-2427,3020-3021,5712,7961`.
   - Allocator, alignment & padding: `libavutil/mem.c:66` (`ALIGN`), `84-160` (Windows ASan wrapper), `164-173` (`-Wl,-Bsymbolic` note, `max_alloc_size = INT_MAX`), `193-215` (`av_malloc`), `245-246` (`av_malloc(0)`), `608` (`av_realloc`); `libavcodec/defs.h:40` (`AV_INPUT_BUFFER_PADDING_SIZE 64`).
   - Semi-opaque structs & container-of embedding: `libavcodec/avcodec.h:441` (`sizeof(AVCodecContext)` excluded), `748`, `777`, `1165-1223`, `1619`, `1638`; `libavcodec/avcodec_internal.h:33-45` (`FFCodecContext`); `libavcodec/options.c:149-160` (`avcodec_alloc_context3`); `libavcodec/packet.h:578-635` (`AVPacket`); `libavutil/frame.h:331,473,479-675,815-860` (`AVFrame`, `extended_data`, `private_ref`); `libavformat/avformat.h:768,974,1325,1394,1403-1465,2029-2039`; `libavformat/avio.h:153,160-295,402-417`.
   - Reference counting & buffer pool: `libavutil/buffer.h:70-115`; `libavutil/buffer_internal.h:35-98`; `libavutil/buffer.c:30-54,104-154,184-232`.
   - `AVClass`, `AVOption`, `AVDictionary`, `AVERROR`: `libavutil/log.h:76-165,268,307,337`; `libavutil/log.c:49,385-500`; `libavutil/opt.h:250-310,428-470`; `libavutil/opt.c:221,234-360,904-954,1311-1487`; `libavutil/dict.h:74-200`; `libavutil/dict.c:32-178`; `libavutil/error.h:41-123`.
   - Callback checks & threading: `libavcodec/decode.c:1248-1305,1656-1885` (`validate_avframe_allocation`, `ff_get_buffer`, `ff_get_format`); `libavcodec/pthread_frame.c:1034-1084` (`buffer_mutex` serialization); `libavcodec/pthread_slice.c:58-152` (`execute`, `execute2`); `libavformat/aviobuf.c:501-570` (`read_packet_wrapper`, `fill_buffer`).
2. **`memorysafety/rav1d` at `2e7216c20ac2a75de204d6c8d7268b75a45959b4`:**
   - `src/c_box.rs:15-190`, `src/c_arc.rs:1-145`, `src/disjoint_mut.rs:32-95`, `src/ffi_safe.rs:10-57`, `src/wrap_fn_ptr.rs:41-100`.
3. **`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:**
   - `src/items/external-blocks.md:78-116,215-236`, `src/items/functions.md:86,178-263`, `src/type-layout.md`.

### Reproducible Micro-Probes (`Basis: execution`, `2026-11-20`)

Executed on `x86_64-unknown-linux-gnu` (`AMD EPYC 7B12`, `gcc (Debian 15.2.0-14) 15.2.0`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`):

1. **C/Rust Layout, Error-Tag, and Self-Referential Move Probe (`abi_probe.c` + `abi_probe.rs`, `gcc -O2 -c` + `rustc -O --edition 2024`):**
   - Observed output:
     ```text
     sizeof_frame: C=128 Rust=128 offsetof_ext_data: C=96 Rust=96
     AVERROR_EOF: C=-541478725 Rust=-541478725 (0xdfb9b0bb) | INVALIDDATA: C=-1094995529 Rust=-1094995529 | BSF_NOT_FOUND: C=-1179861752 Rust=-1179861752 | EAGAIN=-11 ENOMEM=-12
     self_ptr_move_hazard: boxed_data=0x563e8195cd50 after_move_ext=0x563e8195cd50 after_move_data=0x7ffc5b421860 dangling=true
     ```
2. **FFI Shim Validation + `catch_unwind` Overhead Benchmark (`abi_probe_v2.rs`, `rustc -C opt-level=3 --edition 2024`, 50,000,000 iterations with `std::hint::black_box`):**
   - Minimal reproducer structure: `#[inline(never)]` `direct_rust_core(&[u8], usize, usize, usize) -> i32` vs `extern "C"` shims validating `FakeAVFrame` (`data[0] != NULL`, `extended_data != NULL`, `linesize[0] > 0`, `width > 0`, `height > 0`, `(data[0] as usize & 31) == 0`, `linesize.checked_mul(height)`), with and without `std::panic::catch_unwind`:
     ```text
     bench 50000000 iters (-C opt-level=3): direct_rust=139.393 ms (2.788 ns/call), ffi_no_catch=181.429 ms (3.629 ns/call), ffi_with_catch_unwind=194.410 ms (3.888 ns/call)
     ```

## Revalidation

1. **Upstream ABI drift check:** Diff `libav*/libav*.v`, `libav*/version_major.h`, `libavutil/version.h`, `libavcodec/avcodec.h` (`AVCodecContext`), `libavutil/frame.h` (`AVFrame`), `libavcodec/packet.h` (`AVPacket`), `libavcodec/defs.h` (`AV_INPUT_BUFFER_PADDING_SIZE`), and `libavutil/mem.c` (`ALIGN`) against a newer `FFmpeg/FFmpeg` commit to detect major version bumps, removed `FF_API_*` guards, or changed padding/alignment constants.
2. **Callback validation drift check:** Inspect `validate_avframe_allocation` (`libavcodec/decode.c`) and `read_packet_wrapper` (`libavformat/aviobuf.c`) for newly added invariants or assertions.
3. **FFI overhead & layout probe revalidation:** Recompile and run the standalone `abi_probe.c` / `abi_probe_v2.rs` harness against updated `rustc` / `gcc` releases or target triples (`aarch64-unknown-linux-gnu`, `x86_64-pc-windows-msvc`) to verify `FFERRTAG` / `AVERROR(errno)` parity, `#[repr(C)]` struct offsets, and boundary call latency.
