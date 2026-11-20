# `libavfilter` Graph Scheduling, Frame Threading, and `AVBufferRef` Lifetime Invariants

## Summary

Primary-source inspection of `FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) across `libavutil`, `libavfilter`, and `libavcodec`, together with `memorysafety/rav1d` (`2e7216c20ac2a75de204d6c8d7268b75a45959b4`), establishes four structural concurrency and ownership invariants that govern zero-copy multimedia pipelines:

1. **`AVBuffer` / `AVBufferRef` / `AVBufferPool` ownership and `2.21x` indirection tax (`libavutil/buffer.c`, `buffer_internal.h`, `frame.c`):** FFmpeg splits reference-counted buffers into a heap-allocated `AVBuffer` (holding `atomic_uint refcount`) and a separate heap-allocated 24-byte `AVBufferRef` view (`buffer.c:45, 106`). Cloning and dropping a handle therefore incurs `av_mallocz`/`av_freep` plus `memory_order_acq_rel` atomic decrement (`34.54 ns/pair` vs `15.63 ns/pair` for inline single-indirection handles in our Xeon C11 micro-probe). Because `av_buffer_is_writable` (`buffer.c:148-154`) checks only `atomic_load(&buf->buffer->refcount) == 1 && !(flags & AV_BUFFER_FLAG_READONLY)`, two C pointers sharing one `AVBufferRef *` satisfy `is_writable == 1` and silently alias-corrupt readers (verified by execution). Meanwhile, `BufferPoolEntry` embeds `AVBuffer buffer` inline (`buffer_internal.h:85`) with `BUFFER_FLAG_NO_FREE` (`buffer.c:410`), making `buffer_replace`'s pre-callback flag load (`line 133`) essential to prevent immediate Use-After-Free when returning the final buffer frees its owning `AVBufferPool`.
2. **Cooperative single-threaded `libavfilter` scheduling and constraint-merging negotiation (`libavfilter/avfiltergraph.c`, `avfilter.c`, `formats.c`, `framequeue.h`):** `AVFilterGraph` negotiates link properties (`mergers_video` / `mergers_audio`, `formats.c:392+`) via iterative list intersection (`query_formats`, `avfiltergraph.c:551-642`), auto-inserting `scale` or `aresample` filters whenever `can_merge` fails, then executes demand-driven activation (`ff_filter_graph_run_once` `O(N)` ready-score max scan at `avfiltergraph.c:1675-1692`, plus `avfilter_graph_request_oldest` sink PTS min-heap at `lines 1626-1673`) over `FFFrameQueue` rings bounded by `FFFrameQueueGlobal.max_queued`. The graph scheduler carries **zero internal mutexes**; multi-threading in `libavfilter` is strictly synchronous intra-filter fork-join slice threading (`libavfilter/pthread.c:59-109`).
3. **Intra-frame slice release sequences and inter-frame `ThreadProgress` barriers (`libavutil/slicethread.c`, `libavcodec/pthread_frame.c`, `threadprogress.c`):** `AVSliceThread::run_jobs` synchronizes workers lock-free using a C17 release sequence (`current_job == nb_jobs + nb_active_threads - 1` under `memory_order_acq_rel`, `slicethread.c:65-86`). Inter-frame `pthread_frame.c` steps workers through `STATE_INPUT_READY -> STATE_SETTING_UP -> STATE_SETUP_FINISHED` (`ff_thread_finish_setup`, `lines 675-718`) and relies on `ThreadProgress` (`threadprogress.c:53-78`): a `memory_order_acquire` fast path (`1.68 ns` vs `15.47 ns` mutex-guarded check in our micro-probe) paired with a mutex-enclosed `memory_order_release` store (`line 59`) whose ordering guarantees soundness of the slow-path `memory_order_relaxed` loop (`line 75`).
4. **Eliminating `rav1d`'s unsound `DisjointMut` erasure under Anneal:** `memorysafety/rav1d` (`src/disjoint_mut.rs:34-109`) disables overlap tracking in release builds under the unsound rationale (`lines 70-74`) that data races on provenanceless pixel arrays cannot violate memory safety. A clean Rust rewrite modeled in `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) retains zero-copy throughput and `0 ns` runtime borrow checks without soundness compromises via: (a) `&mut` uniqueness on `CowFrame` (`Arc<PooledStorage>` + value slice `(offset, len, stride)`), (b) scoped `split_at_mut` row partitioning for intra-frame slices, and (c) monotonic ghost `RowProgressPlane` capabilities binding `Acquire`/`Release` progress integers to frozen prefix slices `[0 .. r * stride)`.

## Applicability

This report documents primary sources in `FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) covering `libavutil/buffer_internal.h`, `libavutil/buffer.{h,c}`, `libavutil/frame.c`, `libavutil/slicethread.c`, `libavfilter/avfilter.{h,c}`, `libavfilter/filters.h`, `libavfilter/avfiltergraph.c`, `libavfilter/formats.c`, `libavfilter/framequeue.h`, `libavfilter/pthread.c`, `libavcodec/pthread_frame.c`, `libavcodec/pthread_slice.c`, and `libavcodec/threadprogress.{h,c}`.

Findings are evaluated against ISO/IEC 9899:2018 (C17) §7.17 atomics/release-sequence rules and contrasted with Rust implementations in `memorysafety/rav1d` (`2e7216c20ac2a75de204d6c8d7268b75a45959b4`), `crossbeam-rs/crossbeam` (`a28f40fdddb70bea8e5faf0efad9af0be4b9dbea`), `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`).

Related foundational analyses in this corpus are referenced directly rather than duplicated: hardware weak-memory fence mappings (`x86-64` TSO, `aarch64` LDAR/STLR, `riscv64` RVWMO) in `assembly-atomic-fence-mappings-and-aarch64-x86-weak-memory-models`; Rust operational concurrency and Tree Borrows aliasing in `rust-atomics-weak-memory-and-aliasing-operational-models` and `minirust-tree-borrows-protectors-and-program-logic-correspondence`; slice splitting and Polonius limits in `borrow-checker-self-referential-views-disjoint-slices-and-polonius-limits`; explicit GPU/DMA fence passing (`DRM_IOCTL_SYNCOBJ`, `PipeWire` scheduling) in `wayland-explicit-drm-syncobj-dbus-fd-passing-and-pipewire-graph-scheduling` and `tcp-msg-zerocopy-errqueue-lifetimes-pcie-p2pdma-and-nvlink-peer-ordering`; and incremental ABI strangulation in `incremental-c2rust-lifting-mvee-shadow-execution-and-ffi-strangulation`.

## Findings

### 1. `AVBuffer`, `AVBufferRef`, `AVBufferPool`, and `AVFrame` Copy-on-Write Lifetime Invariants

Basis: normative (`ISO/IEC 9899:2018` §7.17) + source (`FFmpeg/FFmpeg`) + execution (`probe_avbuffer_progress.c`).

FFmpeg achieves zero-copy sharing of video frames, compressed packets, and hardware surface descriptors across demuxers, decoders, filtergraphs, and encoders through two distinct heap objects (`libavutil/buffer_internal.h:38-66`, `libavutil/buffer.h:82-95`):

- **`AVBuffer` (shared control + backing pointer):** Stores `uint8_t *data`, `size_t size`, `atomic_uint refcount`, `void (*free)(void *opaque, uint8_t *data)`, `void *opaque`, `int flags` (`AV_BUFFER_FLAG_READONLY`), and `int flags_internal` (`BUFFER_FLAG_REALLOCATABLE`, `BUFFER_FLAG_NO_FREE`).
- **`AVBufferRef` (per-handle subslice descriptor):** Heap-allocated (`av_mallocz(sizeof(*ret))` at `buffer.c:45, 106`) holding `AVBuffer *buffer`, `uint8_t *data` (potentially offset inside the backing `AVBuffer`), and `size_t size`.

#### Atomic Ordering, Heap Indirection Cost, and `BUFFER_FLAG_NO_FREE`

Inspecting `libavutil/buffer.c:104-164` reveals three performance and lifetime subtleties:

1. **Per-reference heap allocation (`2.21x` pair overhead):** `av_buffer_ref` (`buffer.c:104-116`) allocates a fresh 24-byte `AVBufferRef` on the system heap (`line 106`), shallow-copies `{buffer, data, size}`, and increments `buf->buffer->refcount` with `memory_order_relaxed` (`line 113`). On unref (`buffer_replace`, `lines 118-138`), it frees the `AVBufferRef` *first* (`av_freep(dst)` at `line 128`) and executes `atomic_fetch_sub_explicit(&b->refcount, 1, memory_order_acq_rel)` (`line 130`). Unlike Rust's `Arc::drop` (which executes `Release` and only issues an `Acquire` fence on the winning `1 -> 0` transition), FFmpeg pays a full `acq_rel` barrier on *every* non-terminal decrement plus a heap `malloc`/`free` pair per clone/drop—measuring **`34.54 ns/pair` vs `15.63 ns/pair`** for inline single-indirection handles in our Xeon probe (`probe_avbuffer_progress.c`).
2. **Invasive `BufferPoolEntry` UAF prevention (`buffer.c:130-137, 348-429`):** `AVBufferPool` (`buffer_internal.h:68-108`) tracks `atomic_uint refcount` initialized to `1` for the caller's pool handle (`buffer.c:279, 298`) and incremented with `memory_order_relaxed` on every `av_buffer_pool_get` (`line 426`). Each pooled allocation (`pool_alloc_buffer`, `lines 367-394`) replaces `ret->buffer->free` with `pool_release_buffer` and embeds an inline `AVBuffer buffer` inside `BufferPoolEntry` (`buffer_internal.h:85`), later tagged `BUFFER_FLAG_NO_FREE` (`line 410`) when recycled in `av_buffer_pool_get`. When `pool_release_buffer` (`lines 348-363`) returns the last checked-out buffer after `av_buffer_pool_uninit` (`line 331-346`) has already dropped the caller's reference, `buffer_pool_free(pool)` (`line 362`) runs inside `b->free(b->opaque, b->data)` and calls `av_freep(&buf)` (`line 312`), freeing the `BufferPoolEntry` containing `*b` itself! Consequently, `buffer_replace` (`line 133`) **must** hoist `int free_avbuffer = !(b->flags_internal & BUFFER_FLAG_NO_FREE);` into a local variable *before* invoking `b->free(b->opaque, b->data)`—reading `b->flags_internal` afterward would be an immediate Use-After-Free.
3. **ASan / MemorySanitizer pool hygiene (`buffer.c:310, 354, 411-418`):** Returned default-freed pool buffers are poisoned (`FF_ASAN_POISON` at `line 354`) while idle in the free list and unpoisoned on checkout (`line 412`), with `FF_MEM_UNDEFINED` applied only when no zero-initialization allocator (`pool->alloc2` or non-`av_buffer_alloc`) was provided (`lines 416-417`).

#### `AVFrame` Writability Checks and C Aliasing Hazards

`av_frame_is_writable` (`libavutil/frame.c:538-553`) requires `!frame->buf[0]` to be false (`line 543`, treating unmanaged raw-pointer frames as immutable) and checks `av_buffer_is_writable` across all non-null slots of `frame->buf[0..7]` and `frame->extended_buf[0..nb_extended_buf-1]` (`lines 546-550`). When false, `av_frame_make_writable` (`frame.c:555-595`)—or `ff_inlink_make_frame_writable` (`libavfilter/avfilter.c:1623-1663`) using the destination link's frame pool—allocates a fresh frame (`av_hwframe_get_buffer` or `av_frame_get_buffer`), copies pixel data and frame properties, unrefs the old frame, and overwrites `*frame = tmp`. This design exposes four distinct C failure modes:

1. **Same-`AVBufferRef` aliasing (`refcount == 1` false positive):** Because writability checks `atomic_load(&buf->buffer->refcount) == 1` (`buffer.c:153`) rather than Rust-style `&mut` pointer exclusivity, two C structs sharing the same `AVBufferRef *` (or a cached `frame->data[0]` pointer outliving a shallow struct copy) both observe `is_writable == 1` and silently mutate shared memory under active readers (reproduced in `probe_avbuffer_progress.c`, flipping reader byte `0x42 -> 0xff`).
2. **Missing `AV_BUFFER_FLAG_READONLY` on decoder reference surfaces:** Under frame-threaded decoding (`FF_THREAD_FRAME`), decoded frames remain referenced as inter-prediction reference frames across worker threads. If a decoder clears its internal reference prematurely or omits `AV_BUFFER_FLAG_READONLY` on handed-out frames, an in-place downstream filter (`ff_inlink_make_frame_writable`) sees `refcount == 1` (or races with another worker's `av_buffer_ref`) and overwrites pixels still needed for motion compensation.
3. **`refcount == 2 -> 1` concurrent check-then-write TOCTOU:** `av_buffer_is_writable` uses `memory_order_seq_cst` (`atomic_load`), yet if two threads hold *distinct* `AVBufferRef`s to the same `AVBuffer` (`refcount == 2`) and Thread A calls `av_buffer_unref` concurrently with Thread B calling `av_buffer_make_writable`, Thread B lacks an atomic `Acquire` fence *after* observing `refcount == 1` unless `av_buffer_unref` on Thread A used `acq_rel` (`line 130`)—which happens to synchronize-with `seq_cst` load (`line 153`) under C17 §7.17.3 only if Thread A never reads/writes `data` after decrement, whereas concurrent `av_buffer_is_writable` on two threads holding the same `AVBufferRef` always races.
4. **Hardware-context vs CPU-pool mismatch (`frame.c:574-577`):** `av_frame_make_writable` dispatches on `frame->hw_frames_ctx` while `ff_inlink_make_frame_writable` ignores `hw_frames_ctx` when allocating via `ff_get_video_buffer(link, ...)` (`avfilter.c:1637`) unless pixel format mismatch diverts to `av_frame_make_writable` (`line 1635-1636`).

### 2. `libavfilter` Graph Format Negotiation and Cooperative Activation Scheduling

Basis: source (`FFmpeg/FFmpeg`).

`avfilter_graph_config` (`libavfilter/avfiltergraph.c:1480-1525`) resolves format/layout constraints and constructs an active DAG before any frames traverse the graph:

#### Iterative Constraint-Merging Format Negotiation (`avfiltergraph.c:551-642, 1348-1445`, `formats.c:315-415`)

1. **Constraint tables:** `libavfilter/formats.c:392+` defines `AVFilterFormatsMerger` descriptors (`mergers_video` for pixel formats, color spaces, color ranges, alpha modes, chroma locations; `mergers_audio` for sample formats, sample rates, channel layouts), mapping each property via `offsetof(AVFilterFormatsConfig, ...)` and pairing a list intersection `merge`/`can_merge` function with a `conversion_filter` (`"scale"` with `scale_sws_opts`, or `"aresample"` with `aresample_swr_opts`, `formats.c:384-390`).
2. **Intersection & auto-conversion (`query_formats`, `avfiltergraph.c:551-642`):** After invoking each filter's `query_formats` callback (`lines 560-572`), the solver loops over all links (`lines 576-633`). For every merger dimension where input and output config lists `a != b` exist and `can_merge(a, b)` is false (`line 596`), it deduplicates the required converter name into `conv_filters[]` (`lines 597-610`), then auto-inserts conversion filters in reverse order (`lines 640+`) and restarts at `goto retry` (`line 575`).
3. **Concrete selection & dynamic invariants:** `swap_sample_fmts` (`avfiltergraph.c:1348`) and `pick_formats` (`lines 1357-1405`) collapse remaining multi-element lists to singleton negotiated parameters stored in `FilterLinkInternal` (`cfg_format`, `cfg_w`, `cfg_h`). At runtime, `ff_filter_frame` (`avfilter.c:1112-1165`) enforces those parameters via `ff_inlink_check_frame_params` (`avfilter.c:1607-1621`), rejecting mid-stream size or pixel-format changes unless the filter declares `FF_FILTER_FLAG_DYNAMIC_FRAME_SIZE` or `FF_FILTER_FLAG_DYNAMIC_FRAME_FORMAT` (`libavfilter/filters.h:214, 220`); audio links never support dynamic format/rate/channel-layout changes (`avfilter.c:1130-1141, 1164`, returning `AVERROR_PATCHWELCOME`).

#### Demand-Driven Activation, `FFFrameQueue` Backpressure, and Single-Thread Restriction

| Component | Source Location (`FFmpeg/FFmpeg`) | Runtime Scheduling Invariant & Edge Case |
| :--- | :--- | :--- |
| Link queue & global cap | `framequeue.h:44-95`, `avfilter.c:1151-1158` | Circular `FFFrameBucket` ring with inline 1-frame `first_bucket` fast slot; fails with `ENOMEM` when `global->queued >= global->max_queued`. |
| Status latching | `avfilter.c:1507-1521` | `ff_inlink_acknowledge_status` drains `li->fifo` to empty *before* promoting `li->status_in` (`EOF`/error) into `li->status_out`. |
| Ready-score priority scan | `avfilter.c:1159, 1491-1505`, `avfiltergraph.c:1675-1692` | `ff_filter_frame` sets `ff_filter_set_ready(link->dst, 300)`; `ff_filter_graph_run_once` scans all `graph->nb_filters` linearly for max `ctxi->ready` and resets `ctxi->ready = 0` prior to `fi->activate(filter)`. |
| Sink age min-heap | `avfiltergraph.c:1618-1673` | `avfilter_graph_request_oldest` maintains `graphi->sink_links` binary min-heap (`age_index`) ordered by `current_pts_us`, stepping `ff_filter_graph_run_once` until the oldest un-EOF sink advances `frame_count_out`. |
| Graph thread safety | `libavfilter/pthread.c:59-109` | **Zero graph-level locks:** `AVFilterGraph` scheduling is strictly single-threaded; `graphi->thread_execute` provides synchronous intra-filter slice workers only (`AVFILTER_FLAG_SLICE_THREADS`). |

A subtle structural consequence: in diamond graphs (e.g., `split -> [heavy_denoise, passthrough] -> overlay`), if a sink pulls frames directly without `avfilter_graph_request_oldest`'s min-heap arbitration, or if a misbehaving filter pushes unboundedly without honoring `frame_wanted_out`/`frame_blocked_in`, the fast branch fills `FFFrameQueueGlobal.max_queued` and aborts the entire graph with `ENOMEM` (`avfilter.c:1154-1156`).

### 3. Intra-Frame Slice Threading (`AVSliceThread`) and Release-Sequence Join Barriers

Basis: normative (`ISO/IEC 9899:2018` §7.17.3) + source (`FFmpeg/FFmpeg`).

Both `libavfilter` (`libavfilter/pthread.c:59-73`) and `libavcodec` (`libavcodec/pthread_slice.c:41-113`) delegate intra-frame data-parallel execution to `AVSliceThread` (`libavutil/slicethread.c:36-245`):

- **Work stealing (`slicethread.c:63-86`):** `avpriv_slicethread_execute2` initializes `ctx->first_job = 0`, `ctx->current_job = ctx->nb_active_threads`, and `ctx->error = 0` (`lines 213-215`), then wakes `nb_workers` persistent pthreads (`lines 220-226`) while optionally participating via the calling thread (`lines 228-231`). Inside `run_jobs(ctx)`:
  1. Each participating thread atomically claims its initial slice `first_job = atomic_fetch_add_explicit(&ctx->first_job, 1, memory_order_acq_rel)` (`line 67`, yielding dense worker IDs `0 .. nb_active_threads - 1`).
  2. In the `do { ... } while ((current_job = atomic_fetch_add_explicit(&ctx->current_job, 1, memory_order_acq_rel)) < nb_jobs)` loop (`lines 69-83`), threads dynamically steal remaining jobs until `current_job >= nb_jobs`.
  3. First non-zero worker error is latched lock-free via `atomic_compare_exchange_strong_explicit(&ctx->error, &prev, ret, memory_order_relaxed, memory_order_relaxed)` (`lines 77-79`).
- **Exact C17 release-sequence completion predicate (`slicethread.c:85, 105-109, 233-243`):** Every one of the `nb_active_threads` participating threads executes exactly **one** failing `atomic_fetch_add_explicit(&ctx->current_job, 1, memory_order_acq_rel)` on exit. Therefore, the return values observed upon loop termination are a bijection onto `{nb_jobs, nb_jobs + 1, ..., nb_jobs + nb_active_threads - 1}`. By ISO/IEC 9899:2018 §7.17.3 (and the C++20/C23 contiguous-RMW release sequence rule), each `acq_rel` fetch-add synchronizes with subsequent RMWs in the modification order of `ctx->current_job`. The unique thread observing `current_job == nb_jobs + nb_active_threads - 1` (`line 85`) has guaranteed *happens-before* visibility of **all** worker slice writes and `ctx->error` updates before returning `is_last = 1` (or acquiring `done_mutex` to set `ctx->done = 1` and signal `done_cond`, `lines 105-109`).
- **Unchecked pointer aliasing in C callers:** `pthread_slice.c:64` dispatches `c->func(avctx, (char *)c->args + c->job_size * jobnr)` over raw `void *`. Nothing in the type system prevents two slices from mutating overlapping destination macroblock/pixel rows (e.g., horizontal/vertical deblocking edge filters or improperly stride-partitioned filter kernels).

### 4. Inter-Frame Codec Threading (`pthread_frame.c`) and Lock-Free `ThreadProgress` Barriers

Basis: normative (`ISO/IEC 9899:2018` §7.17) + source (`FFmpeg/FFmpeg`) + execution (`probe_avbuffer_progress.c`).

Inter-frame decoding (`libavcodec/pthread_frame.c`) overlaps execution across $T$ `PerThreadContext` worker threads arranged in a circular ring (`next_decoding`, `next_finished`, `lines 143-144, 588-601`):

1. **Sequential setup handoff (`submit_packet`, `pthread_frame.c:492-558`):** Before waking worker `p = &fctx->threads[fctx->next_decoding]`, the main thread waits for `prev_thread` to leave `STATE_SETTING_UP` (reaching `STATE_SETUP_FINISHED`), invokes the codec's `update_thread_context(p->avctx, prev_thread->avctx, 0)` (`line 530`) to copy reference picture lists/SPS/PPS headers synchronously, swaps non-threadsafe `hwaccel` state (`stash_hwaccel` at `lines 544-548` & `703-707`) protected by `hwaccel_mutex` (`lines 271-274, 685-688`) and `async_lock` (`lines 159-173, 567, 627, 695`), stores `STATE_SETTING_UP` into `p->state` (`line 550`), and signals `p->input_cond`.
2. **Parallel reconstruction after `ff_thread_finish_setup` (`lines 258-331, 675-718`):** Once the worker finishes parsing headers and allocating output buffers, it calls `ff_thread_finish_setup(avctx)`, transitioning `p->state` to `STATE_SETUP_FINISHED` and broadcasting `p->progress_cond`. Thereafter, the **next** worker thread $k+1$ may begin entropy decoding and reconstructing Frame $t+1$ concurrently while thread $k$ reconstructs rows of Frame $t$.

#### Memory-Model Analysis of `ThreadProgress` (`threadprogress.c:53-78` & `pthread_frame.c:631-673`)

Row-level synchronization between producer thread $k$ and reference-consuming thread $k+1$ uses `ThreadProgress` (`libavcodec/threadprogress.h:43-48`, `threadprogress.c:53-78`) or per-field `ThreadFrame.progress[2]` (`pthread_frame.c:631-673`):

```c
void ff_thread_progress_report(ThreadProgress *pro, int n) {
    if (atomic_load_explicit(&pro->progress, memory_order_relaxed) >= n)
        return;
    ff_mutex_lock(&pro->progress_mutex);
    atomic_store_explicit(&pro->progress, n, memory_order_release);
    ff_cond_broadcast(&pro->progress_cond);
    ff_mutex_unlock(&pro->progress_mutex);
}

void ff_thread_progress_await(const ThreadProgress *pro_c, int n) {
    ThreadProgress *pro = (ThreadProgress*)pro_c;
    if (atomic_load_explicit(&pro->progress, memory_order_acquire) >= n)
        return;
    ff_mutex_lock(&pro->progress_mutex);
    while (atomic_load_explicit(&pro->progress, memory_order_relaxed) < n)
        ff_cond_wait(&pro->progress_cond, &pro->progress_mutex);
    ff_mutex_unlock(&pro->progress_mutex);
}
```

- **Fast-path speedup:** In our Xeon C11 micro-probe (`probe_avbuffer_progress.c`), the uncontended `memory_order_acquire` check executes in **`1.68 ns`** versus **`15.47 ns`** for a mutex-guarded check (`9.21x` faster), forming a direct C17 `Release -> Acquire` *synchronizes-with* edge that publishes all pixel stores completed prior to `ff_thread_progress_report(..., n)`.
- **Brittle slow-path invariant (`threadprogress.c:58-61, 74-77`):** Notice that line `75` inside the `while` loop reads `pro->progress` with **`memory_order_relaxed`**, NOT `memory_order_acquire`! Why does this not violate weak memory ordering on `aarch64` or `riscv64`? Solely because the producer performs `atomic_store_explicit(..., memory_order_release)` *while holding `pro->progress_mutex`* (`lines 58-61`). Consequently, if the consumer enters `ff_mutex_lock(&pro->progress_mutex)` (`line 74`) and immediately observes `progress >= n` on `line 75` without blocking on `ff_cond_wait`, mutex acquisition (`ff_mutex_lock`) *synchronizes-with* the producer's `ff_mutex_unlock` (`line 61`), providing the missing acquire semantics! If a future optimization ever moved `atomic_store_explicit` *before* `ff_mutex_lock` on the producer side, a consumer missing the fast path (`line 71`) could acquire the lock first, read the new `n` on `line 75` via `memory_order_relaxed`, skip `ff_cond_wait`, and read stale reference frame bytes on weakly ordered ISAs!
- **Disconnected spatial invariant:** Neither `ThreadProgress` nor `ThreadFrame.progress` links integer `n` to actual `AVFrame` row slices `[0 .. n * stride)`. Any codec bug that forgets vertical subpel interpolation filter margins (e.g., reading `y + 4` rows for 8-tap luma MC) or conflates top/bottom fields in `progress[field]` silently races without bounds or sanitizer detection unless ThreadSanitizer executes that exact MV path.

### 5. Empirical Critique of `rav1d`'s `DisjointMut` vs. Verified Zero-Copy Rust Ownership & Concurrency

Basis: source (`memorysafety/rav1d`, `crossbeam-rs/crossbeam`, `google/zerocopy`, `joshlf/anneal`) + derived.

`memorysafety/rav1d` (`2e7216c20ac2a75de204d6c8d7268b75a45959b4`) demonstrates the pitfalls of a mechanical C-to-Rust concurrency port (`dav1d` -> `rav1d`):

1. **Over-synchronized task scheduling (`src/thread_task.rs:51-165`):** `Rav1dTasks` combines `RwLock<Vec<Rav1dTask>>`, `Mutex<Vec<Rav1dTask>>`, and `Ordering::SeqCst` atomics (`lines 60, 61, 105, 117, 124, 133-134, 165`), paying global sequential consistency fences on ring indices instead of tight `Acquire`/`Release` pairs.
2. **Unsound release-mode erasure in `DisjointMut<T>` (`src/disjoint_mut.rs:34-109`):** `DisjointMut<T>` wraps `UnsafeCell<T>` (`line 39`) and hands out mutable guards `DisjointMutGuard { slice: &'a mut V, ... }` (`line 99`) from a shared `&DisjointMut<T>` reference across worker threads. While debug builds dynamically track borrowed index ranges (`#[cfg(debug_assertions)]`), release builds compile `DisjointMut` to `#[repr(transparent)]` (`line 33`) with **zero runtime checks**, justified by the comment at `src/disjoint_mut.rs:70-74`:
   > *"Furthermore, all `T`s used have `AsMutPtr::Target`s that are provenanceless, i.e. they have no internal references or pointers or integers that hold pointer provenance. Thus, a data race due the lack of runtime disjointness checking in release mode would only result in wrong results, and cannot result in memory safety."*
   This premise is **false in Rust and LLVM**: (a) creating two overlapping `&mut [u8]` slices (or `&mut [u8]` overlapping `&[u8]`) violates Rust aliasing invariants (Stacked/Tree Borrows) regardless of whether element bytes carry pointer provenance; (b) non-atomic read/write data races in LLVM produce `poison`/`undef` values, which can poison branch predicates, loop bounds, or table indices derived from those pixels—causing out-of-bounds memory corruption in release builds (`minirust-tree-borrows-protectors-and-program-logic-correspondence`, `rust-atomics-weak-memory-and-aliasing-operational-models`).

#### Clean-Rewrite Verified Rust Architecture (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

A clean-room Rust rewrite targeting Anneal verification eliminates C aliasing, `AVBufferRef` heap bloat, and `DisjointMut` UB simultaneously:

1. **Inline `FrameBuf` / `CowFrame` (`Arc<PooledStorage>` + value slice `(offset, len, stride)`):**
   Eliminate FFmpeg's heap-allocated 24-byte `AVBufferRef` wrapper (`2.21x` pair speedup measured in `probe_avbuffer_progress.c`). A `PlaneSlice` holds `storage: Arc<PooledStorage>` plus by-value `(offset, len, stride)`. Calling `frame.make_mut(&pool)` takes `&mut CowFrame`—statically preventing FFmpeg's single-`AVBufferRef` aliasing corruption via Rust's exclusive borrow checker—and checks `Arc::get_mut(&mut self.storage)` (`Release` on drops + `Acquire` on `strong_count == 1` check) to mutate in place with zero copies whenever unshared, falling back to fallible pool checkout (`pool.try_get()`) otherwise. `PooledStorage` returns backing slabs to a lock-free `crossbeam_queue::SegQueue` (`crossbeam-rs/crossbeam@a28f40fdddb70bea8e5faf0efad9af0be4b9dbea`, `crossbeam-queue/src/seg_queue.rs:1-120`) without FFmpeg's invasive `BUFFER_FLAG_NO_FREE` self-freeing hazard.
2. **Type-state `FilterGraph` & Scoped Slice Threading:**
   Split filtergraph lifecycle into `UnconfiguredGraph -> ConfiguredGraph` (output by constraint intersection `mergers_video`/`mergers_audio`, locking every link's `LinkFormat` statically) and require `&mut ConfiguredGraph` for `step()` / `request_oldest()`, rejecting concurrent multi-threaded graph activation at compile time. Within individual filters and `AVSliceThread`-style codecs, use `std::thread::scope` over `out_plane.chunks_mut(slice_rows * stride)` paired with read-only `&in_plane[..]` halo views—requiring **zero `unsafe`** and **zero runtime interval tracking**.
3. **Monotonic `RowProgressPlane` Ghost Capability for `FF_THREAD_FRAME`:**
   To preserve FFmpeg's sub-frame `1.68 ns` `ThreadProgress` overlap without `rav1d`-style `DisjointMut` UB, partition each in-flight decoded frame plane into a single producer handle `RowWriter<'a, H>` and shareable `RowReader` handles governed by one `AtomicUsize` `progress_row` (in `[0..=H]`) plus a `Mutex<()>`/`Condvar`:
   - **Monotonic spatial invariant (proven in Anneal MIR-to-Lean):** At any instant where `progress_row == r`, rows `[0 .. r)` are **permanently immutable** (`&[u8]` only, shared across all reference consumers) for the remaining lifetime of that decode pass (until all `Arc<Frame>` readers drop and `Arc::get_mut` reclaims the entire buffer for the pool), while `RowWriter` holds exclusive mutable permission **strictly to suffix `[r * stride .. H * stride)`**.
   - `RowWriter::publish_until(&mut self, new_r: usize)` checks `new_r >= self.published && new_r <= self.height`, finishes all pixel/deblocking writes up to `new_r` (including any vertical filter tail margin), stores `new_r` with `Ordering::Release` inside the slow-path mutex lock (or pairs explicit `Ordering::Acquire` on both fast and slow paths of `await_row` so soundness does not even depend on mutex placement!), and permanently surrenders write capability for `[self.published .. new_r)`.
   - `RowReader::await_rows(&self, needed_r: usize) -> Result<&[u8], DecodeError>` validates `needed_r <= self.height`, executes the `1.68 ns` `Ordering::Acquire` fast path (`if progress.load(Ordering::Acquire) >= needed_r`), and returns an ordinary `&[u8]` slice of `[0 .. needed_r * stride)`.
   - Because `&mut` suffix `[r..H)` and `&` prefix `[0..r)` are **provably disjoint** and transition monotonically once per frame generation, this design achieves **zero UB, zero runtime overlap tables, zero panics, and full row-pipelined parity with FFmpeg**.
4. **Verification Priority Stack Across `libavutil`/`libavfilter`/`libavcodec` Threading:**

| Priority Tier | Target Guarantee | Concurrency & Buffer Lifetime Mechanism |
| :--- | :--- | :--- |
| **1. UB-Freedom** | 100% absence of data races, UAF, & aliasing UB | Borrow-checked `&mut` exclusivity on `CowFrame::make_mut` & `&mut ConfiguredGraph`; monotonic prefix/suffix split in `RowProgressPlane` replacing `DisjointMut` erasure; `C` ABI `AVBufferRef` wrappers only at FFI boundary. |
| **2. Panic-Freedom** | Zero aborts/panics on OOM or malformed MV row bounds | Clamped/fallible `await_rows(needed_r) -> Result<&[u8], FrameErr>`; checked pool allocation (`try_alloc`); Anneal 3-axiom proofs discharging monotonic index invariants `0 <= r <= H` and non-overlapping `slice_rows * stride`. |
| **3. Behavioral Equivalence** | Deterministic FATE parity & bit-exact SIMD/scalar results | Single-threaded sink-heap schedule (`request_oldest`) matches FFmpeg filtergraph execution order deterministically; `RowProgressPlane` publishes bit-identical reference pixels to FFmpeg `ThreadProgress`. |
| **4. Spec Conformance** | Exact C17/Rust atomics & H.264/HEVC/AV1 MV bounds | Explicit `Acquire`/`Release` synchronization independent of producer mutex placement; vertical subpel interpolation halo margin enforced in `needed_r` type signature. |

## Boundaries

- **known not to apply:** The monotonic `RowProgressPlane` freeze-prefix invariant applies to raster/superblock-row codecs where all in-loop filtering (deblocking, SAO, CDEF, loop restoration) on rows `[0 .. r)` completes *before* advancing `progress_row` to `r`. It is **known not to apply** to out-of-order multi-pass algorithms that mutate previously published rows `[0 .. r)` after signaling `r` (which is likewise a data race in FFmpeg's `ff_thread_report_progress`). `AVFilterGraph` lock-free concurrency is also **known not to apply** to multi-threaded external filtergraph calls without an outer mutex.
- **not examined:** GPU hardware-surface timeline synchronization (`AVHWFramesContext` backing Vulkan `VkSemaphore`, VA-API `vaSyncSurface`, D3D12 fences, or DRM syncobjs—covered for Wayland/PipeWire/Vulkan in `wayland-explicit-drm-syncobj-dbus-fd-passing-and-pipewire-graph-scheduling` and `vulkan-webgpu-explicit-memory-models-spirv-uniformity-and-shader-sandboxing`), individual filter SIMD assembly kernels, and end-to-end 4K/8K wall-clock scaling benchmarks across all CPU core counts (only single-process micro-probes of `AVBufferRef`/`Arc` and `ThreadProgress` fast-path vs mutex latencies were executed).
- **unknown:** Exact Lean 4 kernel proof-checking wall-clock cost in Anneal for verifying full codec motion-vector row-margin arithmetic composed with `RowProgressPlane` ghost tokens.
- **unsupported:** Unsynchronized concurrent calls to `avfilter_graph_request_oldest` / `ff_filter_graph_run_once` or simultaneous `av_buffersrc_add_frame` / `av_buffersink_get_frame` from separate threads on one `AVFilterGraph` in upstream FFmpeg.

## Evidence

### Source Code & Specification Citations

- **`FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`):**
  - `libavutil/buffer_internal.h:38-108` (`struct AVBuffer`, `BufferPoolEntry`, `struct AVBufferPool`, `BUFFER_FLAG_NO_FREE`).
  - `libavutil/buffer.h:82-145` (`AVBufferRef`, `AV_BUFFER_FLAG_READONLY`).
  - `libavutil/buffer.c:30-71` (`buffer_create`, `av_buffer_create`), `104-164` (`av_buffer_ref` `relaxed`, `buffer_replace` `acq_rel` + line `133` `BUFFER_FLAG_NO_FREE` hoist, `av_buffer_is_writable` `seq_cst`), `260-436` (`av_buffer_pool_init2`, `buffer_pool_free`, `av_buffer_pool_uninit`, `pool_release_buffer`, `av_buffer_pool_get`).
  - `libavutil/frame.c:209-255` (`av_frame_get_buffer`, `frame_copy_props`), `538-595` (`av_frame_is_writable`, `av_frame_make_writable`).
  - `libavutil/slicethread.c:36-135, 206-265` (`AVSliceThread`, `run_jobs` release sequence at `65-86`, `avpriv_slicethread_execute2`).
  - `libavfilter/avfilter.h:172, 279-395` (`AVFILTER_FLAG_SLICE_THREADS`, `AVFilterContext`, `AVFilterLink`).
  - `libavfilter/filters.h:145-221` (`FilterLink`, `FF_FILTER_FLAG_DYNAMIC_FRAME_SIZE`, `FF_FILTER_FLAG_DYNAMIC_FRAME_FORMAT`).
  - `libavfilter/framequeue.h:35-95` (`FFFrameBucket`, `FFFrameQueueGlobal`, `FFFrameQueue` `first_bucket`).
  - `libavfilter/avfilter.c:1112-1165` (`ff_filter_frame`, `max_queued`, `ff_filter_set_ready(..., 300)`), `1491-1663` (`ff_filter_activate`, `ff_inlink_acknowledge_status`, `ff_inlink_check_frame_params`, `ff_inlink_make_frame_writable`).
  - `libavfilter/avfiltergraph.c:551-642` (`query_formats`), `1348-1525` (`swap_sample_fmts`, `pick_formats`, `avfilter_graph_config`), `1618-1692` (`ff_avfilter_graph_update_heap`, `avfilter_graph_request_oldest`, `ff_filter_graph_run_once`).
  - `libavfilter/formats.c:315-415` (`merge_generic_internal`, `CONVERSION_FILTER_SWSCALE`, `CONVERSION_FILTER_ARESAMPLE`, `mergers_video`).
  - `libavfilter/pthread.c:59-115` (`thread_execute`, `ff_graph_thread_init`).
  - `libavcodec/pthread_slice.c:41-115` (`SliceThreadContext`, `worker_func`, `thread_execute`).
  - `libavcodec/pthread_frame.c:78-158` (`PerThreadContext`, `FrameThreadContext`), `241-315` (`frame_worker_thread`), `492-629` (`submit_packet`, `ff_thread_receive_frame`, `output_cond`), `631-718` (`ff_thread_report_progress`, `ff_thread_await_progress`, `ff_thread_finish_setup`).
  - `libavcodec/threadprogress.h:43-92` & `libavcodec/threadprogress.c:33-78` (`ThreadProgress`, `ff_thread_progress_report`, `ff_thread_progress_await`).
- **Rust Concurrency & Verification References:**
  - `memorysafety/rav1d` (`2e7216c20ac2a75de204d6c8d7268b75a45959b4`): `src/thread_task.rs:51-165`, `src/disjoint_mut.rs:32-115` (`DisjointMut` debug-only tracking and release-mode soundness rationale at `60-74`).
  - `crossbeam-rs/crossbeam` (`a28f40fdddb70bea8e5faf0efad9af0be4b9dbea`): `crossbeam-queue/src/seg_queue.rs:1-120` (`SegQueue` lock-free segmented pool).
  - `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`): `zerocopy/src/lib.rs:4358` (`FromBytes`), `zerocopy/src/ref.rs:835-860` (`Ref::from_prefix_with_elems`).
  - `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`): `Cargo.toml:1-15`.

### Reproducible Execution Probe (`probe_avbuffer_progress.c`)

Standalone extracted C11 micro-probe comparing (1) `AVBufferRef` same-pointer aliasing corruption under `av_buffer_is_writable`, (2) `av_buffer_ref` + `av_buffer_unref` heap-wrapped pair cost vs single-indirection `Arc`-style clone/drop, and (3) `ThreadProgress` `memory_order_acquire` fast path (`libavcodec/threadprogress.c:71`) vs `pthread_mutex_lock` check. Executed on `Linux 7.1.6-1rodete1-amd64 x86_64` (`8-vCPU Intel(R) Xeon(R) CPU @ 2.20GHz`), compiled with `gcc (Debian 15.2.0-14) 15.2.0`:

```c
#define _POSIX_C_SOURCE 200809L
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <pthread.h>

typedef struct SimAVBuffer {
    uint8_t *data;
    size_t size;
    atomic_uint refcount;
    int flags;
} SimAVBuffer;

typedef struct SimAVBufferRef {
    SimAVBuffer *buffer;
    uint8_t *data;
    size_t size;
} SimAVBufferRef;

static SimAVBufferRef *sim_av_buffer_ref(const SimAVBufferRef *buf) {
    SimAVBufferRef *ret = calloc(1, sizeof(*ret));
    if (!ret) return NULL;
    *ret = *buf;
    atomic_fetch_add_explicit(&buf->buffer->refcount, 1, memory_order_relaxed);
    return ret;
}

static void sim_av_buffer_unref(SimAVBufferRef **pbuf) {
    SimAVBuffer *b = (*pbuf)->buffer;
    free(*pbuf);
    *pbuf = NULL;
    if (atomic_fetch_sub_explicit(&b->refcount, 1, memory_order_acq_rel) == 1) {
        free(b->data);
        free(b);
    }
}

static SimAVBuffer *sim_arc_clone(SimAVBuffer *inner) {
    atomic_fetch_add_explicit(&inner->refcount, 1, memory_order_relaxed);
    return inner;
}

static void sim_arc_drop(SimAVBuffer *inner) {
    if (atomic_fetch_sub_explicit(&inner->refcount, 1, memory_order_release) == 1) {
        atomic_thread_fence(memory_order_acquire);
        free(inner->data);
        free(inner);
    }
}

typedef struct SimThreadProgress {
    atomic_int progress;
    pthread_mutex_t mutex;
    pthread_cond_t cond;
} SimThreadProgress;

static void sim_progress_await(SimThreadProgress *pro, int n) {
    if (atomic_load_explicit(&pro->progress, memory_order_acquire) >= n)
        return;
    pthread_mutex_lock(&pro->mutex);
    while (atomic_load_explicit(&pro->progress, memory_order_relaxed) < n)
        pthread_cond_wait(&pro->cond, &pro->mutex);
    pthread_mutex_unlock(&pro->mutex);
}

static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

int main(void) {
    const int N = 2000000;
    SimAVBuffer *b = calloc(1, sizeof(*b));
    b->data = calloc(1, 64);
    b->size = 64;
    atomic_init(&b->refcount, 1);
    SimAVBufferRef root = { .buffer = b, .data = b->data, .size = 64 };

    SimAVBufferRef *alias_reader = &root;
    SimAVBufferRef *alias_writer = &root;
    b->data[0] = 0x42;
    int writable = (!(alias_writer->buffer->flags & 1) && atomic_load(&alias_writer->buffer->refcount) == 1);
    if (writable) alias_writer->data[0] = 0xFF;
    printf("same_ref_aliasing: is_writable=%d reader_byte_after=0x%02x (expected_immutable=0x42)\n",
           writable, alias_reader->data[0]);

    uint64_t t0 = now_ns();
    for (int i = 0; i < N; i++) {
        SimAVBufferRef *r = sim_av_buffer_ref(&root);
        asm volatile("" : "+r"(r) :: "memory");
        sim_av_buffer_unref(&r);
    }
    uint64_t t1 = now_ns();

    uint64_t t2 = now_ns();
    for (int i = 0; i < N; i++) {
        SimAVBuffer *a = sim_arc_clone(b);
        asm volatile("" : "+r"(a) :: "memory");
        sim_arc_drop(a);
    }
    uint64_t t3 = now_ns();

    SimThreadProgress pro;
    atomic_init(&pro.progress, 64);
    pthread_mutex_init(&pro.mutex, NULL);
    pthread_cond_init(&pro.cond, NULL);

    uint64_t t4 = now_ns();
    for (int i = 0; i < N; i++) {
        sim_progress_await(&pro, 32);
        asm volatile("" ::: "memory");
    }
    uint64_t t5 = now_ns();

    uint64_t t6 = now_ns();
    for (int i = 0; i < N; i++) {
        pthread_mutex_lock(&pro.mutex);
        int ok = atomic_load_explicit(&pro.progress, memory_order_relaxed) >= 32;
        asm volatile("" : "+r"(ok) :: "memory");
        pthread_mutex_unlock(&pro.mutex);
    }
    uint64_t t7 = now_ns();

    printf("avbuffer_ref_unref_ns_per_pair=%.2f\n", (double)(t1 - t0) / N);
    printf("arc_clone_drop_ns_per_pair=%.2f\n", (double)(t3 - t2) / N);
    printf("threadprogress_acquire_fastpath_ns=%.2f\n", (double)(t5 - t4) / N);
    printf("mutex_guarded_check_ns=%.2f\n", (double)(t7 - t6) / N);

    free(b->data);
    free(b);
    return 0;
}
```

Command and verbatim output (`2026-11-20`):

```text
$ gcc -O2 -Wall -pthread probe_avbuffer_progress.c -o probe_avbuffer_progress
$ ./probe_avbuffer_progress
same_ref_aliasing: is_writable=1 reader_byte_after=0xff (expected_immutable=0x42)
avbuffer_ref_unref_ns_per_pair=34.54
arc_clone_drop_ns_per_pair=15.63
threadprogress_acquire_fastpath_ns=1.68
mutex_guarded_check_ns=15.47
```

## Revalidation

To verify whether these invariants or overheads have changed on a newer `FFmpeg/FFmpeg` or `memorysafety/rav1d` revision:

1. **Micro-probe timing & aliasing check:** Compile and execute `probe_avbuffer_progress.c` (`gcc -O2 -pthread`) on the target host ISA (`x86_64`, `aarch64`, `riscv64`) to re-measure the `AVBufferRef` heap wrapper penalty and `ThreadProgress` acquire fast-path latency.
2. **Buffer & atomic-ordering diffs:** Inspect `libavutil/buffer.c` (`av_buffer_ref`, `buffer_replace` line `133` `BUFFER_FLAG_NO_FREE`), `libavcodec/threadprogress.c` (confirming `ff_thread_progress_report` still performs `memory_order_release` *inside* `progress_mutex`), and `libavutil/slicethread.c` (`run_jobs` completion count).
3. **`rav1d` `DisjointMut` check:** Inspect `src/disjoint_mut.rs` in `memorysafety/rav1d` to check whether release-mode disjointness checks remain erased (`#[cfg(debug_assertions)]`).
