# Memory Allocator Architectures, Hardened Heaps, and Virtual-Page Quarantines

## Summary

Modern memory allocators navigate an irreducible four-way trade-off among multicore fast-path latency, TLB/page-table efficiency, temporal and spatial exploit resistance, and formal verifiability. Direct source inspection across seven production and research allocators (`mimalloc` v3, `TCMalloc`, `jemalloc`, Apple `XNU kalloc_type` and `libmalloc xzone`, `LLVM Scudo`, `MarkUs`, and `FFMalloc`), combined with analytical and Linux kernel micro-probes, establishes five engineering invariants:

1. **Multicore fast paths eliminate atomic RMW operations through sharding or kernel-assisted restartable sequences (`rseq`):** `mimalloc` v3 shards every slab page (`mi_page_t`) into three free lists (`free`, `local_free`, and atomic `xthread_free` carrying an ownership bit in LSB 0) so owning-thread allocation and free execute with zero atomics while bounding work via a monotonic heartbeat. `TCMalloc` avoids per-thread memory blowup by caching per *CPU* via Linux `rseq` (`percpu_rseq_x86_64.S`), executing batch push/pop inside signed abort-trampoline critical sections committed by a single 32-bit store to `[current:16, remaining_capacity:16]`. `TCMalloc` (Temeraire `HugePageFiller`) and `jemalloc` (`hpa` + two-stage `smoothstep` dirty/muzzy decay) prioritize 2 MiB hugepage packing over raw `malloc` instruction count because TLB miss reduction dominates fleet-wide throughput.
2. **Type-segregated heaps break cross-type UAF exploitation at the cost of bucket-scaled slab fragmentation:** Apple `kalloc_type` analyzes C struct layouts in 8-byte granules (`__builtin_xnu_type_signature`: `PADDING`, `POINTER`, `DATA`, `DUAL`, `PAC`) to strictly isolate pure-data buffers from pointer-bearing structures. Userspace `xzone malloc` extends this with Typed Memory Operations (`malloc_type_*`), per-boot-stable randomized pointer buckets, opposing allocation fronts (blocking cross-bucket spatial grooming), PAC-signed sequence-numbered free-list pointers, guard objects above 32 KiB, and an "early allocator" escape hatch to suppress cold-start fragmentation.
3. **ARM MTE odd-even parity tagging deterministically catches 1-slot linear overflows but more than doubles 2nd-reuse UAF collision risk:** Both `Scudo` (`combined.h` `computeOddEvenMaskForPointerMaybe`) and Apple `xzone` support odd-even parity tagging. Because Tag `0` is always excluded (`ExcludeMask |= 1`), odd-even mode restricts alternating slots to 8 odd tags `{1,3,5,7,9,11,13,15}` and 7 non-zero even tags `{2,4,6,8,10,12,14}`. Executable verification confirms 100.00% 1-slot linear OOB detection (vs. 93.33% uniform), while raising mean 2nd-reuse temporal UAF tag-collision probability from **7.14%** (`1/14`, uniform) to **15.48%** (`0.5*(1/7 + 1/6)`, **2.17× higher**)—explaining why Scudo exposes `M_MEMTAG_TUNING_BUFFER_OVERFLOW` vs. `M_MEMTAG_TUNING_UAF`.
4. **Deterministic UAF-prevention allocators pay structural penalties in conservative GC pauses (`MarkUs`) or VMA fragmentation, TLB shootdowns, and page pinning (`FFMalloc`):** `MarkUs` quarantines explicitly freed objects in an XOR-masked list (`XOR = 1ul << 52`, preventing self-pinning by its conservative Boehm-GC scanner) and triggers a mark-and-sweep pass once quarantine exceeds 25% of mapped heap. `FFMalloc` bans virtual-address reuse outright, reclaiming physical pages via batched `munmap` (`MIN_PAGES_TO_FREE = 8` or VMA-coalescing islands) and explicitly swallowing `ENOMEM` on Linux `vm.max_map_count` exhaustion. Live Linux probing shows 1-page alternating `munmap` creates `+1023` VMAs over 8 MiB (`15.955 ms`) vs. `+127` VMAs (`1.365 ms`, 11.7× faster) for 8-page batches and `+0` VMAs (`6.816 ms`) for `madvise(MADV_DONTNEED)`—while 1 surviving object per 4 KiB page amplifies physical RSS up to $256\times$ for 16 B objects.
5. **Formal verification of allocators hinges on non-duplicable provenance tokens, intrusive free-list type punning, and concurrency model fidelity:** Robson's theorem proves any non-moving allocator incurs worst-case $\Omega(M \log n)$ heap overhead (empirically exact at $\frac{1}{2}\log_2 n + 1$ for first-fit and best-fit). Mechanized proofs (`VST` sequential resource-aware specs, `RefinedC` on `Iris`/Coq for fixed-size `mpool` slabs, and `StarMalloc` in F*/Steel for concurrent security-oriented slabs) verify intrusive free-list recycling using authoritative/fragmental ghost ownership tokens, but Linux `rseq` restartable sequences, relaxed-atomic `QSBR` reclamation, and hardware MTE tag provenance remain outside standard sequentially consistent Iris `HeapLang` specifications.

## Applicability

This report examines eight pinned upstream allocator implementations and five foundational theoretical and verification specifications recorded in `REPORT.json`, observed on `2026-11-19`:

- **Production multicore allocators:** `microsoft/mimalloc` (`1d8fd85aa3ab`, `main3` / v3 architecture; APLAS 2019 DOI `10.1007/978-3-030-34175-6_13`), `google/tcmalloc` (`9c3ddad744bc`; OSDI 2021 Temeraire), and `jemalloc/jemalloc` (`91de8ca2d405`).
- **Hardened & hardware-assisted allocators:** `apple-oss-distributions/xnu` (`f6217f891ac0`, kernel `kalloc_type`/`zalloc`), `apple-oss-distributions/libmalloc` (`c49dafa25f1e`, userspace `xzone malloc`), and `llvm/llvm-project` (`16ee29de0984`, `compiler-rt/lib/scudo/standalone/`).
- **Deterministic temporal-safety allocators:** `SamAinsworth/MarkUs-sp2020` (`60690b9a1421`, IEEE S&P 2020 DOI `10.1109/SP40000.2020.00058`) and `bwickman97/ffmalloc` (`2f24ecf72888`, USENIX Security 2021).
- **Bounds & formal verification foundations:** Robson (JACM 1974, DOI `10.1145/321832.321846`), Iris (Jung et al., JFP 2018, DOI `10.1017/S0956796818000151`), RefinedC (Sammler et al., PLDI 2021, DOI `10.1145/3453483.3454036`), StarMalloc (Reitz, Fromherz, Protzenko, OOPSLA 2024, DOI `10.1145/3689773`), and VST Malloc/Free (Appel & Naumann, ISMM 2020, DOI `10.1145/3381898.3397211`).

Relationships among subjects: the report compares architectural trade-offs across performance-first allocators (`mimalloc`, `TCMalloc`, `jemalloc`), deployable exploit-hardened allocators (`kalloc_type`/`xzone`, `Scudo` + MTE), deterministic UAF-mitigating quarantine/OTA designs (`MarkUs`, `FFMalloc`), and mechanized separation-logic verification frameworks (`Iris`/`RefinedC`, `VST`, `StarMalloc`). Architecture-specific observations apply as scoped: `TCMalloc` `rseq` assembly applies to Linux x86-64 (and analogously AArch64 `percpu_rseq_aarch64.S`), ARM MTE tagging applies to AArch64 `FEAT_MTE`/`FEAT_MTE2` with Top-Byte Ignore (`TBI`), Apple `kalloc_type`/`xzone` apply to Darwin/XNU + Clang Typed Memory Operations, and Linux VMA-count probing applies to Linux virtual memory (`mmap`/`munmap`/`madvise` under `vm.max_map_count`).

## Findings

### 1. Comparative Allocator Architecture, Security, and Reclamation Matrix

Basis: source + documentation + derived

| Allocator | Fast-Path Sharding & Concurrency | Metadata Placement & Integrity | Temporal (UAF / Double-Free) Defense | Spatial (OOB) Defense | OS Reclamation & Hugepage Strategy | Dominant Failure / Cost Mode |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **mimalloc v3** (`microsoft/mimalloc` @ `1d8fd85aa3ab`) | Per-thread `theap` + triple per-page free lists (`free`, `local_free`, atomic `xthread_free`) | Out-of-band page header + `MI_ENCODE_FREELIST` XOR keys; `MI_PADDING` canary | Double-free detection via encoded free lists; optional ARM MTE neighbor-excluding retag (`prim-mte.h`); `MI_QSBR` | Optional `MI_PADDING` (`MI_SECURE>=4`), `MI_GUARDED` sampled guard pages, MTE | Arena slice commitment + OS purge | Cross-thread producer-consumer frees traverse `xthread_free` CAS; abandoned-page adoption |
| **TCMalloc** (`google/tcmalloc` @ `9c3ddad744bc`) | Per-**CPU** slab caches via Linux `rseq` (`percpu_rseq_x86_64.S`); lock-free single-store commit | Out-of-band pagemap + central freelists; sampled `GWP-ASan` (separate) | None on hot path (sampled GWP-ASan only); LIFO per-CPU reuse | None on hot path (sampled GWP-ASan) | Temeraire `HugePageFiller` / `HugeRegion` / `HugeCache` 2 MiB packing + subrelease | Immediate LIFO reuse is UAF-friendly; `rseq` unavailable on non-Linux/pre-4.18 kernels |
| **jemalloc** (`jemalloc/jemalloc` @ `91de8ca2d405`) | Per-thread `tcache` + sharded arenas + optional per-CPU arena binding | Out-of-band `emap` radix tree + slab bitmaps | None deterministic (LIFO/FIFO bin reuse); debug junk fill | Optional opt-in guard/redzone in debug builds | Two-stage `smoothstep` decay (`dirty` -> `muzzy` -> purged) + `hpa` pageslab hugification | Multi-arena fragmentation if thread-to-arena balance skews; no native MTE/type isolation |
| **Apple `kalloc_type` / `xzone`** (`xnu` @ `f6217f891ac0`, `libmalloc` @ `c49dafa25f1e`) | Per-CPU/magazine + size-and-type-bucketed spans (`16 KiB` slices) | Out-of-band metadata at unpredictable offsets; PAC-signed sequence-numbered inline free-list links | Type bucket isolation (data vs. ObjC vs. 1–4 randomized ptr buckets) + zero-on-free ($\le 1\text{ KiB}$) + ARM MTE ($\le 4\text{ KiB}$ tag-on-free; $\le 32\text{ KiB}$ tag-on-alloc) | Opposing allocation fronts + probabilistic guard pages + MTE odd-even parity + guard objects ($> 32\text{ KiB}$) | Slice/span reclamation per bucket; early allocator mitigates cold-start waste | Fragmentation scales with bucket count; intra-bucket same-type UAF still possible without MTE |
| **LLVM Scudo + MTE** (`llvm/llvm-project` @ `16ee29de0984`) | Exclusive or shared `TSD` + randomized per-region `SizeClassAllocator64` free lists | Inline 64-bit `AtomicPackedHeader` with 16-bit CRC32/BSD checksum keyed by `(Cookie, Ptr)` | FIFO `GlobalQuarantine` + header `State` check + ARM MTE retag (odd-even or uniform) | Header checksum catches linear overflow into adjacent header; MTE odd-even deterministic 1-slot OOB | Primary region release-to-OS (`MADV_DONTNEED`) + secondary `munmap` | 2-bit `Origin` cannot check aligned `new`/`delete` mismatch; odd-even MTE doubles 2nd-reuse UAF collision |
| **MarkUs** (`SamAinsworth/MarkUs-sp2020` @ `60690b9a1421`) | Boehm-Demers-Weiser GC heap + mutex-protected quarantine freeing lists | Out-of-band `hblkhdr` mark bits; quarantine links XOR-masked with `1ul << 52` | Deterministic UAF prevention (while pointers remain unhidden) via conservative root+heap mark before sweeping quarantine | None beyond underlying BDWGC layout | `potential_unmap` for idle large blocks; conservative GC sweep at >25% quarantine | Stop-the-world conservative mark pauses; hidden/encoded pointers bypass sweep; false retention |
| **FFMalloc** (`bwickman97/ffmalloc` @ `2f24ecf72888`) | Thread-cached bump-pointer bins over 4 MiB pools (`POOL_SIZE = 1<<22`) | Out-of-band 3-level 48-bit radix tree + `pagemap_t` bitmaps (internal metadata uses separate non-OTA mini-allocator) | Complete virtual-address one-time allocation (zero VA reuse; `SIGSEGV` after `munmap`) | Page-level separation across bins; no intra-page guard bytes | Batched `munmap` on $\ge 8$ contiguous all-freed 4 KiB pages or VMA-merging islands | Linux VMA exhaustion (`ENOMEM` on `vm.max_map_count`), TLB shootdowns, up to $256\times$ RSS pinning blowup |

---

### 2. High-Performance Multicore Heap Architectures: mimalloc, TCMalloc, and jemalloc

#### 2.1 mimalloc v3: Triple Free-List Sharding, Reciprocal Unalignment, and Security Tiers

Basis: source + documentation

In `microsoft/mimalloc` (`1d8fd85aa3ab`, `main3` / v3; building on `Leijen, Zorn, de Moura, APLAS 2019`, DOI `10.1007/978-3-030-34175-6_13`), allocation and deallocation are sharded down to individual fixed-block-size pages (`struct mi_page_s`, `include/mimalloc/types.h` L485–561). Every `mi_page_t` maintains **three** distinct free lists:
1. **`free`** (`mi_block_t*`, L518): immediately allocatable blocks popped exclusively by the owning thread (`theap`) without atomic instructions.
2. **`local_free`** (`mi_block_t*`, L519): blocks freed by the owning thread. Keeping `local_free` separate from `free` guarantees a *monotonic heartbeat*: even if a thread repeatedly allocates and frees a single object in a tight loop, `free` deterministically drains to `NULL`, forcing periodic execution of `_mi_page_free_collect` (which migrates `local_free` and `xthread_free`, performs deferred reclamation, and detects completely empty pages) in bounded amortized time.
3. **`xthread_free`** (`_Atomic(mi_thread_free_t)`, L538, placed on a separate cache line from `free`/`local_free` to eliminate false sharing!): a lock-free Treiber stack where non-owning threads push cross-thread frees via a single CAS loop (`mi_free_block_mt`, `src/alloc/free.c` L124–146). The least significant bit of `xthread_free` packs a page-ownership flag (`1` if owned, `0` if abandoned), enabling a concurrent freeing thread to atomically free a block *and* detect/reclaim an abandoned page in one CAS (`types.h` L503–508).

The page accounting invariant is exact (`types.h` L495–496):
$$(\text{used} - |\text{thread\_free}|) + |\text{free}| + |\text{local\_free}| = \text{capacity}$$
storing `used` rather than `freed` avoids reading free-list lengths on `mi_page_all_free`.

Three notable implementation details in mimalloc v3 (`1d8fd85aa3ab`):
- **Division-Free Interior Pointer Unalignment (`src/alloc/free.c` L165–176):** To convert an interior or aligned pointer offset `diff` into its block index without expensive integer division, each page precomputes `uint64_t block_recip = ceil(2^64 / block_size)` (`types.h` L550) and evaluates `(size_t)mi_mul_hi64_32((uint32_t)diff, page->block_recip)` (Lemire–Kaser–Kurz direct quotient computation).
- **Cache-Set Coloring (`types.h` L575–582):** First-block offsets within pages are randomized/stepped across `64 B` (`MI_PAGE_SMALL_CACHE_OFFSET_UNIT`, up to `512 B`) or `128 B` (`MI_PAGE_LARGE_CACHE_OFFSET_UNIT`, up to `4 KiB`) increments to avoid L1/L2 set-associativity thrashing across identically sized pages.
- **Tiered Hardening & MTE (`types.h` L127–162, `include/mimalloc/prim/prim-mte.h` L15–25):** `MI_SECURE >= 2` enables `MI_ENCODE_FREELIST` (XORing next pointers with per-page random `keys[2]`); `MI_SECURE >= 4` adds `MI_PADDING` overflow canaries; `MI_SECURE >= 5` enables byte-precise `MI_PADDING_CHECK_BYTES`; `MI_GUARDED` adds sampled trailing guard pages; `prim-mte.h` implements ARM MTE 4-bit tagging (`bits [59:56]`) by reading adjacent blocks' current hardware tags and excluding both neighbors (`mi_memtag_exclude_adjacent`) so linear 1-slot overflows deterministically fault without halving the tag space statically (subject to concurrent neighbor retagging races noted at `prim-mte.h` L23).

#### 2.2 TCMalloc: Linux `rseq` Per-CPU Caches and Temeraire HugePage-Aware Packing

Basis: source + documentation

Per-thread caching scales linearly in RAM with thread count ($O(T \cdot C)$). On servers running thousands of threads across 64–256 hardware cores, `TCMalloc` (`google/tcmalloc` @ `9c3ddad744bc`) instead caches small objects per **logical CPU** ($O(P \cdot C)$) using Linux **Restartable Sequences (`rseq`)**—avoiding both mutex contention and `LOCK CMPXCHG` atomic stalls on the hot path.

Direct inspection of `tcmalloc/internal/percpu_rseq_x86_64.S` (L23–360) reveals the exact low-level kernel-userspace contract:
1. **Signed Abort Trampoline (`DEFINE_UPSTREAM_CS`, L79–118):** Each critical section registers a 32-byte `__rseq_cs_<label>` descriptor containing `{version, flags, start_ip, post_commit_offset, abort_ip}`. To prevent an attacker with a write primitive over writable `__rseq_cs` memory from redirecting `abort_ip` to an arbitrary ROP gadget on preemption, the Linux `rseq` ABI verifies that the 4 bytes immediately preceding `abort_ip` match `TCMALLOC_PERCPU_RSEQ_SIGNATURE`, encoded as a valid `nopl 0xSIGNATURE(%rip)` instruction (`0x0f 0x1f 0x05 <sig>`, L115–117).
2. **Single-Store Commit Semantics (`TcmallocSlab_Internal_PushBatch` L261–294, `PopBatch` L328–360):**
   - `START_RSEQ` stores `&__rseq_cs_<label>` into `%fs:__rseq_abi@TPOFF+8`.
   - `FETCH_SLABS(%r8)` loads the per-CPU slab pointer and checks `TCMALLOC_CACHED_SLABS_BIT` (`btrq`).
   - A 32-bit header `(%r8, %rdi, 4)` packs two 16-bit fields: `[current:16, remaining_capacity:16]`.
   - `PushBatch` copies up to `min(len, remaining_capacity)` pointers into the *unused* slots above `current` (`movq %r10, (%r8, %r9, 8)`), and finally commits all pushed items with a **single 32-bit store** `movl %ecx, (%r8, %rdi, 4)` (L286) immediately before `.L..._commit`.
   - **Strict Register-Clobber ABI (L214–230):** If the kernel preempts or migrates the thread at any instruction in `[start, commit)`, it clears `rseq_cs` and jumps to `label_trampoline -> .L..._abort`, re-executing from scratch without restoring registers. Therefore the critical section MUST NOT mutate argument registers (`%rdi`, `%rsi`, `%rdx`) or callee-saved registers (`%rbx`, `%rbp`, `%rsp`, `%r12`–`%r15`), and MUST NOT perform any externally visible side effect before the final commit store.
3. **Temeraire HugePage-Aware Page Heap (`Hunter et al., OSDI 2021`; `tcmalloc/huge_page_aware_allocator.h`, `huge_page_filler.h` L96–637):**
   - Traditional 4 KiB page heaps fragment 2 MiB transparent hugepages (THPs), inflating dTLB misses. Temeraire reorganizes backing memory into four tiers: `HugePageFiller` (packs sub-2 MiB spans densely into 2 MiB `PageTracker` buckets classified as `kDenseRegular`, `kSparseRegular`, `kDonated`, and `kSparsePartialReleased`), `HugeRegion` (handles large allocations slightly exceeding 2 MiB slack thresholds), `HugeCache` (caches whole 2 MiB hugepages), and `HugeAllocator` (OS mmap interface).
   - **Subrelease vs. TLB Tension (`GetDesiredSubreleasePages`, `huge_page_filler.h` L635–637):** Releasing free 4 KiB sub-ranges inside a partially used 2 MiB hugepage via `MADV_DONTNEED` reclaims physical RAM immediately but breaks the 2 MiB PMD mapping into 512 4 KiB PTEs. `HugePageFiller` therefore prioritizes releasing from `kSparsePartialReleased` / `kSparseRegular` trackers and gates subrelease with `SkipSubreleaseIntervals` peak-demand history to keep hot working sets hugepage-backed. In Google fleet experiments (OSDI 2021), Temeraire increased throughput by up to 7.7% RPS, cut TLB miss stalls by 6%, reduced fragmentation by 26%, and lowered fleet-wide RAM usage by 2.4%.

#### 2.3 jemalloc: Sigmoidal Dirty/Muzzy Decay and HugePage Allocator (`hpa`)

Basis: source + documentation

`jemalloc` (`jemalloc/jemalloc` @ `91de8ca2d405`) combines per-thread `tcache` bins (`include/jemalloc/internal/tcache.h`), sharded `arena`s (`arena.h`), out-of-band extent metadata (`emap`), and two distinctive OS-reclamation mechanisms:
1. **Smoothstep Two-Stage Decay (`src/decay.c` L16–43):** Freed extents transition from *active* to *dirty* (immediately reusable, zero page-fault cost), then after `dirty_decay_ms` to *muzzy* (released lazily via `MADV_FREE` where supported, staying mapped until kernel memory pressure reclaims them), and finally after `muzzy_decay_ms` to *retained* (deterministically purged via `MADV_DONTNEED`). Rather than purging in abrupt cliffs, `decay_interval_init` divides `decay_ms` by `SMOOTHSTEP_NSTEPS` (L34) and applies jittered deadlines (`decay_deadline_init`, L16–27) so unused pages decay smoothly along a cubic smoothstep backlog curve.
2. **HugePage Allocator (`include/jemalloc/internal/hpa.h` L25–51, `src/hpa.c`):** Mirrors Temeraire's goal inside jemalloc via `psset` (pageslab sets), tracking explicit `npurge_passes`, `npurges`, `nhugifies`, and `nhugify_failures` to pack small/medium extents into 2 MiB pageslabs and call `MADV_HUGEPAGE` once slab density crosses the hugification threshold.

---

### 3. Type-Isolated and Hardware-Tagged Hardened Allocators: Apple `kalloc_type` / `xzone` and LLVM Scudo + ARM MTE

Size-segregated allocators are inherently type-blind: freeing a 64-byte control struct with function pointers allows an attacker to spray a 64-byte user-controlled byte buffer into the exact same slot, turning a dangling pointer into arbitrary read/write or code execution. Hardened production allocators counter this via *type segregation* (Apple) and *hardware memory tagging* (ARM MTE in Scudo and Apple `xzone`).

#### 3.1 Apple XNU `kalloc_type`: 8-Byte Granule Structural Type Signatures

Basis: source + documentation

In `apple-oss-distributions/xnu` (`f6217f891ac0`, `osfmk/kern/kalloc.h` L255–815), `kalloc_type` shifts heap isolation from size classes to **structural memory-layout compatibility**:

1. **8-Byte Granule Classification (`kt_granule_t`, `kalloc.h` L722–749):** Clang's `__builtin_xnu_type_signature(T)` and `__builtin_xnu_type_summary(T)` partition any C/C++ type `T` into 8-byte granules and bitwise-OR member categories within each granule:
   - `KT_GRANULE_PADDING = 0` (struct padding)
   - `KT_GRANULE_POINTER = 1` (raw pointer)
   - `KT_GRANULE_DATA = 2` (non-pointer scalar data)
   - `KT_GRANULE_DUAL = 4` (reserved/currently unused)
   - `KT_GRANULE_PAC = 8` (pointer subject to ARM Pointer Authentication)
2. **Data-Only vs. Pointer Segregation (`kalloc.h` L764–813):** `KT_SUMMARY_GRANULES(type)` extracts a 16-bit summary bitmask where bit `1 << g` indicates presence of granule class `g`. Types matching `KT_SUMMARY_MASK_DATA` (`PADDING | DATA` only, zero pointers) receive `KT_DATA_ONLY = 0x0008` (L304) and are routed strictly to dedicated data-only zones—making it structurally impossible for user-controlled raw byte arrays to reclaim a freed slot from any pointer-bearing kernel object (`struct kalloc_type_view`, L336–343). Pointer-bearing types are further hashed by their exact granule layout signature into randomized fixed-size/variable-size `kalloc.type.*` zones so distinct pointer layouts cannot cross-alias.

#### 3.2 Apple `libmalloc` `xzone`: Bucketed Userspace Type Isolation, Allocation Fronts, and Guard Objects

Basis: source + documentation

In `apple-oss-distributions/libmalloc` (`c49dafa25f1e`, `doc/xzone_malloc.md` L1–230, `include/malloc/_malloc_type.h` L30–72), Apple extends type-isolated heap design to general-purpose userspace (`Memory Integrity Enforcement`) while bounding fragmentation across diverse applications:

1. **Typed Memory Operations (`_malloc_type.h`, `xzone_malloc.md` L40–55):** Clang rewrites standard C `malloc`/`calloc`/`realloc`/`free` calls and C++ `operator new` into `malloc_type_*` entrypoints carrying a 64-bit `malloc_type_id_t` descriptor (Objective-C and Swift runtimes synthesize descriptors directly; untyped legacy call sites fall back to the caller program counter as a type proxy).
2. **Bucketed Partitioning & Boot-Stable Entropy (`xzone_malloc.md` L56–75):** Rather than allocating one isolated slab per distinct C type (which would explode fragmentation), `xzone` partitions each size class into:
   - a dedicated **pure-data** bucket (no pointers),
   - a dedicated **Objective-C object** bucket, and
   - **1 to 4 general ("pointer") buckets**, assigned randomly per type using entropy that is *stable across restarts of the same binary within a boot*—explicitly defeating crash-and-retry attacks that attempt to re-roll favorable bucket collisions.
   - Virtual addresses for a given `(size, bucket)` pair remain permanently isolated from all other buckets for the lifetime of the process.
3. **Anti-Fragmentation Escape Hatch (`Early allocator`, L76–85):** The first $N$ allocations of a lightly used bucket are served from a compact shared early allocator that intentionally foregoes type isolation to prevent cold-start memory blowup.
4. **Spatial & Metadata Hardening (`xzone_malloc.md` L87–180):**
   - *Zero-on-free:* blocks $\le 1\text{ KiB}$ are unconditionally zeroed on `free()` to curb uninitialized-memory info leaks.
   - *Externalized metadata + PAC free lists:* almost all chunk/slice metadata (`16 KiB` OS slices) resides at randomized out-of-band addresses; the sole inline metadata—free-list next pointers—are ARM PAC-signed with a **sequence number** to thwart pointer replay attacks (L99–103).
   - *Allocation fronts (L114–121):* buckets are partitioned into two groups growing in opposite virtual-address directions so an attacker cannot reliably arrange spatial `A-before-B` adjacency between two types in different buckets.
   - *ARM MTE policy split (L123–152):* blocks $\le 4\text{ KiB}$ are **retagged on free** (catching UAF immediately before reallocation); blocks $4\text{ KiB} < s \le 32\text{ KiB}$ are **retagged on alloc** (saving tagging bandwidth on large frees; still prevents cross-object UAF type confusion, though permitting pre-reuse scratch UAF); **pure-data allocations are NOT MTE-tagged by default** unless opted in via the `com.apple.security.hardened-process.checked-allocations.enable-pure-data` entitlement (L149–151, L214–216).
   - *Guard objects (`> 32 KiB`, L153–180):* slabs of power-of-2 slots where a randomized fraction of slots are mapped `mprotect(PROT_NONE)` and reshuffled as objects allocate and free.

#### 3.3 LLVM Scudo Standalone and the Quantitative ARM MTE Odd-Even vs. Uniform Trade-Off

Basis: source + execution

LLVM's `Scudo` (`llvm/llvm-project` @ `16ee29de0984`, `compiler-rt/lib/scudo/standalone/`) is Android's production hardened allocator. Source inspection pins four concrete invariants:

1. **Checksummed 64-Bit Atomic Chunk Headers (`chunk.h` L55–158):** Every allocation is preceded by an aligned 64-bit `AtomicPackedHeader` (`UnpackedHeader`: `ClassId:8`, `State:2` $\in \{\text{Available}=0, \text{Allocated}=1, \text{Quarantined}=2\}$, `OriginOrWasZeroed:2` $\in \{\text{Malloc}=0, \text{New}=1, \text{NewArray}=2, \text{Memalign}=3\}$, `SizeOrUnusedBytes:20`, `Offset:16`, `Checksum:16`). `computeHeaderChecksum` hashes `(Cookie, Ptr, Header)` via hardware CRC32 (`CRC32_INTRINSIC`, folded `Crc ^ (Crc >> 16)`) or software BSD checksum. Because only 2 bits store `Origin`, Scudo explicitly documents (`chunk.h` L66–68) that it **cannot** verify aligned `operator new` vs. aligned `operator delete` mismatches.
2. **Delayed Quarantine (`quarantine.h`):** Freed chunks enter per-thread and global FIFO `QuarantineBatch` lists (`State = Quarantined`) up to a configured byte budget before recycling into `SizeClassAllocator64`'s randomized free-list shuffle batches (`primary64.h`), turning immediate UAFs into double-free/quarantine detections at bounded RSS cost.
3. **ARM MTE Tag Mechanics (`memtag.h` L36–180, `combined.h` L360–371 & L830–835):**
   - ARMv8.5-A MTE assigns a 4-bit allocation tag to each 16-byte granule and embeds the 4-bit logical pointer tag in bits `[59:56]` under Top-Byte Ignore (`untagPointer`: `Ptr & ((1ULL << 56) - 1)`).
   - Tag `0` is permanently reserved as the untagged/wild/metadata tag: `selectRandomTag` executes `ExcludeMask |= 1` (L155) before the `irg` instruction (and `prctl(PR_SET_TAGGED_ADDR_CTRL, ... | (0xfffe << PR_MTE_TAG_SHIFT))` at L106).
   - When `OptionBit::UseOddEvenTags` is enabled (`M_MEMTAG_TUNING_BUFFER_OVERFLOW`, `combined.h` L831–832), `computeOddEvenMaskForPointerMaybe` computes (`combined.h` L370):
     $$\text{ExcludeMask}_{\text{parity}} = \texttt{0x5555} \ll \Bigl(\bigl(\text{Ptr} \gg \text{ctz}(\text{ClassSize})\bigr) \mathbin{\&} 1\Bigr)$$
     Because consecutive blocks of size `ClassSize` flip bit `ctz(ClassSize)` in `010101...` alternation, adjacent blocks receive disjoint tag parities.
4. **Executable Micro-Probe 2B — Exact MTE Parity vs. UAF Collision Quantification:** Reproducing `combined.h` L370 and `memtag.h` L155 verbatim in Python establishes the exact asymmetry caused by excluding Tag `0`:
   - **Uniform mode (`M_MEMTAG_TUNING_UAF`, `UseOddEvenTags = false`):** 15 usable tags `{1..15}`.
     - 1-slot linear buffer overflow detection: $14/15 = \mathbf{93.33\%}$ (6.67% silent miss).
     - Temporal UAF tag collision: **0.00%** on 1st reuse (previous tag excluded via `irg`), **$1/14 = 7.14\%$** on 2nd reuse (stationary $1/15 = 6.67\%$).
   - **Odd-Even mode (`M_MEMTAG_TUNING_BUFFER_OVERFLOW`, `UseOddEvenTags = true`):**
     - Parity-0 slots (`exclude = 0x5555`): **8** usable odd tags `{1, 3, 5, 7, 9, 11, 13, 15}`.
     - Parity-1 slots (`exclude = 0xAAAA | 1 = 0xAAAB`): only **7** usable non-zero even tags `{2, 4, 6, 8, 10, 12, 14}`!
     - 1-slot linear buffer overflow detection: **100.00% deterministic** (disjoint sets).
     - Temporal UAF tag collision: **0.00%** on 1st reuse, but on 2nd reuse **`1/7 = 14.29%`** (parity-0 slots) and **`1/6 = 16.67%`** (parity-1 slots)—a mean 2nd-reuse UAF collision rate of **15.48%**, which is **2.17× higher** than uniform mode! (And stationary UAF collision rises from 6.67% to 12.50% / 14.29%.)

---

### 4. Deterministic Temporal-Safety Quarantines: MarkUs (GC-Swept) vs. FFMalloc (One-Time Virtual Pages) and TLB/VMA Costs

Probabilistic MTE tagging (4 bits) and bounded FIFO quarantines cannot guarantee zero temporal reuse against an attacker with an arbitrary heap-spray or tag-oracle primitive. Two distinct architectural paradigms achieve *deterministic* UAF-reallocation immunity: conservative pointer-swept quarantine (`MarkUs`) and one-time virtual-page allocation (`FFMalloc`).

#### 4.1 MarkUs: Conservative GC-Swept Quarantine Without Automatic Collection

Basis: source + documentation

`MarkUs` (`SamAinsworth/MarkUs-sp2020` @ `60690b9a1421`; `Ainsworth & Jones, IEEE S&P 2020`, DOI `10.1109/SP40000.2020.00058`) modifies the Boehm-Demers-Weiser conservative garbage collector (`bdwgc-markus`) to decouple *when the programmer frees memory* from *when an address becomes safe to reuse*:

1. **Quarantine Insertion (`bdwgc-markus/malloc.c` L603–608):** Under `#if FREEING_LIST` (default `1` in `include/private/freeing_list.h` L41), `GC_free(p)` diverts directly to `GC_safe_free(p)`, placing `p` onto a quarantine freeing list rather than returning it to allocation free lists. Crucially, live objects that the programmer has *not* passed to `free()` are **never** collected, preserving deterministic manual lifetime semantics (and avoiding premature reclamation bugs if an application temporarily obscures a live pointer).
2. **Self-Reference Evasion (`bdwgc-markus/freeing_list.c` L39–90):** Because the conservative GC scans globals and heap memory for word-aligned values pointing into the heap, storing raw pointers in `flink_head`/`flink_tail` would cause the conservative marker to treat MarkUs's own quarantine metadata as live dangling pointers! `freeing_list.c` masks quarantine list pointers with `#define XOR (1ul << 52)` (`write_flink_head` / `read_flink_head`), rendering them non-canonical / out-of-heap to the conservative scanner.
3. **Adaptive Mark Trigger (`include/private/freeing_list.h` L60–62, `alloc.c` L630):** MarkUs invokes a conservative mark phase over thread registers, stacks, static data, and live heap whenever `WALK_GC_FREEING_LIST` holds:
   $$4 \cdot (\text{freeing\_list\_size} + \text{freeing\_link\_size} - \text{failed\_frees}) > (\text{GC\_heapsize} - \text{unmapped})$$
   (i.e., reclaimable quarantined bytes exceed 25% of mapped heap—subtracting `failed_frees` so genuinely leaked dangling pointers do not induce infinite GC thrashing—or `big_sections > 8 * (GC_heapsize - unmapped)`). After marking, *only* quarantined objects whose mark bit remains `0` (zero reachable pointers anywhere in the address space) are swept back to allocation free lists; quarantined objects still referenced by a dangling pointer stay quarantined (`failed_frees`), preventing type-confusion reallocation.
4. **Structural Limitations:** Conservative marking relies on the assumption that dangling pointers remain intact, aligned, unencoded bit patterns inside scanned memory; XOR-encoded pointers, tagged/compressed handles, or pointers stashed in kernel buffers (`epoll`/`io_uring` `user_data`) evade scanning and permit premature reuse. Conversely, arbitrary integer data matching a quarantined address causes false retention, and stop-the-world conservative mark pauses degrade tail latency in large-heap services.

#### 4.2 FFMalloc: One-Time Virtual-Page Allocation, Batch `munmap`, and Linux VMA / TLB-Shootdown Costs

Basis: source + execution + documentation

`FFMalloc` (`bwickman97/ffmalloc` @ `2f24ecf72888`; `Wickman et al., USENIX Security 2021`) eliminates the need for pointer scanning altogether via **One-Time Allocation (OTA)**: every allocation receives a fresh virtual address from a monotonically advancing 48-bit address space (`poolHighWater`, `ffmalloc.c` L692), and *no virtual address is ever reassigned to a later allocation*. Physical RAM is reclaimed only when **every** object allocated on a 4 KiB page has been freed.

Direct source inspection of `ffmalloc.c` reveals the exact virtual-memory engineering required to keep OTA viable on Linux—and its sharp scaling cliffs:

1. **Address-Space and Bin Architecture (`ffmalloc.c` L99–215, L345–442):**
   - Virtual memory is carved in `POOL_SIZE = 4 MiB` (`1 << 22`, L99–100) pools indexed by an out-of-band 3-level 48-bit radix tree (`ROOT_BITS = 8`, `STEM_BITS = 8`, `LEAF_BITS = 10`, L139–149). Thread caches refill `PAGES_PER_REFILL = 128` pages (512 KiB) at a time (L111).
   - Default 16-byte alignment defines `BIN_COUNT = 32` small bins: 16-byte spacing up to 304 B, then maximal page-packing sizes (`PAGE_SIZE / SIZE`) above 304 B (L196–214). Within each page, allocations bump forward linearly without free-list reuse; freed slots are recorded in an out-of-band bitmap referenced by `struct pagemap_t`.
2. **Coalesced Batch `munmap` and VMA-Exhaustion Recovery (`ffmalloc.c` L113–118, L706–711, L2002–2084):**
   - `pagemap_t->allocSize` encodes page lifecycle in its low 3 bits: `5` = page exhausted and all slots freed, awaiting OS return; `7` (`|= 2UL`) = page returned to OS.
   - When the last live slot on a page is freed, `free_page` scans left and right contiguous neighbors in state `5` (L2016–2060) and calls `os_decommit` iff either (a) the contiguous freed run meets `MIN_PAGES_TO_FREE = 8` (32 KiB), **or** (b) `leftIsFreed != 0 && rightIsFreed != 0` (the freed run forms an "island" connecting two already-unmapped holes, so unmapping it *merges* the holes and **reduces** total Linux VMA count!).
   - Critically, `os_decommit` (`ffmalloc.c` L706–711) calls `munmap(startAddress, size)` (explicitly commenting out `madvise(..., MADV_FREE)`), and lines 2067–2072 specifically catch `errno == ENOMEM`:
     ```c
     if (os_decommit((void*)startAddress, endAddress - startAddress) == FALSE) {
         if (errno == ENOMEM) {
             // Likely out of VMAs. Don't die here - continue on in the hopes that
             // more frees will allow VMAs to retire completely
             FFLeaveCriticalSection(&pool->poolLock);
             return;
         }
     ```
   - **Security vs. Kernel VMA/TLB Cost:** Using `munmap` rather than `madvise(MADV_DONTNEED)` provides deterministic `SIGSEGV` crash-on-UAF after a page is reclaimed (whereas `MADV_DONTNEED` leaves the VMA mapped and silently demand-zero-faults a fresh physical page upon dangling dereference!). However, each `munmap` acquires the kernel `mmap_lock` write lock, splits a VMA when punching an interior hole (counting against `vm.max_map_count`, default 65,530 on stock Linux), and broadcasts cross-core **TLB shootdown IPIs** to all active threads sharing the `mm_struct`.
3. **Executable Micro-Probe 2C — Live Linux VMA-Splitting and Syscall Latency Measurement:** Executing a compiled C probe (`gcc -O2`) over an 8 MiB anonymous pool (2048 × 4 KiB pages, all touched to populate PTEs) on a Linux x86-64 host (kernel 7.1.x, 4 KiB pages) measured:
   - **Alternating 1-page `munmap` (1024 calls, worst-case unbatched OTA):** `delta_VMAs = +1023` (`25 -> 1048`), wall time **`15.955 ms`** (~15.6 µs/call single-threaded; scales sharply worse under multi-core `mmap_lock` contention and cross-core TLB shootdown IPIs). Extrapolated to stock `vm.max_map_count = 65,530`, just ~512 MiB of alternating-page OTA fragmentation exhausts the entire process VMA table.
   - **Batched 8-page `munmap` (`MIN_PAGES_TO_FREE = 8`, 128 calls):** `delta_VMAs = +127` (`25 -> 152`), wall time **`1.365 ms`** (**11.7× faster** and **8× fewer VMAs** than 1-page `munmap`).
   - **Alternating 1-page `madvise(MADV_DONTNEED)` (1024 calls):** `delta_VMAs = +0` (`25 -> 25`), wall time **`6.816 ms`** (**2.34× faster** than 1-page `munmap` with zero VMA splitting, at the security cost of losing post-reclaim `SIGSEGV` trapping).
4. **Executable Micro-Probe 2A — OTA Physical Page-Pinning Amplification:** Because OTA can never compact or reuse freed slots within a partially live 4 KiB page, a single long-lived object surviving per page permanently pins all remaining bytes on that page in physical RAM:
   - `16 B` objects (256 slots/page): up to **$256\times$ physical RSS amplification** (99.6% freed -> 0 pages reclaimed).
   - `64 B` objects (64 slots/page): up to **$64\times$ RSS amplification**.
   - `256 B` objects (16 slots/page): up to **$16\times$ RSS amplification**.
   - `512 B` objects (8 slots/page): up to **$8\times$ RSS amplification**.
   In long-running servers with mixed short-lived/long-lived object lifetimes in the same size bin, OTA requires either lifetime segregation (grouping objects by expected lifetime) or bounded virtual-space/RSS budgets.

---

### 5. Fragmentation Lower Bounds (Robson) and Separation-Logic Specifications for Slab/Free-List Allocators

#### 5.1 Robson Worst-Case Fragmentation Bounds

Basis: normative + execution

Robson (`Bounds for Some Functions Concerning Dynamic Storage Allocation`, JACM 1974, DOI `10.1145/321832.321846`) proved an information-theoretic lower bound on **external fragmentation** for *any* non-moving dynamic storage allocator: if the allocator serves object sizes in $\{1, \dots, n\}$ and total simultaneously live memory never exceeds $M$, there exists an adversarial allocation/deallocation sequence forcing peak heap consumption:
$$N(M, n) \ge M \cdot \left(\frac{1}{2}\log_2 n + 1\right) \quad \text{(for powers of two } n = 2^k\text{)}$$
(and asymptotically $\Theta(M \log n)$ for arbitrary integer sizes in $[1, n]$).

**Executable Micro-Probe 2A** simulated Robson's hitting-set adversarial workload (iteratively allocating size $s = 1, 2, 4, \dots, 2^k$, freeing maximal subsets while retaining one pinning block every $< s$ bytes to prevent any size-$s$ placement in existing gaps) at live cap $M = 1024$ against both first-fit and best-fit allocators:
- $n = 8$: first-fit `2560` (**`2.50x M`**), best-fit `2560` (**`2.50x M`**), Robson lower bound = **`2.50x`**.
- $n = 32$: first-fit `3584` (**`3.50x M`**), best-fit `3584` (**`3.50x M`**), Robson lower bound = **`3.50x`**.
- $n = 128$: first-fit `4608` (**`4.50x M`**), best-fit `4608` (**`4.50x M`**), Robson lower bound = **`4.50x`**.
- $n = 256$: first-fit `5120` (**`5.00x M`**), best-fit `5120` (**`5.00x M`**), Robson lower bound = **`5.00x`**.

Consequence for allocator design: segregated size-class slabs (`mimalloc`, `TCMalloc`, `jemalloc`, `Scudo`, `xzone`) cannot beat Robson's $\Omega(\log n)$ external fragmentation barrier across adversarial multi-size workloads—instead, they trade bounded *internal* fragmentation ($\le 12.5\%$ for ~8 sub-classes per power of 2 in `mimalloc`/`TCMalloc`) plus per-class slab pinning for $O(1)$ deterministic fast paths. Adding $B$ type-isolation buckets (`kalloc_type`/`xzone`) multiplies slab-pinning slack by up to $B\times$ unless lightly used buckets share an early allocator.

#### 5.2 Iris Separation-Logic Specifications for Slab and Free-List Recycling

Basis: normative + documentation + derived

Formally verifying a real-world slab/free-list allocator in higher-order concurrent separation logic (`Iris`, `Jung et al., JFP 2018`, DOI `10.1017/S0956796818000151`) requires solving four specification challenges absent from toy garbage-collected languages:

1. **Client-Facing Abstract Specification (Ownership + Non-Duplicable Provenance Token):**
   A reusable Hoare triple for `malloc` / `free` must separate raw byte memory ownership from allocator-private metadata provenance so clients cannot forge `free(p + 8)` or execute a double-free:
   $$\begin{aligned}
   &\{\, \text{True} \,\}\ \texttt{malloc}(n)\ \{\, p.\ (p = \texttt{NULL}) \lor (\text{alloc\_token}(p, n) * p \mapsto_{\text{bytes}} \vec{u} * |\vec{u}| = n * \text{aligned}(p, A)) \,\} \\
   &\{\, \text{alloc\_token}(p, n) * p \mapsto_{\text{bytes}} \vec{u} * |\vec{u}| = n \,\}\ \texttt{free}(p)\ \{\, \text{True} \,\}
   \end{aligned}$$
   Because `alloc_token(p, n)` is an *affine/linear* (non-duplicable, non-persistent) Iris ghost resource—typically a fragmental element $\bigcirc\{p \mapsto_{\text{excl}} (\text{slab\_id}, \text{class\_id}, n)\}$ tied to an authoritative slab map $\bullet M$—consuming it on `free(p)` makes double-free and interior-pointer free statically unprovable in any verified client.

2. **Intrusive Free-List Type-Punning Invariant (Slab Recycling):**
   Inside a slab page $P$ of block size $S \ge \texttt{sizeof(void*)}$ holding $K$ slots $\{b_0, \dots, b_{K-1}\}$, each free slot repurposes its first word to store the intrusive `next` pointer (or XOR-encoded `next ^ key` in `mimalloc`). The Iris slab invariant $\mathcal{I}_{\text{slab}}(P)$ maintains a ghost partition $S_{\text{all}} = S_{\text{free}} \uplus S_{\text{live}}$ (or $S_{\text{free}} \uplus S_{\text{local}} \uplus S_{\text{thread}} \uplus S_{\text{live}}$ for `mimalloc`-style triple lists):
   $$\mathcal{I}_{\text{slab}}(P) \triangleq \exists S_{\text{free}}, S_{\text{live}}, \ell_{\text{hd}}.\ \bullet_{\gamma_P} (S_{\text{free}}, S_{\text{live}}) * \text{free\_list}(\ell_{\text{hd}}, S_{\text{free}}, S) * \bigl(\mathop{\scalebox{1.3}{$\ast$}}_{b \in S_{\text{free}}} (b + \texttt{sizeof(void*)}) \mapsto_{\text{bytes}} \vec{w}_b\bigr) * \text{page\_hdr}(P, |S_{\text{live}}|)$$
   - **On `malloc`:** Popping $b = \ell_{\text{hd}}$ extracts $b \mapsto \text{next}$ from `free_list`, merges it with the trailing $(S - \texttt{sizeof(void*)})$ bytes into a contiguous raw byte array $b \mapsto_{\text{bytes}} \vec{u}$ (requiring a *byte-level* memory model supporting pointer-to-bytes reinterpretation, as in Cerberus/CompCert/MiniRust), updates authoritative ghost state $\bullet_{\gamma_P}$ to move $b$ from $S_{\text{free}}$ to $S_{\text{live}}$, and mints $\bigcirc_{\gamma_P}\{b \mapsto \text{live}\}$ as the client's `alloc_token(b, S)`.
   - **On `free`:** Surrendering `alloc_token(b, S)` proves $b \in S_{\text{live}}$ via authoritative-fragmental agreement ($\bullet M * \bigcirc\{b \mapsto \text{live}\} \implies M[b] = \text{live}$), splits the raw byte array back into leading pointer word + trailing bytes, writes the intrusive `next` pointer into $b$, and moves $b$ back into $S_{\text{free}}$ (or atomically CAS-pushes into `xthread_free` inside a shared Iris invariant while `free`/`local_free` remain in the owning thread's exclusive non-atomic ghost resource!).

3. **Comparison of Mechanized Allocator Verifications:**

| Verification System | Proof Assistant & Logic | Allocator Architecture Verified | Key Verified Properties | Unverified / Out-of-Scope Frontier |
| :--- | :--- | :--- | :--- | :--- |
| **VST Malloc/Free** (`Appel & Naumann, ISMM 2020`, DOI `10.1145/3381898.3397211`) | Coq + Verifiable C (VST separation logic) | Sequential segregated-bin free-list C allocator | Functional correctness + *resource-aware* non-NULL allocation guarantee refining to POSIX spec | Single-threaded only; no concurrent CAS, `rseq`, MTE, or OS page release |
| **RefinedC `mpool`** (`Sammler et al., PLDI 2021`, DOI `10.1145/3453483.3454036`) | Coq + **Iris** (Caesium C semantics + Lithium automation) | Fixed-size chunk intrusive free-list memory pools (e.g., Hafnium `mpool`) | Memory safety, intrusive free-list ownership transfer, lock-protected concurrency, refinement-type preservation | Assumes sequentially consistent / lock-synchronized C memory model; does not model Linux `rseq` or ARM MTE |
| **StarMalloc** (`Reitz, Fromherz, Protzenko, OOPSLA 2024`, DOI `10.1145/3689773`) | **F\*** + **Steel** (concurrent separation logic, distinct from Iris/Coq) | Production-class concurrent, hardened slab/free-list C allocator | Functional safety, absence of double-free/data races, metadata separation, randomized/quarantined allocation at competitive speed | Extracted via KaRaMeL to C (relies on C compiler / sequential consistency); no `rseq` or hardware MTE |

4. **Open Verification Frontier for Modern Production Allocators:**
   - **Linux `rseq` (`TCMalloc`):** Verifying `percpu_rseq_x86_64.S` requires extending concurrent separation logic with *per-CPU ghost ownership*, kernel-preemption abort semantics over PC intervals `[start, commit)`, and proving that all pre-commit writes land strictly in dead slots invisible to other threads upon preemption abort.
   - **Relaxed Atomics & QSBR (`mimalloc` v3 `MI_QSBR` / `xthread_free`):** `mi_free_block_mt` uses `mi_atomic_load_relaxed` and release/acquire CAS loops plus quiescent-state reclamation (`qsbr.h`), requiring weak-memory Iris logics (`iGPS`, `Cosmo`, or RustBelt relaxed-atomic views) rather than SC `HeapLang`.
   - **ARM MTE Hardware Provenance (`Scudo` / `xzone` / `mimalloc`):** Proving MTE spatial/temporal fault properties requires augmenting points-to predicates with physical granule tags ($\ell^{\tau_{\text{ptr}}} \mapsto_{\tau_{\text{mem}}} v$) where loads/stores assert $\tau_{\text{ptr}} = \tau_{\text{mem}}$ (or $\tau_{\text{ptr}} = 0$ / `TCO = 1`), and proving that `irg`-excluded retagging invalidates dangling capabilities with exact probability $1 - 1/|T_{\text{avail}}|$.

## Boundaries

- **Known not to apply:**
  - `TCMalloc` `rseq` per-CPU caching (`tcmalloc/internal/percpu_rseq_x86_64.S`) applies only to Linux kernels supporting `sys_rseq` ($\ge 4.18$) with ELF TLS `__rseq_abi`; on non-Linux or older kernels, TCMalloc falls back to per-thread caches (`ThreadCache`).
  - Apple `xzone` MTE protection (`apple-oss-distributions/libmalloc` `doc/xzone_malloc.md` L125–152) does not apply to blocks $> 32\text{ KiB}$ (which use `mprotect` guard objects instead) and does not tag pure-data allocations by default without the `enable-pure-data` entitlement; blocks in $(4\text{ KiB}, 32\text{ KiB}]$ are tagged on alloc rather than free, so pre-reuse UAF scratch accesses remain undetected by MTE.
  - `Scudo`'s `UseOddEvenTags` deterministic 1-slot overflow guarantee does not prevent non-linear out-of-bounds accesses (e.g., jumping 2 slots to an identically-paritied neighbor) and degrades 2nd-reuse UAF protection by 2.17× compared to uniform mode (Probe 2B).
  - `MarkUs` conservative GC-swept quarantine does not protect against UAF when dangling pointers are obfuscated (XORed, compressed, or stored outside scanned user memory/registers).
  - `FFMalloc` one-time virtual-page allocation does not prevent spatial intra-page buffer overflows between adjacent slots in the same bin, nor does it prevent physical RSS exhaustion under single-object page pinning (Probe 2A).
  - Robson's $\Omega(M \log n)$ fragmentation lower bound applies strictly to *non-moving* allocators; compacting/moving garbage collectors escape it by relocating live objects.
- **Unsupported:**
  - `LLVM Scudo` (`compiler-rt/lib/scudo/standalone/chunk.h` L66–68) explicitly does not support verifying aligned `operator new`/`new[]` vs. aligned `operator delete`/`delete[]` mismatches due to the 2-bit `Origin` field width.
  - `LLVM Scudo` MTE (`memtag.h` L29–34) is explicitly disabled under `HWASan`, `ASan`, `ILP32`, or `SCUDO_DISABLE_TBI`.
  - Standard sequentially consistent `Iris` (`HeapLang`) does not natively model Linux `rseq` PC-range preemption aborts, ARM MTE hardware tag storage, or C11 relaxed-atomic `QSBR` without specialized language semantics and weak-memory logic extensions.
- **Not examined:**
  - Full-application runtime throughput benchmarks across SPEC / warehouse-scale traces for `mimalloc` v3, `TCMalloc`, `jemalloc`, `xzone`, `Scudo`, `MarkUs`, and `FFMalloc` were not re-executed; performance figures cited for `TCMalloc` Temeraire originate from Hunter et al. (OSDI 2021).
  - Multi-threaded cross-core TLB shootdown IPI latency scaling under Linux `munmap` (e.g., 64-core contention on `mmap_lock`) was not benchmarked directly; Probe 2C measured single-threaded VMA splitting and syscall latency only.
  - Apple `xnu` `zalloc.c` guard-object reshuffling heuristics (`osfmk/kern/zalloc.c`) and `libmalloc` `xzone_malloc.c` internal span/segment-group state machine (308 KiB source file) were not audited line by line beyond the documented architecture (`doc/xzone_malloc.md`) and public type headers.
  - CHERI hardware capability allocators (e.g., `Cornucopia` / `Cornucopia Reloaded` temporal capability revocation) and Rust-specific allocators (`talc`, `rpmalloc`, `snmalloc` message-passing frees) were not examined.
- **Unknown:**
  - Exact multi-core tail-latency cliff of `FFMalloc`'s `ENOMEM` VMA-exhaustion fallback (`ffmalloc.c` L2067–2072) under sustained production workloads with default Linux `vm.max_map_count = 65,530` when island merges fail to keep pace with alternating-page frees.
  - Practical empirical UAF exploitation bypass rate of Apple `xzone`'s 1–4 general pointer buckets combined with boot-stable entropy and the shared early allocator across real-world browser/media threat models.

## Evidence

### Primary Git Source Citations (Observed 2026-11-19)

- **`microsoft/mimalloc` @ `1d8fd85aa3abe719cd9c42c855f1fc27dbccf84d` (`main3`):**
  - `include/mimalloc/types.h` L127–162 (`MI_GUARDED`, `MI_PADDING`, `MI_PADDING_CHECK_BYTES`, `MI_ENCODE_FREELIST` tied to `MI_SECURE` levels), L485–561 (`struct mi_page_s`: `free`, `local_free`, `xthread_free` ownership bit, `xused`, `keys[2]`, `block_recip`, `MI_QSBR` fields), L575–588 (cache-set offsets and max object sizes).
  - `src/alloc/free.c` L124–146 (`mi_free_block_mt` atomic CAS push to `xthread_free`), L165–176 (`mi_page_block_index` Lemire `mi_mul_hi64_32` reciprocal division).
  - `include/mimalloc/prim/prim-mte.h` L15–25 (ARM MTE 4-bit tags in bits 56–59, `mi_memtag_exclude_adjacent` neighbor tag exclusion).
- **`google/tcmalloc` @ `9c3ddad744bc28174d173af47a341e76423e3659`:**
  - `tcmalloc/internal/percpu_rseq_x86_64.S` L23–118 (`DEFINE_UPSTREAM_CS`, `SIGN_ABORT()` `0x0f 0x1f 0x05 + TCMALLOC_PERCPU_RSEQ_SIGNATURE`), L135–162 (`START_RSEQ`, `FETCH_SLABS`), L214–230 (restartable register-clobber ABI), L258–360 (`TcmallocSlab_Internal_PushBatch` and `PopBatch` single-store `[current:16, remaining_capacity:16]` commit).
  - `tcmalloc/huge_page_filler.h` L96–98 (`kDenseRegular`, `kDonated`, `kSparsePartialReleased`), L508–524 (`class HugePageFiller`), L635–637 (`GetDesiredSubreleasePages`, `SkipSubreleaseIntervals`).
- **`jemalloc/jemalloc` @ `91de8ca2d405ed5ccee49172418ef68e35c954a4`:**
  - `src/decay.c` L16–43 (`decay_deadline_init` jitter, `decay_interval_init` dividing `decay_ms` by `SMOOTHSTEP_NSTEPS`, `decay_reinit`).
  - `include/jemalloc/internal/hpa.h` L13–51 (`psset.h`, `hpa_shard_nonderived_stats_s`: `npurge_passes`, `npurges`, `nhugifies`, `nhugify_failures`).
- **`apple-oss-distributions/xnu` @ `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`:**
  - `osfmk/kern/kalloc.h` L255–349 (`KT_DATA_ONLY = 0x0008`, `struct kalloc_type_view`), L720–814 (`__builtin_xnu_type_signature`, `kt_granule_t` 8-byte granule encodings `PADDING=0, POINTER=1, DATA=2, DUAL=4, PAC=8`, `KT_SUMMARY_MASK_DATA`, `KT_SUMMARY_MASK_PTR`, `KALLOC_TYPE_SIG_CHECK`).
- **`apple-oss-distributions/libmalloc` @ `c49dafa25f1efe8607701ae6014a663ad2ee437f`:**
  - `doc/xzone_malloc.md` L1–230 (bucketed type isolation, boot-stable entropy, early allocator, zero-on-free $\le 1\text{ KiB}$, externalized metadata + PAC-signed sequence-numbered free lists, probabilistic guard pages, allocation fronts, MTE $\le 4\text{ KiB}$ tag-on-free / $\le 32\text{ KiB}$ tag-on-alloc / odd-even / pure-data entitlement, guard objects $> 32\text{ KiB}$, 16 KiB slices).
  - `include/malloc/_malloc_type.h` L30–72 (`malloc_type_id_t`, `malloc_type_malloc`/`calloc`/`free`/`realloc`).
- **`llvm/llvm-project` @ `16ee29de098406eb6491878ff70f204a06c7b998`:**
  - `compiler-rt/lib/scudo/standalone/chunk.h` L23–158 (`computeChecksum` CRC32/BSD, `Origin`, `State`, 64-bit `UnpackedHeader`, L66–68 aligned `new`/`delete` verification gap, `storeHeader`/`loadHeader`).
  - `compiler-rt/lib/scudo/standalone/memtag.h` L29–40 (TBI/HWASan/ASan gates, 16 B granule, bits `[59:56]`), L104–108 (`0xfffe << PR_MTE_TAG_SHIFT`), L154–165 (`selectRandomTag` with `ExcludeMask |= 1` and `irg`).
  - `compiler-rt/lib/scudo/standalone/combined.h` L360–371 (`computeOddEvenMaskForPointerMaybe`: `0x5555U << ((Ptr >> LSB) & 1)`), L830–835 (`M_MEMTAG_TUNING_BUFFER_OVERFLOW` vs. `M_MEMTAG_TUNING_UAF`).
  - `compiler-rt/lib/scudo/standalone/quarantine.h`: `GlobalQuarantine`, `QuarantineBatch`.
- **`SamAinsworth/MarkUs-sp2020` @ `60690b9a1421c0792d04088f0fa173e5f6d406ca`:**
  - `bdwgc-markus/malloc.c` L603–608 (`GC_free` -> `GC_safe_free` under `FREEING_LIST`).
  - `bdwgc-markus/freeing_list.c` L39–90 (`#define XOR (1ul<<52)` pointer masking on `flink_head`/`flink_tail`).
  - `bdwgc-markus/include/private/freeing_list.h` L40–63 (`FREEING_LIST`, `BIGSECTION`, `WALK_GC_FREEING_LIST` 25% quarantine threshold discounting `failed_frees`).
  - `bdwgc-markus/alloc.c` L625–675 (`GC_collect_a_little_inner` gated on `WALK_GC_FREEING_LIST`).
- **`bwickman97/ffmalloc` @ `2f24ecf728886dc0ea29b5f2adab2df9c881befa`:**
  - `ffmalloc.c` L99–150 (`POOL_SIZE = 1<<22`, `PAGES_PER_REFILL = 128`, `MIN_PAGES_TO_FREE = 8`, 48-bit 3-level radix tree `ROOT_BITS=8, STEM_BITS=8, LEAF_BITS=10`), L196–215 (16 B default alignment, `BIN_COUNT = 32`), L690–729 (`poolHighWater`, `os_decommit` calling `munmap` with `madvise(MADV_FREE)` commented out at L710), L2002–2084 (`free_page` contiguous scan, `MIN_PAGES_TO_FREE` / `leftIsFreed && rightIsFreed` island-merge rule, `errno == ENOMEM` VMA-exhaustion handler).

### Primary Peer-Reviewed Literature Citations

- Robson (JACM 1974): *Bounds for Some Functions Concerning Dynamic Storage Allocation*, DOI `10.1145/321832.321846`.
- Leijen, Zorn, de Moura (APLAS 2019): *Mimalloc: Free List Sharding in Action*, DOI `10.1007/978-3-030-34175-6_13`.
- Hunter, Kennelly, Turner, Gove, Moseley, Ranganathan (USENIX OSDI 2021): *Beyond malloc efficiency to fleet efficiency: a hugepage-aware memory allocator*.
- Ainsworth, Jones (IEEE S&P 2020): *MarkUs: Drop-in use-after-free prevention for low-level languages*, DOI `10.1109/SP40000.2020.00058`.
- Wickman, Hu, Yun, Jang, Lim, Kashyap, Kim (USENIX Security 2021): *Preventing Use-After-Free Attacks with Fast Forward Allocation*.
- Jung, Krebbers, Jourdan, Bizjak, Birkedal, Dreyer (JFP 2018): *Iris from the ground up: A modular foundation for higher-order concurrent separation logic*, DOI `10.1017/S0956796818000151`.
- Appel, Naumann (ISMM 2020): *Verified Sequential Malloc/Free*, DOI `10.1145/3381898.3397211`.
- Sammler, Lepigre, Krebbers, Memarian, Dreyer, Garg (PLDI 2021): *RefinedC: Automating the Foundational Verification of C Code with Refined Ownership Types*, DOI `10.1145/3453483.3454036`.
- Reitz, Fromherz, Protzenko (OOPSLA 2024): *StarMalloc: A Formally Verified, Concurrent, Performant, and Security-Oriented Memory Allocator*, DOI `10.1145/3689773`.

### Reproducible Execution Probes (Observed 2026-11-19)

- **Probe 2A (Robson adversarial fragmentation & OTA page pinning, Python 3.13.15):** Simulating Robson's hitting-set strategy at $M = 1024$ yielded exact lower-bound ratios for both first-fit and best-fit (`n=8 -> 2.50x`, `n=32 -> 3.50x`, `n=128 -> 4.50x`, `n=256 -> 5.00x`). OTA single-object 4 KiB page pinning yielded $256\times$ (16 B), $128\times$ (32 B), $64\times$ (64 B), $32\times$ (128 B), $16\times$ (256 B), and $8\times$ (512 B) physical RSS amplification.
- **Probe 2B (Scudo/xzone MTE odd-even vs. uniform tag space, Python 3.13.15):** Reproducing `ExcludeMask |= 1` and `0x5555 << parity` verified `|T_uniform| = 15`, `|T_parity0| = 8` (`{1,3,5,7,9,11,13,15}`), `|T_parity1| = 7` (`{2,4,6,8,10,12,14}`), 100.00% vs. 93.33% 1-slot linear OOB detection, and 15.48% vs. 7.14% (2.17×) mean 2nd-reuse UAF tag-collision probability.
- **Probe 2C (Linux VMA-splitting and `munmap` vs. `madvise(MADV_DONTNEED)` C probe, `gcc -O2`, Linux x86-64 kernel 7.1.x, 8 MiB = 2048 × 4 KiB pages):**
  - 1-page alternating `munmap` (1024 calls): `delta_VMAs = +1023` (`25 -> 1048`), `15.955 ms`.
  - 8-page batched `munmap` (`MIN_PAGES_TO_FREE = 8`, 128 calls): `delta_VMAs = +127` (`25 -> 152`), `1.365 ms`.
  - 1-page alternating `madvise(MADV_DONTNEED)` (1024 calls): `delta_VMAs = +0` (`25 -> 25`), `6.816 ms`.

## Revalidation

To cheaply revalidate whether the implementation-specific findings in this report still hold on newer allocator or kernel releases:

1. **mimalloc v3 page sharding and MTE:** Diff `microsoft/mimalloc` `include/mimalloc/types.h` (`struct mi_page_s`) and `include/mimalloc/prim/prim-mte.h` against `1d8fd85aa3ab` to check whether triple free-list sharding, `block_recip`, and adjacent-neighbor MTE tag exclusion remain unchanged.
2. **TCMalloc `rseq` ABI and HugePageFiller:** Diff `google/tcmalloc` `tcmalloc/internal/percpu_rseq_x86_64.S` and `tcmalloc/huge_page_filler.h` against `9c3ddad744bc` to verify the 32-bit packed header commit store and `Subrelease` policies.
3. **Apple `kalloc_type` / `xzone` policies:** Inspect `apple-oss-distributions/xnu` `osfmk/kern/kalloc.h` (`kt_granule_t`, `KT_SUMMARY_MASK_DATA`) and `apple-oss-distributions/libmalloc` `doc/xzone_malloc.md` for changes in bucket count, pure-data MTE defaults, or tag-on-free vs. tag-on-alloc size thresholds (4 KiB / 32 KiB).
4. **Scudo chunk header and MTE parity mask:** Check `llvm/llvm-project` `compiler-rt/lib/scudo/standalone/chunk.h` (`UnpackedHeader` bit widths) and `combined.h` (`computeOddEvenMaskForPointerMaybe`) to confirm whether `Origin` remains 2 bits and whether Tag `0` exclusion still yields the 8/7 odd-even asymmetry.
5. **Linux VMA/TLB behavior under OTA reclamation:** Recompile and run Probe 2C (`mmap` 2048 pages, measure `/proc/self/maps` VMA delta and latency across 1-page `munmap`, 8-page `munmap`, and 1-page `MADV_DONTNEED`, plus `cat /proc/sys/vm/max_map_count`) on the target kernel version and multi-core configuration.
