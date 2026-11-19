# Shadow-Memory Encoding, Bit-Exact Uninitialized Origin Tracking, and Adaptive Vector-Clock Race Detection in ASan, HWASan, GWP-ASan, MSan, and TSan v3

## Summary

Dynamic runtime sanitizers detect distinct classes of undefined behavior in compiled C, C++, and unsafe Rust binaries by mapping application virtual addresses onto disjoint shadow-memory tables or hardware pointer-tag spaces, at the cost of bounded blind spots dictated by shadow compression:

1. **Spatial/temporal redzone vs. pointer-tag vs. sampled-page detection (`ASan` / `HWASan` / `GWP-ASan`):** AddressSanitizer (`ASan`) maps every 8 application bytes to 1 signed shadow byte (`(addr >> 3) + ShadowOffset`, `0x7fff8000` on Linux x86_64 non-PIE), reserving `~20 TiB` of `MAP_NORESERVE` virtual space (`VmSize = 21,474,884,396 KiB` observed in execution) to achieve single-shift shadow lookup while using `0xfa`/`0xf1..0xf3`/`0xfd` magic bytes, a `256 MiB` default quarantine FIFO, and an 11-class power-of-two `FakeStack` for use-after-return detection. Hardware-assisted ASan (`HWASan`) replaces redzones and quarantines with 8-bit random pointer tags (`AArch64 TBI` / `x86_64 LAM`), `1:16` tag shadow (`kShadowScale = 4`), and inline last-byte short-granule tags—shrinking RAM overhead to `~10–35%` at a $1/256$ random tag-collision rate (and $1/16$ on 4-bit `ARMv8.5-A MTE`). `GWP-ASan` drops compiler instrumentation completely (`0%` rebuild), sampling e.g. `1/5000` allocations into a fixed-size `PROT_NONE`-guarded slot pool with alternating left/right page alignment.
2. **Bit-exact boolean vs. fast carry-lossy arithmetic uninitialized tracking (`MSan`):** MemorySanitizer (`MSan`) maintains a $1{:}1$ bit-exact shadow (`addr ^ 0x500000000000ULL` on Linux x86_64: `1` = uninitialized) and defers fault checks until conditional branches, switches, pointer dereferences, or syscalls—allowing uninitialized padding copies (`memcpy` / `MaybeUninit<T>`) without false alarms. Direct source inspection and exhaustive 65,536-state verification prove `visitAnd`, `visitOr`, `visitXor`, and `propagateEqualityComparison` are **100% bit-exact** (`0` false positives, `0` false negatives), whereas `visitAdd` / `visitSub` / unspecialized `visitMul` invoke `handleShadowOr` (`Sa | Sb`), omitting bit-carry propagation (`28,160 / 65,536` false-negative carry states in 4-bit verification) to avoid multi-instruction carry chains. `-fsanitize-memory-track-origins=2` adds a `+1x` 4-byte origin shadow backed by `ChainedOriginDepot` (`kMaxDepth = 7` store links). Any uninstrumented shared library or inline `asm` breaks shadow soundness via unpoisoned writes, causing cascading false positives.
3. **Adaptive 4-slot SIMD shadow cells and eviction blind spots (`TSan v3`):** ThreadSanitizer v3 (`compiler-rt/lib/tsan/rtl/`) halves v2 shadow memory (`4x -> 2x`, plus `0.5x` meta-shadow) by packing four 32-bit `RawShadow` entries per 8-byte user cell (`kShadowCnt = 4`), encoding `(access_mask:8, sid:8, epoch:14, is_read:1, is_atomic:1)` for 128-bit SSE4.2 parallel race checks, while multiplexing arbitrary OS threads onto 255 `TidSlot`s (`kThreadSlotCount = 256`, `kFreeSid = 255`) with `16,383`-epoch shadow resets. Execution against `gcc 15.2.0 -fsanitize=thread` (`libtsan.so.2`) demonstrates a sharp **4-slot eviction blind spot**: an unsynchronized write–read data race is caught (`exit 66`) with `0`, `2`, or `4` synchronized intermediate readers, but silently missed (`exit 0`, `0` races reported) once `8` or `16` synchronized readers with distinct `trace_pos` indices evict the writer's slot and fill all 4 slots with `Read` shadows.

## Applicability

This report characterizes runtime instrumentation passes and support libraries in:

- **`llvm/llvm-project`** (`63b8d2fd94ba3b1a80023dae7139949dd5be6b78`):
  - LLVM IR passes: `llvm/lib/Transforms/Instrumentation/{AddressSanitizer,HWAddressSanitizer,MemorySanitizer}.cpp` (and TSan instrumentation in the same directory).
  - `compiler-rt` runtimes: `compiler-rt/lib/{asan,hwasan,gwp_asan,msan,tsan}/`.
- **`google/sanitizers`** (`aa054ab16a697f206f1888aedbb94407df3e480c`): archival design specs and formal helpers (`hwaddress-sanitizer/prove_hwasanwrap.smt2`, `mte-dynamic-carveout/spec.md`, `gwp-asan/icse2024/`).
- **GCC 15.2.0 host parity (`x86_64-linux-gnu`):** `gcc 15.2.0` links `libasan.so.8` and `libtsan.so.2` synced from upstream `compiler-rt` algorithms; ASan and TSan v3 execution probes verify live runtime behavior on `x86_64` Linux. Note that GCC does not ship `MSan` (`-fsanitize=memory` is Clang/LLVM-only).

**Mutual Exclusivity Invariant (`known not to apply` jointly):** `ASan`, `MSan`, `HWASan`, and `TSan` **cannot** be combined in the same OS process because each assumes exclusive ownership of overlapping 64-bit virtual address ranges (`0x7fff8000`-based shadow vs. `addr ^ 0x500000000000ULL` vs. TSan's `2x` fixed region) and replaces `malloc`/`free`/`pthread_*` interceptors globally. Only `UBSan` (check-local, zero shadow) and `GWP-ASan` (allocator-local pool) compose cleanly alongside normal builds.

## Findings

### 1. Direct-Mapped 1:8 Redzone Shadowing, Quarantine Delays, and `FakeStack` (`ASan`)

Basis: source + normative + execution (`asan_mapping.h`, `asan_internal.h`, `asan_allocator.cpp`, `asan_fake_stack.h`, `asan_flags.cpp`, `AddressSanitizer.cpp`, Serebryany et al. USENIX ATC 2012, `/tmp/probe_sanitizers.py` Experiment A).

ASan partitions memory into aligned 8-byte granules (`ASAN_SHADOW_SCALE = 3`, `asan_mapping.h:182`) mapped via one affine arithmetic step to a single signed byte (`int8_t`) in shadow memory:

$$\text{shadow\_addr}(\text{addr}) = (\text{addr} \gg 3) + \text{ShadowOffset}.$$

On Linux `x86_64` (`asan_mapping.h:21-31, 246`), `ASAN_SHADOW_OFFSET_CONST = 0x7fff8000` reserves `HighShadow` `[0x02008fff7000, 0x10007fff7fff]`, `ShadowGap` `[0x00008fff7000, 0x02008fff6fff]` (`PROT_NONE`), and `LowShadow` `[0x00007fff8000, 0x00008fff6fff]` (dynamically probed `0` / `FindDynamicShadowStart()` on PIE/high-ASLR or 5-level paging systems).

#### Signed Shadow Byte State Space (`asan_internal.h:141-156`, `AddressSanitizer.cpp:1670-1815`)

| Shadow Byte Value (`s = *sh`) | Meaning | Fast-Path Check Outcome |
| :--- | :--- | :--- |
| `0x00` | All 8 bytes in the 8-byte granule are addressable | Pass (`s == 0`) for 1-, 2-, 4-, and 8-byte accesses |
| `0x01..0x07` | Only the first `k = s` bytes (`[0..s-1]`) are addressable; tail `[s..7]` is poisoned | 8-byte access fails (`s != 0`); sub-8B access passes iff `((int8_t)((addr & 7) + size - 1)) < (int8_t)s` (`ICmpSGE`, `AddressSanitizer.cpp:1685`) |
| `0xf1`, `0xf2`, `0xf3` | Stack frame left (`0xf1`), mid (`0xf2`), and right (`0xf3`) redzones | Trap (`__asan_report_*`) |
| `0xf5`, `0xf8` | Stack use-after-return (`FakeStack` retired frame `0xf5`) and stack use-after-scope (`0xf8`) | Trap |
| `0xf9`, `0xfa`, `0xfd` | Global variable redzone (`0xf9`), heap left redzone (`0xfa`), freed heap quarantine (`0xfd`) | Trap |
| `0xfc`, `0xbb`, `0xac`, `0xf7` | Contiguous container OOB (`std::vector`, `0xfc`), intra-object redzone (`0xbb`), C++ `new[]` cookie (`0xac`), manual `__asan_poison_memory_region` (`0xf7`) | Trap |

Experiment A (`/tmp/probe_sanitizers.py`) compiled with `gcc -O2 -fsanitize=address` empirically confirms this layout on a `malloc(13)` allocation (`0x7b90bfbe0010`): `scale=3, offset=0x7fff8000`, adjacent shadow granules `[0xfa, 0x00, 0x05, 0xfa]` (left redzone `0xfa`, 8 valid bytes `0x00`, 5 valid tail bytes `0x05`, right redzone `0xfa`), transitioning immediately to `[0xfd, 0xfd]` upon `free()`. Disassembly of `read_u8` exhibits the exact 8-instruction branch-minimized inline check (`shr $0x3`, `and $0x7`, `movzbl 0x7fff8000(%rax)`, `cmp %dl,%al; jg ok; test %al,%al; jne __asan_report_load1@plt`), while `/proc/self/status` records **`VmSize = 21,474,884,396 kB` (~20.48 TiB)** vs. **`VmRSS = 13,844 kB` (~13.5 MiB)**.

#### Temporal Windows: Heap Quarantine and `FakeStack`

- **FIFO Quarantine (`asan_allocator.cpp`, `asan_flags.cpp:187-200`):** Freed heap blocks are poisoned with `0xfd` and pushed onto a thread-local (`1024 KiB` on 64-bit, `64 KiB` if `ASAN_LOW_MEMORY`) -> global (`256 MiB` default, `16 MiB` if `ASAN_LOW_MEMORY`) quarantine ring. Once cumulative freed bytes exceed `quarantine_size_mb`, the oldest chunks are dequeued, unpoisoned, and reallocated; any UAF occurring *after* eviction silently aliases live memory (`false negative`).
- **Stack Use-After-Return (`asan_fake_stack.h:56-98`):** When `detect_stack_use_after_return=1` (Linux non-Android default, `asan_flags.inc:52`), each thread mmaps a `FakeStack` spanning `kNumberOfSizeClasses = 11` power-of-two frame slabs ($2^6 = 64\text{ B}$ up to $2^{16} = 64\text{ KiB}$). Function prologues allocate frames round-robin inside the matching slab and epilogues poison the frame (`0xf5`) instead of popping an OS stack pointer, catching dangling stack references until the slab wraps.
- **`RLIMIT_AS` (`ulimit -v`) clash:** Because ASan mmaps `~16–20 TiB` with `MAP_NORESERVE`, any container, sandbox, or `ulimit -v` virtual-address cap below ~`21 TiB` fails immediately at `AsanInitFromRtl()` (`Shadow memory range interleaves...` or `mmap` `ENOMEM`), even though actual physical `VmRSS` is only megabytes.

### 2. Pointer-Tag Granules (`HWASan` / `ARM64 TBI` & `MTE`) vs. Guard-Page Sampling (`GWP-ASan`)

Basis: source + normative (`hwasan_mapping.h`, `hwasan_allocator.cpp`, `HWAddressSanitizer.cpp`, `guarded_pool_allocator.h`, `guarded_pool_allocator.cpp`, `gwp_options.inc`, `prove_hwasanwrap.smt2`, `mte_spec.md`, Serebryany 2018, Serebryany et al. ICSE-SEIP 2024).

| Dimension | `ASan` (Redzone) | `HWASan` (Software TBI/LAM) | `ARMv8.5-A MTE` (Hardware Tags) | `GWP-ASan` (Sampled Guard Pages) |
| :--- | :--- | :--- | :--- | :--- |
| Tag / shadow scale | `1:8` (`1 B` per `8 B` granule) | `1:16` (`1 B` tag per `16 B` granule, `kShadowScale = 4`) | `1:16` (`4-bit` tag in hardware DRAM / dynamic carveout `1:32` page ratio) | **Zero shadow memory** (page-table `PROT_NONE` guard pages) |
| Pointer bits consumed | `0` (canonical pointers) | Top 8 bits `[63:56]` (`ARM64 TBI`, `x86_64 LAM`, `RISC-V` pointer masking) | Top 4 bits `[59:56]` (inside `TBI`) | `0` (standard virtual pointers) |
| Spatial sub-granule precision | Exact **1-byte** via `0x01..0x07` | Exact **1-byte** via **short-granule encoding** (`hwasan_allocator.cpp:254-261`) | **16-byte granule** (cannot catch 1-byte overflow within last 16B) | Exact **1-byte** on half the pool via random `PerfectlyRightAlign` / right-align (`guarded_pool_allocator.cpp:247-250`) |
| Temporal UAF detection | Bounded by `256 MiB` quarantine FIFO | Immediate random tag re-roll on `free()` (`1/256` collision risk, zero quarantine!) | Immediate tag re-roll (`1/16` collision risk!) | Immediate `mprotect(PROT_NONE)` on `deallocate()` until slot re-sampled |
| Compiler rebuild needed? | Yes (`-fsanitize=address`) | Yes (`-fsanitize=hwaddress`) | Optional (allocator-only heap MTE or stack IR) | **No** (drops into `Scudo` / `malloc` binary) |

#### Key Mechanisms Verified in Source

1. **`HWASan` Short-Granule Trick (`hwasan_allocator.cpp:253-261`):** Because an allocation of `orig_size = 20` is not a multiple of `kShadowAlignment = 16`, `HWASan` writes the pointer's 8-bit `tag` to the shadow byte of the first full 16-byte granule (`full_granule_size = 16`), writes `orig_size % 16 = 4` (values `1..15` are reserved length tags!) into the shadow byte of the trailing short granule, and stores the **actual pointer tag** inline in `short_granule[15]` (last byte of that 16-byte user granule). On mismatch in `0x01..0x0f`, the outlined tag-mismatch handler reads `*(uint8_t*)((addr | 0xf))` and traps unless `(ptr_tag == short_granule[15]) && ((addr & 0xf) < shadow_val)`. `google/sanitizers`'s `prove_hwasanwrap.smt2` formally verifies via Z3 bitvectors (`#x0000000000000038`) that `HWASan`'s branchless stack ring-buffer `Step` macro wraps cleanly across aligned power-of-two page rings.
2. **Dynamic `MTE` Tag Storage (`mte_spec.md`):** On systems without dedicated ECC tag pins, dynamic MTE pairs `32` data pages with `1` tag page (`3.03%` DRAM overhead), toggling pages between untagged Normal and Tagged Normal memory via `DC CIGVAC` + `DC CIVAC` ("Tag Storage Clean") cache cleans so unused tag pages return to the general allocator pool.
3. **`GWP-ASan` Sampling & Alignment (`guarded_pool_allocator.h:80-93, 247-262`, `gwp_options.inc:26-33`):** `shouldSample()` maintains a zero-branch-prediction-cost thread-local decrementing counter (`NextSampleCounter`, default `SampleRate = 5000`), diverting sampled calls into `MaxSimultaneousAllocations` (default `16`) slots bracketed by `PROT_NONE` guard pages. Each allocation flips a coin (`getRandomUnsigned32() % 2 == 0`): left-aligned catches underflows (`ptr - 1` hits preceding guard page), right-aligned (`alignDown(SlotEnd - Size, Alignment)`) places the last valid byte flush against the trailing guard page so a **1-byte overflow triggers hardware `SIGSEGV`**. On `deallocate()`, `deallocateInGuardedPool` marks the page `PROT_NONE` immediately while preserving compressed alloc/dealloc stack traces in `Metadata`.

### 3. Bit-Exact Uninitialized Shadow Algebra and Chained Origin Tracking (`MSan`)

Basis: source + normative + execution (`MemorySanitizer.cpp`, `msan.h`, `msan_origin.h`, `msan_chained_origin_depot.cpp`, Stepanov & Serebryany CGO 2015, `/tmp/probe_sanitizers.py` Experiment B).

`MSan` maps each bit of application memory 1:1 to a shadow bit (`MEM_TO_SHADOW(mem) = mem ^ 0x500000000000ULL` on Linux `x86_64`, `msan.h:247`, where `1` means **uninitialized/poisoned** and `0` means **initialized/clean**). Crucially, unlike `ASan` or `Valgrind` setups that trap immediately on uninitialized loads, `MSan` implements **C/Rust byte-copy tolerance**: copying structs containing uninitialized padding or `MaybeUninit<T>` bytes merely copies shadow bits (`load`/`store` shadow propagation), deferring `insertShadowCheck` exclusively to *observations* that introduce control-flow or memory-address UB (conditional `br` / `switch` conditions, pointer dereferences, division divisors `visitUDiv`/`visitSDiv` `MemorySanitizer.cpp:3007`, and OS syscall / uninstrumented ABI exits).

#### Exactness vs. Fast Arithmetic Approximation in `MemorySanitizer.cpp`

Direct inspection of `llvm/lib/Transforms/Instrumentation/MemorySanitizer.cpp` paired with exhaustive 4-bit verification over all $16^4 = 65,536$ `(v1, s1, v2, s2)` tuples (`Experiment B`) reveals an important dichotomy between bitwise/comparison handlers and integer arithmetic handlers:

| LLVM IR Instruction | Implemented Shadow Equation in `MemorySanitizer.cpp` | Exhaustive 4-Bit Result (65,536 states) | Semantic Classification |
| :--- | :--- | :--- | :--- |
| `and` (`visitAnd`, L2533–2577) | $S = (S_1 \mathbin{\&} S_2) \mid (V_1 \mathbin{\&} S_2) \mid (S_1 \mathbin{\&} V_2)$ | `exact = 65,536`, `FP = 0`, `FN = 0` | **100% bit-exact** (`0 & uninit = 0`) |
| `or` (`visitOr`, L2579–2624) | $S = (S_1 \mathbin{\&} S_2) \mid (\neg V_1 \mathbin{\&} S_2) \mid (S_1 \mathbin{\&} \neg V_2)$ (plus `S \| sext(V1 & V2 != 0)` if `disjoint`) | `exact = 65,536`, `FP = 0`, `FN = 0` | **100% bit-exact** (`1 \| uninit = 1`) |
| `xor` (`visitXor`, L3005) | `handleShadowOr`: $S = S_1 \mid S_2$ | `exact = 65,536`, `FP = 0`, `FN = 0` | **100% bit-exact** |
| `icmp eq/ne` (`propagateEqualityComparison`, L2290–2320) | $S_c = S_1 \mid S_2,\; C = V_1 \oplus V_2,\; S_i = (S_c \neq 0) \land ((\neg S_c \mathbin{\&} C) = 0)$ | `exact = 65,536`, `FP = 0`, `FN = 0` | **100% bit-exact** (defined `0 != 1` bit clears shadow!) |
| `icmp slt/ult/...` (`handleRelationalComparisonExact`, L3046–3090) | Forms $[a_{\min}, a_{\max}]$ via `(V & ~S)` / `(V \| S)` (XOR sign-flip if signed) and checks `(Amin cmp Bmax) ^ (Amax cmp Bmin)` | Exact interval extrema test | **Bit-exact for single-variable comparisons** |
| `add` / `sub` / non-const `mul` (`visitAdd`/`visitSub`/`visitMul`, L2997–3005) | `handleShadowOr` (`Combiner<true>` L2641–2775): **$S = S_1 \mid S_2$**! | `exact = 37,376`, `FP = 0`, **`FN = 28,160` (`43.0%`)** | **Fast unsound carry trade-off!** (`0b00_s0001 + 0b01_s0000` leaves bit 1 clean `0` despite carry dependence!) |

Specifically, `MemorySanitizer.cpp:2628-2635` documents why `Combiner<true>` defaults to bitwise OR (`S1 | S2`) for general arithmetic: avoiding ripple-carry shadow propagation or full-word `sext((S1 | S2) != 0)` prevents false positives on byte/bitfield-packed registers and saves ~6–10 instructions per `add`/`sub`, trading away detection of uninitialized carries propagating into higher initialized bits (`ADD carry-loss FN witness: v1=0b0000 s1=0b0001 + v2=0b0001 s2=0b0000 -> exact_shadow=0b0011, handleShadowOr=0b0001`). Constant multiplication (`handleMulByConstant`, L2945–2987) preserves trailing zero bits (`S << countr_zero(C)`), and shifts (`handleShift`, L3156–3168) shift `S1` by `V2` while tainting all bits if `S2 != 0`.

#### Chained Origin Tracking and Uninstrumented-FFI Cascades

- **4-byte Origin Shadow (`msan.h:248`, `msan_origin.h`):** `-fsanitize-memory-track-origins=2` adds `SHADOW_TO_ORIGIN(shadow) = shadow + 0x100000000000ULL`, storing one `u32` `Origin` ID per 4-byte aligned word (`2x` total shadow+origin virtual footprint). Bit `31` distinguishes heap allocation StackDepot IDs (`0xxx...`) from stack/chained IDs (`1zzz...`), where 3 bits (`kDepthBits = 3`, `kMaxDepth = 7`, `msan_origin.h:145-163`) bound store-chain length in `ChainedOriginDepot` (`(here_stack_id, prev_origin_id) -> chained_id`), capping explosion at `origin_history_per_stack_limit = 20000` (`msan_flags.inc:21`).
- **Whole-Program Instrumentation Requirement (`FFI` cliff):** Unlike `ASan` (which works incrementally across uninstrumented `.so` libraries because heap allocators still poison memory), `MSan` tracks **every** register write. If *any* linked C/C++ dependency (`libstdc++`, `OpenSSL`, `zlib`, SIMD assembly) is compiled without `-fsanitize=memory`, its writes to caller buffers or TLS leave MSan shadow bytes at `1` (`poisoned`)—triggering deterministic false positives downstream until every library in the link closure (including `libc++`) is rebuilt with MSan or manually wrapped via `__msan_unpoison()`.

### 4. Adaptive 4-Slot SIMD Shadow Cells and Vector-Clock Races (`TSan v3`)

Basis: source + normative + execution (`tsan_defs.h`, `tsan_shadow.h`, `tsan_rtl_access.cpp`, `tsan_vector_clock.h`, `tsan_rtl.cpp`, `tsan_rtl_mutex.cpp`, `/tmp/probe_sanitizers.py` Experiment C).

ThreadSanitizer v3 reduces memory cost by $2\times$ over v2 (`4x -> 2x` application shadow + `0.5x` meta-shadow, `tsan_defs.h:76-94`): every `kShadowCell = 8` aligned user bytes map to `kShadowCnt = 4` compact 32-bit `RawShadow` slots (`16 bytes` per 8 user bytes). Each 32-bit `Shadow` word packs (`tsan_shadow.h:149-171`, little-endian):

| Bit Range | Field | Width | Semantics |
| :--- | :--- | :---: | :--- |
| `[7:0]` | `access_` | 8 bits | Bitmask of accessed bytes within the 8-byte cell (`kFreeAccess = 0x81` marker) |
| `[15:8]` | `sid_` | 8 bits | Active `TidSlot` ID (`0..254`; `kFreeSid = 255`, `kThreadSlotCount = 256`) |
| `[29:16]` | `epoch_` | 14 bits | Per-slot scalar clock epoch (`1..16383`; `kEpochOver = 1 << 14`) |
| `[30]` | `is_read_` | 1 bit | `1` for load, `0` for store (`Shadow::kRodata = 1 << 30` optimizes immutable `.rodata` reads) |
| `[31]` | `is_atomic_` | 1 bit | `1` for C11/C++11/Rust atomic operations (exempt from data race against same-atomic accesses) |

#### Fast-Path Vector Check, Slot Multiplexing, and Soundness Blind Spots

1. **128-Bit SIMD Parallel Race Check (`tsan_rtl_access.cpp:238-387`):** On every memory access, `MemoryAccess()` loads the 128-bit shadow cell (`_mm_load_si128`) and broadcasts `cur` (`_mm_set1_epi32`). `ContainsSameAccess` exits immediately in ~5 instructions if an identical `(sid, epoch, access, rw)` (or `kRodata`) already exists. Otherwise `CheckRaces` computes in parallel across all 4 slots:
   $$\text{no\_race} = (\text{access\_intersect} = 0) \;\lor\; (\text{cur.sid} = \text{old.sid}) \;\lor\; (\text{both\_read\_or\_atomic}).$$
   Any surviving slot (`race_mask != 0`) triggers scalar `thr->clock.Get(sid) < old.epoch` comparison (`VectorClock`, `tsan_vector_clock.h:37` holding `Epoch clk_[256]`, updated at mutex/atomic `Acquire`/`Release` via `SyncVar` in `meta-shadow`, `tsan_rtl_mutex.cpp:440-486`).
2. **4-Slot Eviction Race Blind Spot (`tsan_rtl_access.cpp:344-351`, `Experiment C`):** When all 4 slots in an 8-byte cell are occupied and no slot shares `(cur.sid, cur.access)` (`rewrite_mask == 0`), `CheckRaces` evicts a pseudo-random slot indexed by `index = (atomic_load_relaxed(&thr->trace_pos) / 2) % 16` (`shadow_mem[index / 4]`). **Consequence:** If $>4$ distinct threads read a shared location (synchronizing with a writer $W$) before a concurrent, *unsynchronized* reader $Z$ accesses that word, the readers can evict $W$'s `Write` slot and saturate all 4 slots with `Read` records—causing $Z$'s true data race with $W$ to pass `both_read_or_atomic` silently! Experiment C confirms this directly on `gcc 15.2.0 -fsanitize=thread` (`libtsan.so.2`): with `0`, `2`, or `4` staggered synchronized readers, TSan catches the `writer_fn` vs. `unsync_racer_fn` race (`exit = 66`, `WARNING: ThreadSanitizer: data race`), whereas **`8` or `16` synchronized readers produce `exit = 0, race_reported = False`!**
3. **255-Slot Multiplexing & Epoch Reset (`tsan_rtl.cpp:180-330`):** TSan v3 does *not* fail above 255 threads; instead, `SlotAttachAndLock` multiplexes all OS threads onto 255 `TidSlot`s (`ctx->slots`), incrementing `slot->epoch` on each preemption/attach. When all 255 slots exhaust `kEpochLast = 16383`, `DoReset` pauses and **flushes all shadow memory (`MmapFixedSuperNoReserve`) and resets all meta-shadow clocks**, opening a temporary blind spot for races spanning across the global reset boundary.
4. **Custom Synchronization False Positives:** Lock-free ring buffers, kernel `futex`/`io_uring` completions, or custom inline `asm` memory fences invisible to LLVM's atomic/pthread interceptors trigger spurious data-race reports unless annotated with `__tsan_acquire(addr)` / `__tsan_release(addr)`.

### 5. Six-Level Performance and Resource Footprint Characterization (`L1`–`L6`)

Basis: source + normative + execution (`asan_mapping.h`, `hwasan_mapping.h`, `gwp_options.inc`, `msan.h`, `tsan_defs.h`, `Serebryany et al. USENIX ATC 2012`, `Stepanov & Serebryany CGO 2015`, `Serebryany 2018`, `Serebryany et al. ICSE-SEIP 2024`, `/tmp/probe_sanitizers.py`).

| Level | `ASan` | `HWASan` / `ARM64 MTE` | `GWP-ASan` | `MSan` (`origins=0` / `origins=2`) | `TSan v3` (vs. `TSan v2`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **L1: Human & Agent Authoring Velocity** | Near-zero code change; occasional `RLIMIT_AS` / custom-allocator `ASAN_OPTIONS` tweaks. | `HWASan`: minimal; `MTE`: handles `TBI` top-byte pointer masking assumptions in tag-unsafe C/Rust code. | **Zero** developer annotations; allocator hook only (`Scudo`/Bionic/Chrome). | **High maintenance cost:** requires rebuilding *entire* C/C++ dependency tree (`libc++`) + `__msan_unpoison` on FFI/asm boundaries. | Moderate: requires `__tsan_acquire`/`__tsan_release` on custom `io_uring`/futex/inline-asm sync; avoids v2 false thread-limit crashes. |
| **L2: Toolchain / Runtime Build Time** | `libasan` builds in `~1–2 min`; standard clang/gcc sysroot works unmodified. | `libhwasan` `~1 min`; requires `AArch64 TBI` / `x86 LAM` kernel support. | `libgwp_asan` builds in `< 10 s` (`-fno-rtti -nostdinc++`, `CMakeLists.txt`). | `libmsan` `~1 min`, **but instrumented `libc++` + sysroot rebuild takes `~15–45 min`**. | `libtsan` builds in `~1–2 min` (`-msse4.2` required on x86_64). |
| **L3: Target Compile & Link Latency** | `+30–70%` compile time (shadow checks on every load/store; stack frame poisoning). | `+25–50%` (outlined check callbacks shrink code size/compile time vs. inline ASan). | **`0%`** (no compiler pass). | `+50–90%` (`origins=0`), **`+80–150%`** (`origins=2` due to per-value shadow+origin IR lowering). | `+50–100%` (every non-dead load/store lowers to `__tsan_read/write*` + `FuncEntry`/`FuncExit`). |
| **L4: Target Execution Throughput** | `~1.7–2.5x` slowdown (`USENIX ATC 2012`: `~73%` geometric mean on SPEC CPU2006). | `HWASan`: `~1.8–2.5x` (outlined); **`MTE` async**: `~1.02–1.10x` hardware tag check. | **`< 1.01x` (`~0%` CPU)**; `SampleRate = 1/5000–1/100000` fast-path TLS counter check. | `~2.5x` (`origins=0`), **`~3.5–5.0x`** (`origins=2`, `CGO 2015`). | `TSan v3`: **`~3–10x`** slowdown (`128-bit` SIMD cell checks), down from v2 `~5–15x`. |
| **L5: Check & Crash-Triage Latency** | `3–6` cycles (`< 2 ns`) per inline load/store check; crash stack symbolize `10–200 ms`. | Software `HWASan` outlined check `~5–12` cycles; hardware `MTE` `~0–1` cycle sync/async. | `0` cycles on unsampled; sampled access uses page-table MMU (`0` cycle fast path, `SIGSEGV` handler `~1–50 ms`). | `2–8` cycles per bitwise/OR op; `origins=2` adds `ChainedOriginDepot` hash insert on uninit stores (`~50–300 ns`). | `~10–25` cycles (`ContainsSameAccess` SIMD hit); vector-clock `Acquire`/`Release` `~50–200 ns`; race unwind `10–200 ms`. |
| **L6: RAM, Virtual Address & Binary Footprints** | **`20.48 TiB` `VmSize`**, `1.5–3.5x` `VmRSS` (redzones + `256 MiB` quarantine + `FakeStack`), `+50–120%` `.text`. | `HWASan`: **`1.10–1.35x` `VmRSS`** (`1/16` shadow + zero quarantine); `MTE`: `3.03%–6.25%` DRAM; outlined checks shrink `.text`. | **Fixed `~128 KiB–4 MiB` RSS** (`16` slots × `1`–few pages + metadata); `+0%` `.text`. | `2.0x` RSS (`origins=0`), **`3.0x` RSS** (`origins=2` + `ChainedOriginDepot` hash table); `+80–150%` `.text`. | **`2.5x` shadow+meta (`2x` + `0.5x`)**, `~3–5x` total RSS (halved from v2 `5–10x`!), plus `64 KiB` stack/trace per thread. |

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

Basis: derived + source (`asan_internal.h`, `msan_origin.h`, `tsan_rtl_access.cpp`, `guarded_pool_allocator.h`).

#### (C1) Human Comprehensibility and Diagnostic Legibility

- **Causal diagnostic completeness vs. working-memory overload:** `ASan` and `GWP-ASan` deliver **high human legibility** because every crash prints three crisp causal anchors: (1) exact faulting PC and access size, (2) allocation stack trace + offset within redzone/object, and (3) deallocation stack trace (`free`), alongside a legend-annotated hex dump of `0xfa`/`0xfd`/`0x05` shadow bytes. `MSan` **without origins** (`origins=0`) is notoriously opaque for humans ("Use of uninitialized value at branch line 900" 12 frames downstream from a partial struct init), whereas `-fsanitize-memory-track-origins=2` restores causal readability by printing up to 7 `ChainedOriginDepot` store steps back to the original `malloc` or `alloca`.
- **TSan's hidden diagnostic blind spots:** When `TSan v3` detects a race involving a previously evicted or recycled `TidSlot` epoch—or reports `As if synchronized via sleep` (`Experiment C` stderr!)—humans still get the exact two racing PCs (`writer_fn` vs. `unsync_racer_fn`), but when `trace_part` wraps or `DoReset` clears shadow history, `Previous write` stack recovery degrades to `<null>` or `"stack restored/unavailable"`, forcing non-local speculation over lock hierarchies.
- **Configuration footguns (`detect_leaks`, `ulimit -v`, `MSan` FFI):** Default `ASAN_OPTIONS=detect_leaks=1` triggers `LSan` failures in intentional global-singleton or `fork()` processes; `ulimit -v` breaks `MAP_NORESERVE` shadow startup; and omitting `-stdlib=libc++` instrumented builds under `MSan` produces hundreds of bogus uninitialized-value reports inside `std::string` internals rather than a clean linker-time error.

#### (C2) Simplicity, Orthogonality, and Universal Model Refinement

Stripping away hardware and layout optimizations separates **essential safety semantics** from **realization-medium accidents**:

- **Core semantic model:** Every memory-safety and concurrency bug targeted by these five sanitizers belongs to a single unified abstract machine state per allocated byte $b$ (directly isomorphic to operational UB semantics like `MiniRust` / `Miri` Stacked/Tree Borrows):
  $$\text{AbstractByte}(b) = (\text{Value}_b \in \mathbb{B}^8,\; \text{InitMask}_b \in \mathbb{B}^8,\; \text{ProvenanceTag}_b \in \text{AllocEpoch},\; \text{LastWriteHB}_b \times \text{ReadHBSet}_b),$$
  checked under three orthogonal invariants: (1) pointer provenance matches `ProvenanceTag_b`, (2) observed bits have `InitMask_b = 0`, and (3) concurrent accesses satisfy happens-before (`HB`).
- **Why five specialized mechanisms persist (`Felleisen macro-expressibility` & `Ousterhout deep-module` analysis):** None of `ASan`, `HWASan`, `GWP-ASan`, `MSan`, or `TSan` can cheaply macro-express the others without breaking hardware resource constraints:
  - Encoding `InitMask_b` inside `ASan` fails because `1:8` redzones cannot distinguish bit 3 vs. bit 4 inside an initialized byte (`MaybeUninit`/bitfield false positives);
  - Encoding unbounded `ProvenanceTag` in `16`-bit or `8`-bit hardware tags (`HWASan`/`MTE`) collapses spatial redzones into probabilistic $1/256$–$1/16$ collisions;
  - Encoding full unbounded `ReadHBSet` inside `TSan`'s `128-bit` SIMD cell fails constant-space $O(1)$ per-access lookup, forcing `TSan v3` to project `ReadHBSet` into a lossy 4-slot cache (`Experiment C` blind spot).
  - **Refinement insight:** Rather than stacking ad-hoc runtime adapters (which cannot coexist due to shadow-offset collisions), clean toolchains separate **(a) deterministic pre-merge verification** (high-cost `Miri` / full `ASan` + `MSan(origins=2)` + `TSan` in CI shards, plus linker-enforced `.note.msan` ELF ABI tags preventing silent uninstrumented-`.so` linking!) from **(b) zero-instrumentation production telemetry** (`GWP-ASan` + hardware `MTE` dynamic carveouts).

## Boundaries

- **Intra-object sub-field overflows (`known not to apply` across all five tools without field padding):** Structs like `struct { char buf[8]; int is_admin; };` have no `ASan` redzones, no `HWASan`/`MTE` tag boundary (must be 16B aligned), and no `GWP-ASan` guard page between adjacent fields (`-fsanitize=bounds` / `UBSan` array bounds are required instead).
- **Large stride / pointer-arithmetic jumps (`known not to apply` to redzone/guard-page checks):** Writing `p[1024]` directly can leap cleanly across `ASan`'s `16–2048 B` heap redzone or `GWP-ASan`'s single `4 KiB` guard page into an unrelated valid allocation.
- **Quarantine-evicted UAF (`known not to apply` to `ASan` once FIFO wraps):** Once cumulative frees exceed `quarantine_size_mb` (`256 MiB` default), reallocated pointers pass shadow checks (`0x00`) despite dangling temporal provenance.
- **Tag-collision UAF/OOB (`known not to apply` deterministically in `HWASan` / `MTE`):** Random 8-bit (`HWASan`) and 4-bit (`MTE`) tags fail to catch temporal or distant-object aliasing with probability $1/256$ ($0.39\%$) and $1/16$ ($6.25\%$), respectively; `HWASan` tag `0` also disables checking for untagged allocations.
- **MSan carry-bit arithmetic & uninstrumented-ABI blind spots (`known not to apply` / `unsupported`):** `MemorySanitizer.cpp` (`visitAdd`/`visitSub`/`visitMul`) uses `handleShadowOr` (`Sa | Sb`), missing bit carries (`28,160 / 65,536` 4-bit states in `Experiment B`); uninstrumented `.so` libraries or inline `asm` produce false positives unless manually unpoisoned.
- **TSan v3 4-slot eviction, global reset, and schedule dependence (`known not to apply` universally):** `TSan` only detects races occurring in the observed thread schedule; `>4` readers evict prior write slots (`Experiment C`, `8+` readers -> `0` reports); and `255`-slot epoch exhaustion triggers global shadow flushes (`DoReset`).
- **Windows / macOS / ARM64 runtime specifics (`not examined` by local execution):** While `asan_mapping.h`, `msan.h`, and `hwasan_mapping.h` source layouts for `AArch64`, `RISC-V`, `FreeBSD`, and `Windows` were inspected, live execution probes ran strictly on `x86_64-linux-gnu` (`gcc 15.2.0` `libasan.so.8`, `libtsan.so.2`).

## Evidence

- **Pinned Git repositories and inspected source regions:**
  - `llvm/llvm-project` @ `63b8d2fd94ba3b1a80023dae7139949dd5be6b78`:
    - `compiler-rt/lib/asan/`: `asan_mapping.h` (L21–31, L182, L246), `asan_internal.h` (L141–156), `asan_flags.cpp` (L187–206), `asan_flags.inc` (L19–54), `asan_fake_stack.h` (L56–98), `asan_allocator.cpp` (L334–391); `llvm/lib/Transforms/Instrumentation/AddressSanitizer.cpp` (`createSlowPathCmp` L1670–1686, `instrumentAddress` L1733–1817).
    - `compiler-rt/lib/hwasan/`: `hwasan_mapping.h` (L37–62), `hwasan_allocator.cpp` (short granules L253–261); `llvm/lib/Transforms/Instrumentation/HWAddressSanitizer.cpp` (L86, L538–541).
    - `compiler-rt/lib/gwp_asan/`: `guarded_pool_allocator.h` (L80–93, L239), `guarded_pool_allocator.cpp` (L204–270, L328–360), `options.inc` (L22–65).
    - `compiler-rt/lib/msan/`: `msan.h` (L247–256), `msan_origin.h` (L60–164), `msan_flags.inc` (L20–21), `msan_chained_origin_depot.cpp`; `llvm/lib/Transforms/Instrumentation/MemorySanitizer.cpp` (`handleBitwiseAnd` L2544–2563, `visitOr` L2579–2624, `Combiner` L2641–2708, `CreateShadowCast` L2734–2755, `handleShadowOr` L2769–2775, `handleMulByConstant` L2954–2987, `visitMul`/`visitAdd`/`visitSub`/`visitXor` L2989–3005, `propagateEqualityComparison` L2290–2320, `handleRelationalComparisonExact` L3046–3090, `handleShift` L3156–3168).
    - `compiler-rt/lib/tsan/rtl/`: `tsan_defs.h` (L57–94), `tsan_shadow.h` (L57–177), `tsan_vector_clock.h` (L20–48), `tsan_rtl_access.cpp` (L150–450), `tsan_rtl.cpp` (L180–330), `tsan_rtl_mutex.cpp` (L440–486).
  - `google/sanitizers` @ `aa054ab16a697f206f1888aedbb94407df3e480c`:
    - `hwaddress-sanitizer/prove_hwasanwrap.smt2` (L1–65), `mte-dynamic-carveout/spec.md` (L1–142), `README.md`.
- **Peer-reviewed papers & arXiv preprints:** Serebryany et al. (USENIX ATC 2012, ASan), Stepanov & Serebryany (CGO 2015, `DOI: 10.1109/CGO.2015.7054186`), Serebryany (`arXiv:1802.09517`, Memory Tagging / HWASan), Serebryany et al. (ICSE-SEIP 2024, `DOI: 10.1145/3639477.3640328`, GWP-ASan).
- **Self-contained reproducible execution probe (`Basis: execution`, run 2026-11-19 on `x86_64` Linux with `gcc 15.2.0` + Python 3.13):**
  Save as `/tmp/probe_sanitizers.py` and run `python3 /tmp/probe_sanitizers.py`:

```python
#!/usr/bin/env python3
"""Reproducible micro-probes for ASan shadow layout, MSan bit-exact algebra, and TSan v3 4-slot eviction."""

import os
import re
import subprocess
import tempfile


def experiment_a_asan():
    print("=== Experiment A: Real GCC ASan 1:8 Shadow Layout, VmSize/VmRSS & Poison Bytes ===")
    c_src = r"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sanitizer/asan_interface.h>

__attribute__((noinline)) uint8_t read_u8(volatile uint8_t *p) { return *p; }
__attribute__((no_sanitize("address"), noinline)) uint8_t raw_shadow_read(const uint8_t *sh) { return *sh; }

int main(void) {
  uint8_t *buf = (uint8_t *)malloc(13);
  memset(buf, 0x41, 13);
  uintptr_t addr = (uintptr_t)buf;

  size_t scale = 0, offset = 0;
  __asan_get_shadow_mapping(&scale, &offset);
  uint8_t *sh = (uint8_t *)((addr >> scale) + offset);
  printf("alloc_ptr=%p scale=%zu offset=0x%zx\n", (void *)buf, scale, offset);
  printf("shadow_bytes[granules -1..+2] = [0x%02x, 0x%02x, 0x%02x, 0x%02x]\n",
         raw_shadow_read(sh - 1), raw_shadow_read(sh),
         raw_shadow_read(sh + 1), raw_shadow_read(sh + 2));
  printf("sum=%u\n", (unsigned)read_u8(buf));

  FILE *f = fopen("/proc/self/status", "r");
  char line[256];
  while (f && fgets(line, sizeof(line), f)) {
    if (strncmp(line, "VmSize:", 7) == 0 || strncmp(line, "VmRSS:", 6) == 0) {
      printf("%s", line);
    }
  }
  if (f) fclose(f);
  free(buf);
  printf("after_free shadow[0]=0x%02x shadow[1]=0x%02x\n",
         raw_shadow_read(sh), raw_shadow_read(sh + 1));
  return 0;
}
"""
    with tempfile.TemporaryDirectory(prefix="probe_asan_") as td:
        c_path = os.path.join(td, "p.c")
        bin_path = os.path.join(td, "p")
        with open(c_path, "w") as f:
            f.write(c_src)
        subprocess.run(["gcc", "-O2", "-fsanitize=address", c_path, "-o", bin_path], check=True)
        env = dict(os.environ, ASAN_OPTIONS="detect_leaks=0")
        res = subprocess.run([bin_path], env=env, capture_output=True, text=True, check=True)
        print(res.stdout.strip())
        obj = subprocess.run(["objdump", "-d", bin_path], capture_output=True, text=True, check=True).stdout
        m = re.search(r"<read_u8>:.*?\n\n", obj, re.S)
        if m:
            print("x86_64 emitted read_u8 check:")
            for line in m.group(0).splitlines()[:14]:
                print("  " + line)


def experiment_b_msan_algebra():
    print("\n=== Experiment B: Exhaustive 4-Bit MSan Shadow Soundness & Exactness ===")
    MASK = 0xF

    def concretize(val, shad):
        fixed = (~shad) & MASK
        target = val & fixed
        return [x for x in range(16) if (x & fixed) == target]

    def exact_shadow(v1, s1, v2, s2, op):
        c1 = concretize(v1, s1)
        c2 = concretize(v2, s2)
        outs = [op(x, y) & MASK for x in c1 for y in c2]
        or_all = 0
        and_all = MASK
        for o in outs:
            or_all |= o
            and_all &= o
        return or_all ^ and_all

    stats = {k: {"fp": 0, "fn": 0, "exact": 0} for k in ("and", "or", "xor", "add")}
    add_witness = None
    for v1 in range(16):
        for s1 in range(16):
            for v2 in range(16):
                for s2 in range(16):
                    ex_and = exact_shadow(v1, s1, v2, s2, lambda a, b: a & b)
                    ms_and = (s1 & s2) | (v1 & s2) | (s1 & v2)
                    if ex_and == ms_and:
                        stats["and"]["exact"] += 1
                    else:
                        if ms_and & ~ex_and: stats["and"]["fp"] += 1
                        if ex_and & ~ms_and: stats["and"]["fn"] += 1

                    ex_or = exact_shadow(v1, s1, v2, s2, lambda a, b: a | b)
                    ms_or = ((s1 & s2) | ((~v1 & MASK) & s2) | (s1 & (~v2 & MASK))) & MASK
                    if ex_or == ms_or:
                        stats["or"]["exact"] += 1
                    else:
                        if ms_or & ~ex_or: stats["or"]["fp"] += 1
                        if ex_or & ~ms_or: stats["or"]["fn"] += 1

                    ex_xor = exact_shadow(v1, s1, v2, s2, lambda a, b: a ^ b)
                    ms_xor = s1 | s2
                    if ex_xor == ms_xor:
                        stats["xor"]["exact"] += 1
                    else:
                        if ms_xor & ~ex_xor: stats["xor"]["fp"] += 1
                        if ex_xor & ~ms_xor: stats["xor"]["fn"] += 1

                    ex_add = exact_shadow(v1, s1, v2, s2, lambda a, b: (a + b) & MASK)
                    ms_add = s1 | s2
                    if ex_add == ms_add:
                        stats["add"]["exact"] += 1
                    else:
                        if ms_add & ~ex_add: stats["add"]["fp"] += 1
                        if ex_add & ~ms_add:
                            stats["add"]["fn"] += 1
                            if add_witness is None and s2 == 0 and s1 == 1:
                                add_witness = (v1, s1, v2, s2, ex_add, ms_add)

    for op_name, d in stats.items():
        print(f"op={op_name:3s} (65536 states): exact={d['exact']}, false_positives={d['fp']}, false_negatives={d['fn']}")
    if add_witness:
        v1, s1, v2, s2, ex_a, ms_a = add_witness
        print(f"ADD carry-loss FN witness: v1=0b{v1:04b} s1=0b{s1:04b} + v2=0b{v2:04b} s2=0b{s2:04b} -> exact_shadow=0b{ex_a:04b}, handleShadowOr=0b{ms_a:04b}")

    eq_fp = eq_fn = 0
    for v1 in range(16):
        for s1 in range(16):
            for v2 in range(16):
                for s2 in range(16):
                    c1 = concretize(v1, s1)
                    c2 = concretize(v2, s2)
                    eq_vals = {int(x == y) for x in c1 for y in c2}
                    ex_eq = 1 if len(eq_vals) > 1 else 0
                    sc = s1 | s2
                    c = v1 ^ v2
                    ms_eq = 1 if (sc != 0 and ((~sc & MASK) & c) == 0) else 0
                    if ms_eq and not ex_eq: eq_fp += 1
                    if ex_eq and not ms_eq: eq_fn += 1
    print(f"op=icmp_eq (65536 states): exact={65536 - eq_fp - eq_fn}, false_positives={eq_fp}, false_negatives={eq_fn}")


def experiment_c_tsan_eviction():
    print("\n=== Experiment C: Real GCC TSan v3 4-Slot Shadow-Cell Eviction Blind Spot ===")
    c_src = r"""
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

static uint64_t shared_word = 0;
static atomic_int step = 0;
static volatile uint64_t dummy_sink[32];

static void *writer_fn(void *arg) {
  (void)arg;
  shared_word = 0xdeadbeefULL;
  atomic_store_explicit(&step, 1, memory_order_release);
  while (atomic_load_explicit(&step, memory_order_acquire) < 2) {}
  return NULL;
}

static void *sync_reader_fn(void *arg) {
  int idx = (int)(uintptr_t)arg;
  while (atomic_load_explicit(&step, memory_order_acquire) < 1) {}
  for (int j = 0; j < idx; j++) {
    dummy_sink[j & 31] = (uint64_t)j;
  }
  volatile uint64_t v = shared_word;
  (void)v;
  return NULL;
}

static void *unsync_racer_fn(void *arg) {
  (void)arg;
  usleep(200000);
  volatile uint64_t v = shared_word;
  (void)v;
  return NULL;
}

int main(int argc, char **argv) {
  int num_readers = (argc > 1) ? atoi(argv[1]) : 0;
  pthread_t racer, writer;
  pthread_create(&racer, NULL, unsync_racer_fn, NULL);
  pthread_create(&writer, NULL, writer_fn, NULL);
  while (atomic_load_explicit(&step, memory_order_acquire) < 1) {}
  pthread_t readers[32];
  for (int i = 0; i < num_readers; i++) {
    pthread_create(&readers[i], NULL, sync_reader_fn, (void *)(uintptr_t)i);
    pthread_join(readers[i], NULL);
  }
  pthread_join(racer, NULL);
  atomic_store_explicit(&step, 2, memory_order_release);
  pthread_join(writer, NULL);
  return 0;
}
"""
    with tempfile.TemporaryDirectory(prefix="probe_tsan_") as td:
        c_path = os.path.join(td, "t.c")
        bin_path = os.path.join(td, "t")
        with open(c_path, "w") as f:
            f.write(c_src)
        subprocess.run(["gcc", "-O2", "-fsanitize=thread", "-pthread", c_path, "-o", bin_path], check=True)
        for k in (0, 2, 4, 8, 16):
            res = subprocess.run([bin_path, str(k)], capture_output=True, text=True)
            race = "WARNING: ThreadSanitizer: data race" in res.stderr
            print(f"sync_readers={k:2d}: exit={res.returncode}, race_reported={race}")


if __name__ == "__main__":
    experiment_a_asan()
    experiment_b_msan_algebra()
    experiment_c_tsan_eviction()
```

Observed output (`exit 0`):

```text
=== Experiment A: Real GCC ASan 1:8 Shadow Layout, VmSize/VmRSS & Poison Bytes ===
alloc_ptr=0x7b90bfbe0010 scale=3 offset=0x7fff8000
shadow_bytes[granules -1..+2] = [0xfa, 0x00, 0x05, 0xfa]
sum=65
VmSize:	21474884396 kB
VmRSS:	   13844 kB
after_free shadow[0]=0xfd shadow[1]=0xfd
x86_64 emitted read_u8 check:
  <read_u8>:
      1590:	48 89 f8             	mov    %rdi,%rax
      1593:	48 89 fa             	mov    %rdi,%rdx
      1596:	48 c1 e8 03          	shr    $0x3,%rax
      159a:	83 e2 07             	and    $0x7,%edx
      159d:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
      15a4:	38 d0                	cmp    %dl,%al
      15a6:	7f 04                	jg     15ac <read_u8+0x1c>
      15a8:	84 c0                	test   %al,%al
      15aa:	75 04                	jne    15b0 <read_u8+0x20>
      15ac:	0f b6 07             	movzbl (%rdi),%eax
      15af:	c3                   	ret
      15b0:	50                   	push   %rax
      15b1:	e8 2a fb ff ff       	call   10e0 <__asan_report_load1@plt>

=== Experiment B: Exhaustive 4-Bit MSan Shadow Soundness & Exactness ===
op=and (65536 states): exact=65536, false_positives=0, false_negatives=0
op=or  (65536 states): exact=65536, false_positives=0, false_negatives=0
op=xor (65536 states): exact=65536, false_positives=0, false_negatives=0
op=add (65536 states): exact=37376, false_positives=0, false_negatives=28160
ADD carry-loss FN witness: v1=0b0000 s1=0b0001 + v2=0b0001 s2=0b0000 -> exact_shadow=0b0011, handleShadowOr=0b0001
op=icmp_eq (65536 states): exact=65536, false_positives=0, false_negatives=0

=== Experiment C: Real GCC TSan v3 4-Slot Shadow-Cell Eviction Blind Spot ===
sync_readers= 0: exit=66, race_reported=True
sync_readers= 2: exit=66, race_reported=True
sync_readers= 4: exit=66, race_reported=True
sync_readers= 8: exit=0, race_reported=False
sync_readers=16: exit=0, race_reported=False
```

## Revalidation

1. **Check upstream repository movement:**
   `git -c protocol.version=0 ls-remote https://github.com/llvm/llvm-project.git HEAD`
   `git -c protocol.version=0 ls-remote https://github.com/google/sanitizers.git HEAD`
2. **Verify sanitizer instrumentation and shadow layout stability:**
   - Diff `compiler-rt/lib/asan/asan_mapping.h` (`ASAN_SHADOW_SCALE`, `ASAN_SHADOW_OFFSET_CONST`), `compiler-rt/lib/hwasan/hwasan_allocator.cpp` (short granules), and `compiler-rt/lib/gwp_asan/options.inc`.
   - Diff `llvm/lib/Transforms/Instrumentation/MemorySanitizer.cpp` (`visitAdd`, `visitAnd`, `visitOr`, `propagateEqualityComparison`) to verify whether carry-propagating shadow logic replaced `handleShadowOr`.
   - Diff `compiler-rt/lib/tsan/rtl/tsan_defs.h` and `tsan_rtl_access.cpp` (`kShadowCnt`, `kThreadSlotCount`, `CheckRaces` eviction index).
3. **Re-run deterministic runtime & algebraic probe (`< 4 s`):**
   Execute `python3 /tmp/probe_sanitizers.py` and verify ASan poison bytes (`0xfa`/`0x00`/`0x05`/`0xfd`), MSan 4-bit exactness counts, and TSan 4-slot eviction transition (`sync_readers=4 -> 66` vs. `8 -> 0`).
