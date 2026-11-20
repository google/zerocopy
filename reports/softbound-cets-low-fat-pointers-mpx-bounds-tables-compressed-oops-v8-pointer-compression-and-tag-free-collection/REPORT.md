# Runtime pointer metadata and compressed references: SoftBound+CETS disjoint metadata, low-fat pointers, Intel MPX bounds tables, HotSpot compressed oops and class pointers, V8 pointer compression, and tag-free collection

## Summary

- **Where a scheme stores per-pointer metadata decides how its space cost scales.**
  - *Disjoint-metadata* schemes pay per in-memory pointer slot. These are SoftBound+CETS's shadow trie and Intel MPX's bounds tables.
    - SoftBound+CETS at the pinned revision uses a 32-byte entry for every 8-byte pointer-sized slot that holds a pointer. That is 4× the pointer's own size.
    - MPX also uses a 32-byte bounds-table entry per pointer slot.
    - The published average memory overheads are 64% (SoftBound shadow space, spatial only) and 1.9–2.1× (MPX), with worst cases of 200% (SoftBound) and higher.
  - *Low-fat* schemes store no per-pointer metadata. They pay instead in three ways:
    - allocation rounding to size classes;
    - a source-level one-byte "one past the end" padding rule;
    - reservation of tens of GiB of virtual address space per size class.
  - In the default LowFat configuration a request of exactly 16 bytes is placed in the 32-byte class, and power-of-two requests of 16 KiB and above are doubled. The authors report about 3% memory overhead on SPEC CPU2006.
- **Compressed references are valid only while an address-space invariant holds, and the runtime must check that invariant at startup.**
  - HotSpot decodes `base + (narrow << shift)` and picks one of four modes from where the heap was reserved. On Temurin 25.0.5 with the default 8-byte alignment, compressed oops switched off at `-Xmx32g`. With `ObjectAlignmentInBytes=16` they persisted to `-Xmx60g` (zero-based, shift 4) and switched off at `-Xmx64g` (measured).
  - V8 stores 32-bit tagged values inside a 4 GiB-aligned cage and decompresses with `cage_base | raw`.
- **Compression saves bytes only where a reference field changes the object's aligned size.**
  - Measured on Temurin 25.0.5:
    - a reference-array slot shrinks from 8 to 4 bytes;
    - an object with one reference and one `int` stays at 24 bytes with or without compressed oops (alignment absorbs the saving);
    - an object with two references and one `int` shrinks from 32 to 24 bytes.
  - Compact object headers, a product option in JDK 25, shrink a bare `java.lang.Object` from 16 to 8 bytes. The pinned `openjdk/jdk` revision makes compact headers the default (`globals.hpp` line 135).
- **Tag-free collection removes per-object type tags by moving type information from data to code positions.**
  - The collector recovers layouts from the static type at each program point (Appel 1989; Goldberg 1991). Polymorphism requires either type parameters passed at run time (Tolmach 1994) or reconstruction.
  - Compiler-emitted per-program-point tables are reported as "a modest fraction" of code size (Diwan et al. 1992).
- **Replacing runtime capability handles by statically assigned slots requires a slot assignment that is valid under every interleaving.** In an exhaustive toy model of two parallel threads without synchronization, the minimum number of slots is `maxlive(A) + maxlive(B)`. A slot assignment that is optimal for one schedule is invalid under another. A barrier lets slots be reused across phases. This is a toy-model result, not a property of any production compiler.

## Applicability

The subjects in `REPORT.json` are compared, not combined. Each is examined on its own representation, and the findings relate them through a common cost vocabulary: bytes per pointer slot, bytes per object, validity invariant, and check cost.

| Subject | What was examined | Executed here? |
|---|---|---|
| SoftBound+CETS (`santoshn/softboundcets-34`, pinned) | `softboundcets-lib/softboundcets.h`, `softboundcets.c`, `Makefile` | Header compiled with GCC 15.2.0 (`-fsyntax-only`, static assertions); instrumented programs **not** run |
| LowFat (`GJDuck/LowFat`, pinned) | `config/lowfat-config.c`, `config/sizes.cfg`, `config/sizes2.cfg`, `compiler-rt/lib/lowfat/lowfat.h`, `README.md` | Configuration generator built and run; generated `lowfat_heap_select` compiled into a harness; the instrumented LLVM 4.0 toolchain **not** built |
| OpenJDK HotSpot (`openjdk/jdk`, pinned, JDK 28 development line per `make/conf/version-numbers.conf`) | `oops/compressedOops.{hpp,cpp,inline.hpp}`, `oops/compressedKlass.hpp`, `runtime/arguments.cpp`, `runtime/globals.hpp` | Source only |
| Eclipse Temurin 25.0.5+8 release archive (sha256 in `REPORT.json`) | `java` ergonomics and logs; a footprint microbenchmark | Executed. This is a different, released code line (JDK 25), not the pinned source |
| V8 (`v8/v8`, pinned) | `include/v8-internal.h`, `src/common/ptr-compr.h`, `src/common/ptr-compr-inl.h` | Source only; no V8 binary run |
| Linux kernel commit removing MPX (`torvalds/linux`, pinned) | Commit message and size | Not applicable |
| Papers and documents listed in `REPORT.json` | Abstracts and, where noted, full text | Not applicable |

- **Host for all executions.**
  - Linux 7.1 x86-64 virtual machine, Intel Xeon CPU @ 2.60 GHz, 96 vCPUs, 236 GiB RAM.
  - GCC 15.2.0, Python 3.13.
  - Timing numbers from this host are indicative only.
- **Version-specific HotSpot behaviour.**
  - Temurin 25.0.5 defaults to `UseCompactObjectHeaders=false` (measured). The pinned `openjdk/jdk` source declares it `true`.
  - In Temurin 25.0.5, `UseCompressedClassPointers` is accepted with a deprecation warning ("deprecated in version 25.0", measured). `globals.hpp` at the pinned revision declares no such flag. That is an observation about that one file, not about every flag table in the tree.
- **Scope of the MPX findings.** They describe the hardware and software stack evaluated by Oleksenko et al. They are historical: GCC 9 removed MPX support, and the pinned kernel commit removed MPX handling from `arch/x86`.
- **Scope of the slot-assignment result.** It is a toy model defined entirely inside this report (`support/slot_assignment_toy.py`). It characterizes an obligation, not an implementation.

## Findings

### 1. A cost vocabulary for runtime pointer metadata

Let `P` be the number of pointer-holding memory slots, `O` the number of live objects, `s_i` the requested size of object `i`, and `c(s)` the allocated size of the class chosen for request `s`.

| Scheme | Metadata location | Bytes per in-memory pointer slot | Bytes per object | Main validity condition | Basis |
|---|---|---|---|---|---|
| SoftBound+CETS (pinned runtime, `SPATIAL_TEMPORAL`) | Two-level shadow trie indexed by the slot's address | 32 (base, bound, key, lock) | One 8-byte lock location per allocation (the runtime also reserves a 256 MiB free map) | Pointer slots 8-byte aligned; 48-bit address space covered by a 2^23 × 2^22 trie | source + execution (compiler) |
| SoftBound (PLDI 2009 prototype, spatial only) | Hash table (24-byte entries) or shadow space (16-byte entries) | 24 or 16 | 0 | Shadow space: heap and stack each confined to one eighth of the address space | documentation (paper full text) |
| Intel MPX | Bounds directory → bounds tables, walked by the CPU | 32 per BT entry (lower, upper, pointer value, reserved) | 0 | Pointer value stored in the BT entry must match the loaded pointer, otherwise bounds become "always true" | documentation (paper full text) |
| LowFat (software, x86-64) | None. Bounds are recovered from the pointer value | 0 | `c(s) − s` rounding waste | Objects size-aligned inside 32 GiB per-class regions; base computed via 64-bit reciprocal | source + execution |
| Low-fat pointers (Kwon et al., hardware) | Compressed base/bound fields inside the 64-bit word, 46-bit address | 0 | Rounding waste, "worst-case memory overhead of 3%" | Hardware-tagged, unforgeable words | documentation (abstract) |
| HotSpot compressed oops | None (encoding) | −4 per reference field or array slot, if alignment allows | Header 12 B (default) or 8 B (compact headers) | Heap within `2^(32+shift)` of base | source + execution |
| V8 pointer compression | None (encoding) | −4 per tagged field | — | All compressible objects inside one 4 GiB cage | source + documentation |

The scaling consequences follow from this table (Basis: derived).

- **Disjoint metadata.** Metadata bytes ≈ `32·P` for SoftBound+CETS or MPX.
  - Pointer-dense data structures pay most: a linked list of 16-byte nodes, each with one pointer, adds 32 bytes of metadata per node.
  - Pointer-free buffers pay nothing.
  - The shadow regions are reserved with `MAP_NORESERVE` and committed per touched page, so the resident cost is `32·P` rounded up to whole 4 KiB pages of shadow.
- **Low-fat.** Extra bytes = `Σ (c(s_i) − s_i)`, independent of `P`. The cost is paid per object, not per pointer.
- **Compression.** Saved bytes = 4 × (number of reference slots whose removal reduces the object's aligned size). This can be 0 for many object shapes (§5).

### 2. SoftBound+CETS: disjoint shadow-trie metadata (pinned runtime)

`softboundcets-lib/softboundcets.h` lines 64–114 define the trie entry. With `-D__SOFTBOUNDCETS_SPATIAL_TEMPORAL`, which is the only `CFLAGS` setting in `softboundcets-lib/Makefile`, the entry has four fields:

```c
  void* base;
  void* bound;
  size_t key;
  void* lock;
#define __SOFTBOUNDCETS_METADATA_NUM_FIELDS 4
```

The address-to-entry map (lines 768 and 781) is:

```c
  primary_index = (ptr >> 25);
  ...
  size_t secondary_index = ((ptr >> 3) & 0x3fffff);
```

The table geometry (lines 181 and 188) is 2^23 primary entries and 2^22 secondary entries:

```c
static const size_t __SOFTBOUNDCETS_TRIE_PRIMARY_TABLE_ENTRIES = ((size_t) 8*(size_t) 1024 * (size_t) 1024);
static const size_t __SOFTBOUNDCETS_TRIE_SECONDARY_TABLE_ENTRIES = ((size_t) 4 * (size_t) 1024 * (size_t) 1024);
```

Basis: source + execution (compiler).

- **Entry size, checked by the compiler.** `support/sbcets_layout_probe.sh` compiles the header with GCC 15.2.0 and checks `sizeof(__softboundcets_trie_entry_t) == 32` and `__SOFTBOUNDCETS_METADATA_NUM_FIELDS == 4` as C11 static assertions. Both hold. Execution covers the compiler only.
- **Derived geometry.**
  - Each secondary table covers 2^22 slots × 8 bytes = 32 MiB of program address space and reserves 2^22 × 32 bytes = 128 MiB of virtual memory.
  - The primary table reserves 2^23 × 8 bytes = 64 MiB.
  - 2^23 × 32 MiB = 2^48 bytes, which is the 48-bit user address space.
  - Secondary tables are created lazily by `__softboundcets_trie_allocate` (line 350) with `MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE`.
- **Temporal metadata reservations** (`softboundcets.c` lines 120–169).
  - Lock locations: 64 Mi entries × 8 bytes = 512 MiB, reserved.
  - Free map: 32 Mi entries × 8 bytes = 256 MiB.
  - Shadow stack for passing metadata across calls: 4096 entries.
- **Configuration defect observed with GCC.** The single-component configurations do not compile with GCC 15.2.0 at this revision.
  - Both `-D__SOFTBOUNDCETS_SPATIAL` and `-D__SOFTBOUNDCETS_TEMPORAL` fail with `softboundcets.h:1293:4: error: too many arguments to function '__softboundcets_metadata_load'`.
  - In those configurations `__softboundcets_metadata_load` is declared with three parameters (lines 883 and 888). The vector helpers still pass five arguments. Line 1293 is `__softboundcets_metadata_load((void*) addr, base, bound, key, lock);` and line 1307 is `__softboundcets_metadata_store((void*)addr, base, bound, key, lock);`.
  - Clang was not tested.
  - The default build also triggers a GCC-specific refusal: GCC rejects `always_inline` on weak functions. The probe neutralizes that attribute only for the size check.
- **Published costs of the original systems** (Basis: documentation, full text of the PLDI 2009 paper and the CETS abstract):
  - SoftBound, full checking: 67% average runtime overhead with the shadow space, 93% with the hash table.
  - SoftBound, store-only checking: 22% (shadow space) and 54% (hash table).
  - SoftBound dynamic instruction count: +133% (shadow space) and +173% (hash table).
  - SoftBound memory (4 KiB pages touched): 64% average and 200% worst case for the shadow space (one 16-byte entry per 64 bits of memory); 87% average and 300% worst case for the hash table (24-byte entries).
  - Shadow-space lookup: about 5 x86 instructions; hash-table lookup: about 9.
  - CETS: 48% average runtime overhead; spatial plus temporal checking together: 116%.
  - These measurements predate the pinned SoftBound+CETS runtime, whose entry is 32 bytes. Its memory overhead was **not measured** here.

### 3. Intel MPX: CPU-walked bounds tables

Oleksenko et al. (arXiv full text, §3) describe the two-level structure. Basis: documentation.

- The CPU extracts the bounds-directory (BD) offset from address bits 20–47 of the pointer's *storage location* and loads an 8-byte BD entry. It then uses bits 3–19 for the offset of a 32-byte bounds-table (BT) entry.
- Each BT entry also stores the pointer value. On a mismatch, for example when uninstrumented code has written the slot, the bounds become INIT ("always true"). This is the interoperability rule.
- There is no dedicated metadata cache: BT entries compete with application data in the normal caches.
- Only four bounds registers exist (`BND0`–`BND3`).
- BTs are allocated on demand by the operating system after a `#BR` exception.

Derived geometry: one BT covers 2^17 slots × 8 bytes = 1 MiB of pointer-storage address space and occupies 2^17 × 32 bytes = 4 MiB. The worst-case metadata is 4× the pointer-holding memory, the same per-slot ratio as SoftBound+CETS's 32-byte entries.

Measured costs as reported by the paper (Basis: documentation):

- about 50% average runtime overhead;
- up to 4× slowdown in the worst case;
- 2.1× average memory overhead under ICC and 1.9× under GCC, compared with 2.8× for AddressSanitizer;
- no temporal-safety detection;
- possible false positives and false negatives in multithreaded code.

Two versions of the paper exist and are distinct:

- arXiv:1702.00719 v2, *An Empirical Study of Intel MPX and Software-based Bounds Checking Approaches*;
- the SIGMETRICS/POMACS version, DOI 10.1145/3224423, *A Cross-layer Analysis of the Intel MPX System Stack*.

The full-text numbers above come from the arXiv version.

Removal (Basis: source): the pinned kernel commit "x86/mpx: remove MPX from arch/x86" (2020-01-23) states "MPX is being removed from the kernel due to a lack of support in the toolchain going forward (gcc)". It deletes 1567 lines and keeps only XSAVE state support for KVM guests. The GCC 9 release notes state "Support of Intel MPX (Memory Protection Extensions) has been removed."

### 4. LowFat (software low-fat pointers): bounds from the pointer value

The encoding (`lowfat.h` lines 71–114; generated `lowfat_config.h`) works as follows. Basis: source + execution.

```c
idx  = (uintptr_t)ptr / _LOWFAT_REGION_SIZE;          /* region = size class; _LOWFAT_REGION_SIZE = 2^35 */
size = _LOWFAT_SIZES[idx];
base = (void *)(((unsigned __int128)_LOWFAT_MAGICS[idx] * ptr >> 64) * size);  /* non-power-of-two mode */
base = (void *)((uintptr_t)ptr & _LOWFAT_MAGICS[idx]);                         /* power-of-two mode */
```

- **The generator was run.** `support/lowfat_rounding_probe.sh` builds `config/lowfat-config.c` and runs `lowfat-config sizes.cfg 32` and `lowfat-config sizes2.cfg 32`.
  - The default configuration produced `LOWFAT_NUM_REGIONS 61`, `LOWFAT_REGION_SIZE_SHIFT 35` (32 GiB regions) and `LOWFAT_MAX_HEAP_ALLOC_SIZE 8589934592`.
  - `sizes.cfg` lists 64 sizes, but the generator drops sizes above `region_size / 4` (`lowfat-config.c` line 327: `size_t MAX_SIZE = region_size / 4;`).
  - The power-of-two configuration produced 30 regions.
  - Region 1 begins at 0x800000000. The first 32 GiB holds the program's ordinary segments, as documented in the README.
- **Precision error at large sizes.**
  - For non-power-of-two classes the generator computes `magic = 2^64 / size + 1` (line 419). It then binary-searches, for every object in the region, how many trailing bytes would be attributed to the wrong base.
  - The errors are 0 bytes for classes up to region 51 (size 8 MiB), then 1 B at 16 MiB, rising to 995 B at 8 GiB (region 61).
  - These values are identical to the cached `config/lowfat.errs` rows for 32 GiB regions at the pinned revision.
- **One-past-the-end padding is compiled into the allocator.** `lowfat-config.c` line 797 emits `if (size <= %zu-1-%zu)`, that is `size ≤ class − 1 − error`. The generated `lowfat_heap_select` therefore sends a request of exactly the class size to the next class.
  - Measured with the compiled harness:
    - default configuration: `malloc(16)` → 32-byte class, `malloc(4096)` → 4112-byte class, `malloc(4095)` → 4096-byte class;
    - power-of-two configuration: `malloc(4096)` → 8192-byte class.
  - The 2^k + 16 entries in `sizes.cfg` (272, 528, 1040, 2064, 4112, 8208) absorb power-of-two requests up to 8 KiB. Above 8208 the classes are pure powers of two, so power-of-two requests of 16 KiB and above double.

Allocated/requested ratios for synthetic request sets, measured with the upstream-generated selector. The request sets are synthetic distributions, not workloads.

| Request set | Default `sizes.cfg`: Σalloc/Σreq | Default: worst alloc/req | Power-of-two `sizes2.cfg`: Σalloc/Σreq | Power-of-two: worst |
|---|---|---|---|---|
| uniform 1..4096 | 1.0819 | 16.0 (1 B → 16) | 1.3340 | 16.0 |
| uniform 1..65536 | 1.3197 | 16.0 | 1.3334 | 16.0 |
| powers of two 16..4096 (9 sizes) | 1.0176 | 2.0 | 2.0000 | 2.0 |
| powers of two 16..1 MiB (17 sizes) | 1.9923 | 2.0 | 2.0000 | 2.0 |
| 2^k − 8, 24..4088 (8 sizes) | 1.0079 | 1.333 | 1.0079 | 1.333 |

Reported costs (Basis: documentation, LowFat `README.md` at the pinned revision):

- SPEC CPU2006 runtime overhead: 64% in the default configuration;
- about 9.8% with `-lowfat-no-check-reads`, `-lowfat-no-check-escapes` and `-lowfat-no-check-fields`;
- about 7.8% additionally with power-of-two sizes;
- memory overhead "very low (~3%)", rising to about 12% with power-of-two sizes;
- an independent survey (Song et al., *SoK: Sanitizing for Security*, IEEE S&P 2019, as quoted by the README) measured legacy mode at about 85%;
- 59% when built close to the CC 2016 paper's configuration.

The README states that sub-object (intra-struct) overflows are explicitly out of scope. The stack extension (Duck, Yap and Cavallaro, NDSS 2017) uses pointer mirroring and memory aliasing, and claims compatibility with `alloca`, `setjmp`/`longjmp`, exceptions and threads (Basis: documentation, abstract).

Hardware low-fat pointers (Kwon et al., CCS 2013; Basis: documentation, abstract):

- approximate base and bound plus an exact 46-bit address in one 64-bit word;
- worst-case memory overhead of 3%;
- checks in parallel hardware with 0% runtime overhead;
- 4 ns cycle and about 1100 6-LUTs on a Virtex-6 FPGA implementation.

These are claims about the paper's FPGA implementation, not a deployed processor.

### 5. HotSpot compressed object and class pointers

The four narrow-oop modes are defined in `compressedOops.hpp` lines 55–72 and decoded by `compressedOops.inline.hpp` line 51. Basis: source + execution.

```c
return cast_to_oop((uintptr_t)base() + ((uintptr_t)v << shift()));      // decode_raw
narrowOop result = narrow_oop_cast(pd >> shift());                      // encode_not_null, pd = v - base (line 72)
```

`CompressedOops::mode()` (`compressedOops.cpp` lines 111–125) returns:

- `DisjointBaseNarrowOop` if the base is non-null and has no bits in common with `0xFFFF…FFFF >> (32 − LogMinObjAlignmentInBytes)`;
- otherwise `HeapBasedNarrowOop` if the base is non-null;
- otherwise `ZeroBasedNarrowOop` if the shift is non-zero;
- otherwise `UnscaledNarrowOop`.

`initialize` (lines 57–66) sets the shift when the reserved heap end exceeds `UnscaledOopHeapMax = 2^32`, and sets a null base when the end is at most `OopEncodingHeapMax`.

- **Ergonomics and limits.**
  - `arguments.cpp` line 1419: `OopEncodingHeapMax = (uint64_t(max_juint) + 1) << LogMinObjAlignmentInBytes`.
  - `max_heap_for_compressed_oops()` (lines 1422–1434) subtracts a null-page displacement aligned to the conservative maximum heap alignment.
  - `set_use_compressed_oops()` (lines 1443–1452) turns the flag on ergonomically only if the maximum heap fits. If the user forced it on, it warns "Max heap size too large for Compressed Oops" and turns it off.
  - The pinned `globals.hpp` also adds a diagnostic flag `AOTCompatibleOopCompression` (line 127). When set, it "Always use[s] HeapBasedNarrowOop mode, so that AOT code will always work regardless of runtime heap range". This trades decode cost for code portability.
- **Measured mode selection** (Temurin 25.0.5+8, G1, `-Xlog:gc+heap+coops=debug`; `support/coops_probe.sh`):

| `-Xmx` (alignment 8) | Mode reported |
|---|---|
| 1g | `32-bit` (unscaled), heap at 0xc0000000 |
| 3g, 4g, 16g | `Zero based`, shift 3 |
| 31g | `Non-zero disjoint base: 0x0000001000000000`, shift 3 |
| 32g, 33g | compressed oops off (`UseCompressedOops = false {default}`) |
| 33g, 60g with `ObjectAlignmentInBytes=16` | `Zero based`, shift 4 |
| 64g with `ObjectAlignmentInBytes=16` | off |

- **Measured footprint.**
  - Workload: 4,000,000 instances per measurement, heap used after repeated `System.gc()`, `-Xms2g -Xmx2g -XX:+UseSerialGC`, three repetitions per flag set.
  - The bytes per object and per slot were identical in all three repetitions.
  - Object shapes: `Node {Node next; int value;}`, `Pair {Pair left, right; int value;}`, and `java.lang.Object`.

| Flags | Node | Pair | `Object[]` slot | `Object` |
|---|---|---|---|---|
| default (compressed oops, 12-byte header) | 24 | 24 | 4 | 16 |
| `-XX:-UseCompressedOops` | 24 | 32 | 8 | 16 |
| `-XX:+UseCompactObjectHeaders` | 16 | 24 | 4 | 8 |
| both | 24 | 32 | 8 | 8 |

Derived from the table: with 8-byte alignment, compressed oops save 8 bytes only when two 4-byte savings coincide, or when a 4-byte saving crosses an 8-byte boundary.

- `Node` is 12 + 4 + 4 = 20 → 24 B with compression, and 12 + 4 + 8 = 24 B without, so it saves nothing.
- `Pair` is 12 + 4 + 4 + 4 = 24 B versus 12 + 4 + 8 + 8 = 32 B, a saving of 25%.
- Compact headers save 8 bytes per header-only object.
- The JDK enhancement proposals report "live data is typically reduced by 10%–20%" and 22% less heap with 8% less CPU on SPECjbb2015 in one setting (JEP 450 / JEP 519; Basis: documentation).

- **Traversal timing.** Best-of-seven pointer chasing over the `Node` list measured 2.5–5.4 ns per node across all flag sets in the preserved run. The difference between flag sets is within run-to-run variation, so this probe **does not resolve** the time cost of decoding.
- **Narrow class pointers.**
  - `compressedKlass.hpp` lines 109–117: 32 bits with maximum shift 3 normally, and 22 bits with maximum shift 10 under compact headers.
  - Measured with `-Xlog:gc+metaspace=info`:
    - default: `Narrow klass pointer bits 32, Max shift 3 … Narrow klass shift: 0`;
    - with `-XX:+UseCompactObjectHeaders`: `bits 22, Max shift 10 … shift: 10`.
    - Both cover a 4 GiB encoding range.
  - JEP 450 states that the only reason to disable compressed class pointers is an application loading "more than about four million classes". It also states that compact headers are disabled for heaps above 8 TB unless ZGC is used.

### 6. V8 pointer compression

From `include/v8-internal.h` lines 164–176 (Basis: source):

```c
#ifdef V8_COMPRESS_POINTERS
constexpr size_t kPtrComprCageReservationSize = size_t{1} << 32;
constexpr size_t kPtrComprCageBaseAlignment = size_t{1} << 32;
const int kApiTaggedSize = kApiInt32Size;
```

In `src/common/ptr-compr-inl.h`:

- Line 35: `kPtrComprCageBaseMask = ~(kPtrComprCageBaseAlignment - 1)`.
- `DecompressTagged` (lines 115–131) computes `Address result = cage_base | static_cast<Address>(raw_value);`. OR is valid because the base is 4 GiB-aligned.
- `CompressObject` simply truncates to 32 bits, with a debug-only check that the upper half equals the cage base.
- `ptr-compr.h` keeps the main cage base either process-wide (`V8_COMPRESS_POINTERS_IN_SHARED_CAGE`) or `thread_local` (multiple cages).
- A separate `TrustedCage` scheme exists under `V8_ENABLE_SANDBOX`.
- Smis carry 31-bit payloads under compression. With `V8_COMPRESS_POINTERS`, `kApiTaggedSize` is 4, so `PlatformSmiTagging = SmiTagging<kApiTaggedSize>` (lines 182–186) selects the 31-bit layout (`kSmiValueSize = 31`, line 86). `V8_31BIT_SMIS_ON_64BIT_ARCH` forces the same layout without compression.

The V8 team's write-up ("Pointer Compression in V8", 30 March 2020; Basis: documentation) reports:

- Tagged values were about 70% of the V8 heap on real-world pages.
- Pointer compression reduced V8 heap size by up to 43% and Chrome renderer memory by up to 20% on desktop.
- The first working implementation had a ~35% regression gap, closed by successive optimizations:
  - branchful decompression: +7%;
  - decompression elimination: +2%;
  - "Smi-corrupting" unconditional base addition: +2.5%;
  - and others.
- Giving up 32-bit Smis cost 1%, and double-field unboxing cost 3%.
- Heaps are limited to 4 GB per cage. The write-up names 8–16 GB heaps as future work.

Whether a given embedder build enables `V8_COMPRESS_POINTERS` was **not examined**.

### 7. Compressed pointers outside production VMs

These are published results (Basis: documentation, abstracts).

- **Lattner and Adve (MSP 2005)** apply an automatic, "macroscopic" per-data-structure compression of 64-bit pointers to 32-bit indices.
  - Each data-structure instance may grow up to 2^32 bytes.
  - Peak heap fell by 20% to 2× on several pointer-intensive benchmarks.
  - A dynamic expansion variant is described but was not implemented.
- **Venstermans, Eeckhout and De Bosschere (ECOOP 2007)** use object-relative 32-bit offsets (ORA) in Jikes RVM on POWER4.
  - ORA works for heaps above 4 GB.
  - Total memory fell by 10% on average and by up to 14.5%.
  - The overhead was statistically insignificant on average.

### 8. Tag-free collection: static information that replaces per-object metadata

Basis: documentation (abstracts).

| Work | Static information used | Where runtime metadata goes | Reported cost |
|---|---|---|---|
| Appel 1989 | Static polymorphic types encoded "once—in the program—rather than replicated many times in the data". A tag remains for user-defined variant records | Per-program-point type descriptions | "can lead to savings both in space and time" (not quantified in the abstract) |
| Goldberg 1991 | Compiler-generated, program-specific GC routines, for monomorphic and polymorphic languages | Code (GC routines per type or program point) | "no time overhead during execution other than the cost of the garbage collection process itself" |
| Tolmach 1994 | Explicit second-order type parameters derived from Hindley–Milner inference, manipulated lazily | Runtime type parameters passed with polymorphic calls | "overhead of passing type information explicitly can be made acceptably small" (preliminary) |
| Diwan, Moss and Hudson 1992 | Tables of live pointers and derived pointers at every GC point of optimized code | Compressed per-GC-point tables | Tables "a modest fraction of the size of the optimized code"; stack tracing "a small fraction of total gc time" |

The general pattern (Basis: derived) is that per-object metadata becomes per-code-position metadata.

- Space moves from `O(objects)` to `O(GC points × live slots)`.
- Time moves from header decoding to stack walking and table decoding at collection time.
- Polymorphism and existential types are the cases that force some runtime type evidence back into the data or into frames.

### 9. Obligations for replacing runtime capability handles by statically assigned slots

A *capability handle* is a runtime value that names a memory cell and carries a permission. Erasing handles to compile-time names requires a compiler to discharge the obligations below. Basis: derived, plus a toy-model execution for O3.

- **O1, simultaneous-liveness assignment.**
  - For each program point `p`, the set `Live(p)` of handles that may be used later must get pairwise-distinct slots.
  - In straight-line code this is interval-graph colouring. The number of slots needed equals the maximum live count, and the left-edge greedy algorithm achieves it.
- **O2, permission recoverable from position.** The permission a handle would carry (owner, shared borrow, released) must be a function of the program point, as in tag-free collection, where the layout is a function of the program point. Where it depends on data, a runtime tag or a per-branch slot map is still needed.
- **O3, interference under every schedule.**
  - For `A ∥ B`, two handles conflict if *some interleaving* makes them simultaneously live.
  - Toy model (`support/slot_assignment_toy.py`, exhaustive interleavings, brute-force colouring, 300 random programs × 2 seeds; this is a toy model, not a compiler):
    - With no synchronization, the minimum slot count equalled `maxlive(A) + maxlive(B)` in 300/300 programs for each seed.
    - With one barrier and every handle confined to one phase, it equalled `max over phases p of maxlive(A_p) + maxlive(B_p)` in 300/300.
    - The assignment that is optimal for the single schedule "A runs to completion, then B" was invalid under some interleaving in 300/300. That is expected, since that schedule never overlaps the two threads.
  - Consequence: a slot assignment needs a may-happen-in-parallel analysis or a synchronization structure, not a schedule observed in testing.
- **O4, release placement.** A slot may be reused only after the last use on every path and every schedule. Under borrows, reuse requires knowing which handles were derived from which owner. This is the same non-local information that origin- or loan-based borrow checkers compute.
- **O5, interaction with existing compressed representations.** If slots are indices into a region, the region base must be invariant for the region's lifetime. This is the HotSpot and V8 cage condition.

Published treatment of O1, O2 and O4 exists in register allocation, tag-free GC and borrow checking respectively. A published treatment of O3 for capability-handle erasure specifically was **not found**.

### 10. Performance and resource footprint across levels

| Level | SoftBound+CETS | Intel MPX | LowFat | HotSpot compressed oops / compact headers | V8 pointer compression | Tag-free GC |
|---|---|---|---|---|---|---|
| L1 authoring / maintenance | not measured | Paper reports MPX "restrictions on memory layout require substantial code changes for some programs" | not measured | not measured | "300+ commits" for the V8 implementation | not measured |
| L2 toolchain build | not measured (LLVM 3.4 fork not built) | not applicable (toolchain removed) | not measured (LLVM 4.0 fork not built); config generator builds in 0.75 s with `gcc -O2` (measured) | not measured | not measured | not measured |
| L3 compile / instrumentation latency | not measured | not measured | not measured | not measured | not measured | not measured |
| L4 generated-code time | 67% full / 22% store-only (shadow; paper); CETS 48%; combined 116% | ~50% average, up to 4× (paper) | 64% default, ~9.8% hardened, ~7.8% power-of-two (README) | Traversal difference not resolved on this host (2.5–5.4 ns/node across all flag sets); JEP 519: 8% less CPU on SPECjbb2015 in one setting | ~35% initial regression closed to parity (blog); 32-bit Smi loss 1% | Goldberg: no mutator overhead (abstract) |
| L5 check / verification speed | about 5 x86 instructions per shadow lookup (paper) | not measured | Base via one 128-bit multiply or one mask | not applicable | not applicable | not applicable |
| L6 memory | 32 B per pointer slot (source); paper: 64% average / 200% worst (16-byte entries) | 32 B per pointer slot; 1.9–2.1× average (paper) | ~3% / ~12% (README); synthetic rounding 1.008–1.99× (measured, §4); 32 GiB reserved per class | Slot 8 → 4 B; `Pair` 32 → 24 B; `Node` unchanged; `Object` 16 → 8 B with compact headers (measured) | Heap up to −43%, renderer up to −20% (blog) | Tables "a modest fraction" of code (Diwan) |

### 11. Comprehensibility and conceptual simplicity

- **C1, mental model.**
  - Disjoint metadata gives a local rule (every pointer carries `[base, bound)` and a key/lock pair), but it creates a non-local hazard. Uninstrumented code that writes a pointer leaves stale metadata. MPX handles this by storing the pointer value in the BT entry and degrading to "always true" bounds.
  - Low-fat replaces that hazard with an allocation-placement invariant (size-aligned within the class region). Its diagnostics are legible: the README shows the exact base, size and overflow. Its blind spot (sub-object overflow) is stated in the README, but a programmer would not infer it from the model.
  - HotSpot and V8 compression are invisible to programmers except through performance cliffs: the `-Xmx32g` discontinuity, and the 4 GiB cage.
  - The HotSpot cliff is not monotone in an obvious way. `-Xmx31g` used a disjoint base while `-Xmx16g` was zero-based.
- **C2, one invariant, several mechanisms.**
  - All the schemes enforce, or depend on, one invariant: an object's bounds or identity are recoverable from a pointer-sized word plus static or global context. They differ only in where the residual information lives: shadow memory, the CPU walk, address bits, a heap base register, a cage base register, or code positions.
  - A minimal common abstraction is "pointer = (region id, offset), with region metadata indexed by region id". Each scheme is an instance:
    - low-fat: region id is the high address bits, and the metadata is the size table;
    - compressed oops: one region with base and shift;
    - V8: one cage;
    - tag-free GC: region id is the program counter, and the metadata is the frame layout.
  - Disjoint metadata is the exception that this abstraction does not make ordinary: it indexes metadata by the pointer's storage location, not by the pointer value. That is exactly why it costs `O(P)` rather than `O(regions)`.

### 12. How implementations and claims are validated

- **V1, specification adequacy and non-vacuity.**
  - The LowFat generator validates its own reciprocal arithmetic exhaustively: it binary-searches every object in every region and emits the per-class error that the allocator then subtracts. The probe here reproduced the cached error table byte for byte.
  - HotSpot asserts reversibility in debug builds (`assert(decode_raw(result) == v, "reversibility")`, `compressedOops.inline.hpp`).
  - V8 debug-checks the cage-membership precondition of `CompressObject`.
- **V2, lowering and checker soundness.**
  - The MPX study found compiler-support bugs that caused compilation or runtime errors. The kernel removal message attributes the removal to missing toolchain support.
  - The SoftBound header compile failure in non-default configurations (§2) is a further example of configuration-space breakage that only exercising those configurations reveals.
  - Differential testing of instrumentation passes was **not examined**.
- **V3, concurrency.**
  - MPX may give false positives and negatives in multithreaded code (paper). Its BT updates are not atomic with pointer stores.
  - SoftBound+CETS uses one global trie with no synchronization visible in the `metadata_store` path quoted in §2. Its multithreaded behaviour was **not examined**.
  - The toy model in §9 shows why static slot reuse needs all-schedule interference.
- **V4, field telemetry.** The V8 savings are field-like measurements on browsing user stories. The JEP 519 numbers come from benchmarks and production use reported by vendors. No independent replication was examined.

## Boundaries

- **Not examined.**
  - Running SoftBound+CETS-, LowFat- or MPX-instrumented programs. Building the LLVM 3.4 and LLVM 4.0 forks. Any MPX hardware.
  - The memory overhead of the pinned SoftBound+CETS runtime is **not measured**. Only the 2009 prototype's numbers are cited.
  - V8 execution, embedder build flags, and whether a given Node.js, Deno or Chrome build enables pointer compression.
  - CHERI and other capability ISAs, and their compressed bounds encodings (CHERI Concentrate, for example), are out of scope here. Only the Kwon et al. hardware encoding is cited, from its abstract.
  - AddressSanitizer-style shadow memory is mentioned only through the MPX study's comparison.
  - The full text of Duck and Yap 2016, Duck et al. 2017, Kwon et al. 2013, Lattner and Adve 2005, Venstermans et al. 2007, Appel 1989, Goldberg 1991, Tolmach 1994 and Diwan et al. 1992. Only abstracts or publisher landing-page abstracts were read.
- **Unknown.**
  - The decode-time cost of compressed oops on this host. The traversal probe could not separate it from run-to-run variation.
  - Whether `UseCompressedClassPointers` has been fully removed from the pinned tree. Only `globals.hpp` was checked.
  - Whether the GCC compile failure in SoftBound+CETS's single-component configurations also occurs with Clang.
- **Known not to apply.**
  - The 4× per-slot ratio does not apply to the 2009 SoftBound spatial-only shadow space (16-byte entries, 2×) or to its hash table (24 bytes, 3×).
  - Compressed-oops savings are known to be zero for object shapes like `Node` above. "Compressed oops halve reference cost" is true per slot but false per object in general.
- **Unsupported.**
  - LowFat does not detect sub-object overflows (README).
  - MPX does not detect temporal errors (paper).
  - HotSpot does not use compressed oops at or above the encoding limit (`-Xmx32g` with 8-byte alignment, measured).
  - V8 compression does not support a cage larger than 4 GiB.
- **Stronger conclusions not established.**
  - That low-fat is "metadata-free" in total memory. Its rounding cost on real workloads is cited, not measured. The synthetic distributions show 1.008–1.99×.
  - That any production compiler discharges O3 for capability handles. The toy model shows only that the obligation is necessary and what its optimum is in that model.
  - That tag-free GC tables are always small. The only quantitative statement examined is "a modest fraction" of code size.

## Evidence

Evidence acquired 2026-11-20 (UTC).

- **Git sources** (full revisions in `REPORT.json`):
  - `santoshn/softboundcets-34`:
    - `softboundcets-lib/softboundcets.h`: lines 64–114 (entry), 181/188 (trie sizes), 350–356 (`__softboundcets_trie_allocate`), 768/781 (index computation), 883/888 (three-argument loads), 1293/1307 (five-argument vector calls);
    - `softboundcets-lib/softboundcets.c` lines 116–170 (`mmap` reservations);
    - `softboundcets-lib/Makefile` (`CFLAGS=… -D__SOFTBOUNDCETS_SPATIAL_TEMPORAL`).
  - `GJDuck/LowFat`:
    - `config/lowfat-config.c`: lines 88–160 (error computation), 327 (`MAX_SIZE`), 419/428 (magic numbers), 797 (`size <= class-1-error`);
    - `config/sizes.cfg` (sha256 `9b9d3bf5e0f035f1b0a682180bde2e7731b4bfaf1ae0f57138114f25d12a4af2`);
    - `config/sizes2.cfg` (sha256 `e48b47131dd66a4214f61b40c4c713b65a17000d3dd8a19f0089a080f1453ccb`);
    - `config/lowfat.errs`;
    - `llvm-4.0.0.src/projects/compiler-rt/lib/lowfat/lowfat.h` lines 71–136;
    - `README.md` lines 180–230 and 370–401.
  - `openjdk/jdk`:
    - `src/hotspot/share/oops/compressedOops.hpp` 55–72;
    - `compressedOops.cpp` 49–87 and 111–159;
    - `compressedOops.inline.hpp` 50–74;
    - `compressedKlass.hpp` 40–117;
    - `src/hotspot/share/runtime/arguments.cpp` 1419–1454;
    - `src/hotspot/share/runtime/globals.hpp` 123–137;
    - `make/conf/version-numbers.conf` (`DEFAULT_VERSION_FEATURE=28`).
  - `v8/v8`:
    - `include/v8-internal.h` 164–195;
    - `src/common/ptr-compr-inl.h` 35–131;
    - `src/common/ptr-compr.h` 20–80.
  - `torvalds/linux`: commit "x86/mpx: remove MPX from arch/x86" (message, 1 addition / 1567 deletions, 15 files).
- **Release artifact.** Eclipse Temurin `OpenJDK25U-jdk_x64_linux_hotspot_25.0.5_8.tar.gz`, from the GitHub release `adoptium/temurin25-binaries` tag `jdk-25.0.5+8`, sha256 `68982529869257d0ee6b824ec5aa270ff8b118bb438670da0b97ebdab178d7fb` (verified against the release's `.sha256.txt`). `release` reports `JAVA_RUNTIME_VERSION="25.0.5+8-LTS"`.
- **Execution** (scripts and raw outputs in `support/`; run with `_JAVA_OPTIONS`, `JAVA_TOOL_OPTIONS` and `JDK_JAVA_OPTIONS` unset):
  - `support/sbcets_layout_probe.sh` → `support/sbcets_layout_probe.out`;
  - `support/lowfat_rounding_probe.sh` → `support/lowfat_rounding_probe.out`;
  - `support/coops_probe.sh` with `support/CoopsFootprint.java` → `support/coops_probe.out`;
  - `support/slot_assignment_toy.py` (`python3 slot_assignment_toy.py 1 300; python3 slot_assignment_toy.py 2 300`) → `support/slot_assignment_toy.out`.
- **Literature.** DOIs and arXiv identifiers are in `REPORT.json`. Every DOI was confirmed as registered through the doi.org handle API, and bibliographic data was matched against OpenAlex records. Full text was read for:
  - SoftBound (PLDI 2009, the author-hosted PDF);
  - Intel MPX Explained (arXiv:1702.00719 v2).
- **Documents.**
  - V8 blog "Pointer Compression in V8" (2020-03-30), https://v8.dev/blog/pointer-compression;
  - JEP 450 and JEP 519 (openjdk.org/jeps/450, /519);
  - GCC 9 release notes (https://gcc.gnu.org/gcc-9/changes.html).

## Revalidation

- **SoftBound+CETS entry size.** Run `support/sbcets_layout_probe.sh` (needs `curl` and `gcc`). It must print `static assertions hold`. For another revision, diff `softboundcets-lib/softboundcets.h` lines 59–114 and the index expressions `>> 25` and `(ptr >> 3) & 0x3fffff`.
- **LowFat classes and padding.** Run `support/lowfat_rounding_probe.sh`.
  - The spot checks must read `16 32 2; 4096 4112 34` for `sizes.cfg`.
  - Region 61 must report `error=995B`.
  - Any change in line 797 of `lowfat-config.c` invalidates §4.
- **HotSpot modes and footprint.** Run `support/coops_probe.sh` (downloads the pinned Temurin archive and checks its sha256). For a different JDK, compare the mode column and the four footprint numbers.
  - Before reusing the "default" row on a newer JDK, check `globals.hpp` for the `UseCompactObjectHeaders` default.
  - The cheapest single check is `java -Xmx31g -Xlog:gc+heap+coops=debug -version`.
- **V8.** Diff `include/v8-internal.h` around `kPtrComprCageReservationSize`, and `DecompressTagged` in `src/common/ptr-compr-inl.h`. A change from `|` to `+` or a change of the cage size alters §6.
- **Slot-assignment toy.** Run `python3 support/slot_assignment_toy.py <seed> <trials>`. All three lines must report full agreement (N/N). This checks only the toy model.
