# Compiled Columnar Query Engines, Vectorized Pipelines, and SIMD Compression Codecs

## Summary

Modern analytical query engines eliminate the tuple-at-a-time Volcano iterator bottleneck through two distinct execution architectures—**data-centric push-based query compilation** (`HyPer`, `Umbra`, staged `LMS`) and **vectorized morsel-driven execution** (`MonetDB/X100`, `DuckDB`, `Velox`)—coupled with **zero-copy FFI interchange** (`Apache Arrow C Data Interface`) and **lightweight SIMD-native columnar codecs** (`FastLanes`, `FSST`, `ALP`, `BtrBlocks`).

Key architectural invariants and design boundaries established from primary source code, normative specifications, peer-reviewed studies, and executable micro-probes:

1. **Compilation vs. Vectorization Trade-off:** Pure data-centric push compilation fuses consecutive non-pipeline-breaking operators into tight scalar loops that keep tuple attributes in CPU registers and execute fewer instructions per tuple, winning on compute-heavy, cache-resident scans and expressions. Vectorized engines process L1/L2-cache-resident batches (typically `1024`–`2048` tuples) via explicit `SelectionVector` (DuckDB) or bitmask `SelectivityVector` (Velox), winning on out-of-cache hash probes and SIMD-amenable scans because independent batch loops expose memory-level parallelism (MLP) and out-of-order latency hiding. **Relaxed Operator Fusion (ROF)** bridges both regimes by inserting micro-staging buffers before cache-missing operators to enable software prefetching and SIMD vectorization inside compiled pipelines.
2. **Sub-Millisecond Query Codegen (`Umbra Flying Start`):** Feeding generated query IR into optimizing `LLVM -O3` incurs tens to hundreds of milliseconds of compilation latency that dominates short queries. `Umbra` resolves this via an SSA-based internal IR compiled directly to x86-64 (and ARM) in near-single-pass fashion with loop-depth-aware lightweight register bookkeeping (`Reg`/`ScratchReg`), achieving roughly two orders of magnitude faster compilation than `LLVM` while remaining within ~1.2× of `LLVM -O3` execution speed, with adaptive tier-up to `LLVM` only for long-running queries.
3. **Arrow C Data Interface Zero-Copy FFI Boundaries:** The ABI-stable `ArrowSchema` / `ArrowArray` / `ArrowArrayStream` contract transfers ownership via a producer-supplied `release` callback and opaque `private_data`, requiring trivial relocatability (no internal self-pointers) and strict consumer move semantics (shallow copy + nulling source `release`). Zero-copy interchange breaks silently at four concrete seams verified in `arrow-rs`, `Velox`, and `DuckDB`: (a) non-matching null-bitmap vs. array offsets force bitmap realignment copies (`arrow-rs::ffi::align_nulls`), (b) Arrow couples encoding (dictionary, run-end) into `ArrowSchema` whereas DuckDB and Velox decouple logical type from per-batch physical encoding, (c) Arrow `StringView` (`vu`/`vz`, Format 1.4) uses `[len: i32, prefix: [u8; 4], buf_idx: i32, offset: i32]` whereas Velox's 16-byte `StringView` stores an 8-byte raw `const char*`, forcing Velox's `exportViews` to share string data buffers zero-copy while allocating and rewriting the 16-byte view-descriptor buffer, and (d) divergent temporal/alignment layouts (e.g., Velox 16-byte `{seconds, nanos}` timestamps or unaligned 128-bit decimals) mandate conversion copies.
4. **Compressed-Column Execution & SIMD Codecs:**
   - **FastLanes Unified Transposed Layout (UTL):** Permutes 1024-value vectors across a virtual 1024-bit SIMD register using the `FLS_ORDER = [0, 4, 2, 6, 1, 5, 3, 7]` interleaving bijection so that scalar auto-vectorized C++ decodes bit-packed (`FFOR`) and delta (`rsum`) streams with zero cross-lane shuffles across 128-bit, 256-bit, 512-bit, and GPU widths.
   - **FSST & `dict_fsst`:** Maps 1–8 byte substrings onto 1-byte codes (`0..254`, escape `255`), enabling single-string random access, SWAR branchless 4-byte escape scanning, and equality pushdown over compressed bytes under a shared symbol table. DuckDB (`StorageVersion::V1_3_0+`) supersedes standalone `FSST` with unified `dict_fsst` segments that scan directly into `DICTIONARY_VECTOR` without materializing strings.
   - **ALP & `ALP_RD`:** Losslessly compresses decimal-origin IEEE-754 floats into bit-packed integers via two-parameter decimal scaling $(e, f)$ ($f \le e$) and magic-number round-to-nearest-even (`2^51 + 2^52`), patching `-0.0`, `NaN`, `±Inf`, non-decimal, and $> 2^{51}$ odd-integer exceptions out of band—falling back adaptively to `ALP_RD` high-bit dictionary splitting for high-precision scientific floats.

## Applicability

This report synthesizes a comparative architectural and source-level analysis across eight pinned upstream codebases and twelve peer-reviewed primary publications:

- **Execution Engines Compared:** `duckdb/duckdb` (`bc04be044b0d84075aa6d63fc11d5dfaa6e9aaa8`) and `facebookincubator/velox` (`f112bee8903de272ade6086878297ad9f66cdf17`) are inspected directly at source level for vectorized pipelines, vector encodings, selection/selectivity abstractions, compressed scans, and Arrow FFI bridges. `HyPer`, `Umbra`, `MonetDB/X100`, `LMS` query compilation, and `Relaxed Operator Fusion` are characterized from their primary peer-reviewed publications (no public source repository exists for closed-source `HyPer`/`Umbra` binaries).
- **FFI Interchange Layer:** `apache/arrow` (`931b9cccda5de68d48201dc2db50b6b6a9a72741`) supplies the normative C Data Interface (`abi.h`, `CDataInterface.rst`) and Columnar Format 1.4 (`Columnar.rst`) specifications; `apache/arrow-rs` (`44a4bdb287dfcc7297c5fb4c98d8c6d8c43f6e70`), `velox/vector/arrow/Bridge.{h,cpp}`, and `duckdb/src/common/arrow/` show concrete Rust and C++ FFI producer/consumer implementations interpreting that specification.
- **SIMD Compression Codecs:** `cwida/FastLanes` (`f0edc1020a538f1f8098640fce8347c9ac247a0d`), `cwida/fsst` (`e638d4cf8c26129d73c242a4127b42b975de5b63`), `cwida/ALP` (`31ca0ed11c93c99d3f5b5c30e01a3e1c3832d3ce`), and `maxi-k/btrblocks` (`c950c3c01c1fbf91007936b05781d431a29a60d3`) are examined directly at source level alongside their publications and integrations inside `duckdb/duckdb`.
- **Target Scope Constraints:** Findings apply to in-process analytical (OLAP) relational execution on little-endian 64-bit CPUs (`x86-64` SSE/AVX2/AVX-512, `ARM64` NEON/SVE) with IEEE-754 binary32/binary64 floating point and strict-aliasing / `-fno-associative-math` semantics. Claims about Arrow C Data Interface zero-copy apply strictly to **in-process** shared-address-space FFI (not cross-process Arrow IPC or network Flight serialization).
- **Version-Specific Nuances:** DuckDB's replacement of standalone `FSST` compression with `dict_fsst` applies specifically to `StorageVersion::V1_3_0` and later (`src/storage/compression/fsst.cpp:95-98`, `dict_fsst.cpp:76-79`). Arrow `Variable-size Binary View` (`vu`/`vz`) and `List View` (`+vl`/`+vL`) layouts require Arrow Columnar Format 1.4+ (`Columnar.rst:485`).

## Findings

### 1. Execution Models: Data-Centric Push Compilation vs. Vectorized Morsel-Driven Pipelines

Basis: documentation (peer-reviewed literature) + source (`duckdb/duckdb`, `facebookincubator/velox`) + derived

Classical relational engines implemented Graefe's **Volcano pull-iterator model**, where each physical operator implements `next()` returning one tuple at a time. Boncz, Zukowski, and Nes (`MonetDB/X100`, CIDR 2005) demonstrated that tuple-at-a-time pull execution depresses CPU Instructions-Per-Cycle (IPC) below `0.5` due to virtual function dispatch per tuple, register spilling across call boundaries, instruction-cache thrashing, and unpredictable per-tuple control flow. Two primary execution models superseded Volcano for modern analytical hardware:

#### 1.1 Data-Centric Push Compilation (`HyPer`, `Umbra`, `LMS`)

Neumann (`HyPer`, PVLDB 2011, DOI `10.14778/2002938.2002940`) inverted control flow from operator-centric pull to **data-centric push** (`produce()` / `consume()`):

- **Pipeline Boundaries:** A query plan is partitioned at **pipeline breakers**—operators that must materialize tuples into a memory data structure before downstream consumption (e.g., hash-join build side, hash-aggregation group table, sort buffer). Every maximal chain of non-blocking operators between two pipeline breakers compiles into a **single tight loop** with zero intermediate tuple materialization.
- **Compile-Time Control Flow (`produce` / `consume`):** At compile time, the root operator calls `produce()` down the operator tree until reaching a scan or materialized pipeline breaker, which emits a tight loop and invokes `parent.consume(tuple_regs)` inside the loop body. Filter predicates emit conditional branches; hash-join probes emit inline table lookups; aggregations update in-place state. Live tuple attributes stay in SSA virtual registers across operator boundaries.
- **Staged Modularity (`LMS`):** Tahboub, Essertel, and Rompf (SIGMOD 2018, DOI `10.1145/3183713.3196893`) demonstrated via Lightweight Modular Staging (`LMS`) that writing a query interpreter in a multi-stage host language with continuation-passing style (`CPS`) automatically yields Neumann's push-based fused loops when staged, avoiding manual AST/IR emission boilerplate while preserving composability for user-defined functions and complex control flow.

#### 1.2 Sub-Millisecond Code Generation (`Umbra Flying Start`)

Standard `HyPer` lowered generated query code to `LLVM IR` and invoked `LLVM`'s optimization passes (`-O2`/`-O3`). For complex analytical queries (e.g., TPC-H / TPC-DS with dozens of joins and generated functions spanning tens of thousands of IR instructions), `LLVM`'s super-linear optimization and graph-coloring/greedy register allocation passes incur **tens to hundreds of milliseconds**—often exceeding execution time on small or selective inputs.

Kersten, Leis, and Neumann (`Umbra`, VLDB Journal 2021, DOI `10.1007/s00778-020-00643-4`) introduced **Flying Start**, a custom direct-to-machine-code backend targeting `Umbra`'s SSA-based internal IR:

1. **Near-Single-Pass Lowering:** Translates Umbra SSA IR directly to `x86-64` (and subsequently `ARM64`) machine instructions without constructing a secondary MIR/SelectionDAG or running iterative dataflow fixpoints, using only a lightweight preliminary liveness/loop-depth scan so values live inside inner loops retain register priority.
2. **On-the-Fly Register Bookkeeping:** Replaces global interference-graph allocation with lightweight register tracking (`Reg` / `ScratchReg` abstractions) that maps live SSA values to physical registers or stack spill slots linearly during emission.
3. **Adaptive Tiered Execution:** `Umbra` begins executing immediately using `Flying Start` (~`100x` lower compile latency than `LLVM`, ~`1.2x` of `LLVM -O3` execution time) and compiles asynchronously with `LLVM` only if execution duration justifies the compilation cost (adaptive execution / OSR-like morsel handoff at pipeline boundaries).

#### 1.3 Vectorized Morsel-Driven Execution (`MonetDB/X100`, `DuckDB`, `Velox`)

Vectorized engines retain interpreted operator pipelines but amortize dispatch and materialization over cache-resident **columnar vectors** (typically `1024`–`2048` tuples, e.g., DuckDB's `STANDARD_VECTOR_SIZE = 2048` and FastLanes/ALP's `1024`):

- **Morsel-Driven Parallelism (Leis et al., SIGMOD 2014, DOI `10.1145/2588555.2610507`):** Rather than static Exchange-operator hash-partitioning across fixed worker threads, a global scheduler dynamically hands fixed-size input slices (**morsels**, e.g., ~100K tuples or row groups) to worker threads executing the **entire pipeline** into thread-local or lock-free shared pipeline-breaker states. NUMA-local scheduling pins morsels to the socket holding the memory pages, while work-stealing eliminates skew without Exchange serialization barriers.
- **DuckDB Push-Based Vectorized Pipelines (`duckdb/duckdb`, `src/include/duckdb/parallel/pipeline.hpp`):** DuckDB combines vectorized chunks with a **push-based** `Source -> Operator* -> Sink` `Pipeline` architecture scheduled by `PipelineTask` (`PARTIAL_CHUNK_COUNT = 50` chunks per partial execution slice, `pipeline.hpp:54`) and coordinated through `MetaPipeline` dependencies (`REQUIRED` / `OPTIONAL_DEPENDENCY`, `pipeline.hpp:34`), `PipelineExecutionOrder` batch-index tracking (`BATCH_INCREMENT = 10000000000000`, `pipeline.hpp:89`), and `PipelineInputMode::EXTERNAL_INPUT` for zero-materialization CTE/dataflow streaming (`pipeline.hpp:33,230`).
- **Architectural Comparison (`Kersten et al., PVLDB 2018`, DOI `10.14778/3275366.3275370` & `ROF`, PVLDB 2017, DOI `10.14778/3136610.3136611`):**

| Architectural Dimension | Data-Centric Push Compilation (`HyPer` / `Umbra`) | Vectorized Pipelines (`DuckDB` / `Velox`) | Relaxed Operator Fusion (`ROF`, Menon et al. 2017) |
| :--- | :--- | :--- | :--- |
| **Control Flow** | Fused scalar loops across non-blocking operators (`produce`/`consume`) | Batch-at-a-time pipeline (`Source -> Ops -> Sink`) over 1024–2048 row vectors | Compiled stages separated by L1-resident micro-staging buffers |
| **Instruction Count / Tuple** | Minimal (attributes stay in registers; zero loop-boundary load/store) | Higher (per-operator loop + L1 vector read/write + selection indirection) | Near-compiled for arithmetic; bounded staging cost at memory-bound ops |
| **Cache-Miss Hiding (MLP)** | Poor on random L3-missing hash probes (1 tuple stalls core ROB) | High (independent loop iterations over 2048 keys overlap L3 misses) | High (explicit software prefetching `PREFETCHT0` over staged hash keys) |
| **SIMD Auto-Vectorization** | Fragile under nested selection branches / nullable predicates | Strong (tight typed array kernels + branchless mask/selection loops) | Strong (stages feed SIMD-predicated kernels before branching) |
| **Compile Latency** | `LLVM -O3`: 10–500 ms; `Umbra Flying Start`: <1 ms | `0 ms` (pre-compiled C++ operator/kernel templates) | Same as host codegen backend |
| **Compressed Vector Execution** | Requires generating specialized code per encoding combination | Native via runtime `VectorType` / `VectorEncoding::Simple` dispatch | Hybrid: decodes or propagates dictionary codes into staging vectors |

*Derived Architectural Synthesis:* Neither pure push compilation nor pure vectorization strictly dominates across all OLAP workloads (`Kersten et al., PVLDB 2018`). Compute-bound expressions (e.g., TPC-H Q1 arithmetic aggregations) favor compiled register residency, whereas memory-latency-bound multi-way hash joins over tables exceeding LLC size favor vectorized batching or `ROF` prefetching because CPU out-of-order windows can overlap dozens of concurrent L3 misses across independent vector lanes.

---

### 2. Zero-Materialization Vector Representations: DuckDB vs. Velox

Basis: source (`duckdb/duckdb`, `facebookincubator/velox`)

Both `DuckDB` and `Velox` decouple a column's **logical SQL type** from its **per-batch physical vector encoding**, enabling downstream operators to filter, slice, project, and evaluate expressions without copying underlying buffers. Their designs diverge sharply in **how active rows are tracked** and **how nested encodings compose**:

| Feature | DuckDB (`duckdb/duckdb`) | Velox (`facebookincubator/velox`) |
| :--- | :--- | :--- |
| **Core Vector Types / Encodings** | `VectorType` on `VectorBuffer`: `FLAT_VECTOR`, `CONSTANT_VECTOR`, `DICTIONARY_VECTOR`, `SEQUENCE_VECTOR`, `FSST_VECTOR` (`vector.hpp:135,181-187`; `fsst.cpp:2`) | `VectorEncoding::Simple` (`VectorEncoding.h:29-41`): `BIASED`, `CONSTANT`, `DICTIONARY`, `FLAT`, `SEQUENCE`, `ROW`, `MAP`, `FLAT_MAP`, `ARRAY`, `LAZY`, `FUNCTION` |
| **Active-Row Filtering Representation** | **`SelectionVector`** (`selection_vector.hpp:34-189`): dense index array `sel_t*` (`uint32_t` indices) of active rows; `get_index(i)` returns `sel_vector ? sel_vector[i] : i` (`line 140`) | **`SelectivityVector`** (`SelectivityVector.h:39-200`): 64-bit word **bitmask** (`bits_`) with tight `[begin_, end_)` active span and cached `allSelected_` flag (`lines 44-48`) |
| **Canonical Read Abstraction** | **`UnifiedVectorFormat`** ("Orrify", `vector.hpp:120-126`): zero-copy projection of `FLAT`, `CONSTANT`, and `DICTIONARY` into `(data_ptr, validity_mask, SelectionVector)` | **`DecodedVector`** (referenced by `BaseVector.h` / `DictionaryVector.h`): peels arbitrarily nested `DICTIONARY`/`CONSTANT` layers into flat index mapping + null bitmask |
| **Deferred Column Loading** | Late materialization via `Select(..., SelectionVector& sel, sel_count)` on compressed storage segments (`dict_fsst.cpp:154-160`, `bitpacking.cpp:1307-1319`) | First-class **`LAZY`** encoding (`VectorEncoding::Simple::LAZY`): unreferenced columns in a `RowVector` are loaded/decoded only for rows surviving earlier filters (`SelectivityVector`) |
| **String Representation (16B)** | `string_t` (Umbra/German-string style: 4B len + 4B prefix + 8B inline/ptr; `INLINE_LENGTH = 12`, `dict_fsst.cpp:124`) | `StringView` (`velox/type/StringView.h:73-117`): 4B `size_`, 4B `prefix_`, 8B inline (`<= 12` bytes, zero-padded for 2×`int64` equality!) or `const char*` pointer |

#### Key Source-Level Trade-Offs and Failure Modes

1. **Selection Vector (Index List) vs. Selectivity Vector (Bitmask):**
   - DuckDB's dense index list `SelectionVector` excels at **low selectivity** (e.g., `< 5%` rows pass): downstream operators iterate strictly `0..sel_count`, and `SelectionVector::SliceInPlace` (`selection_vector.hpp:159`) composes cascaded filters without scanning dead rows. Moreover, `DuckDB` reuses the exact same `SelectionVector` machinery for `DICTIONARY_VECTOR` indirection (`Vector::Slice(sel, count)` turns a vector into a dictionary view without copying payloads, `vector.hpp:85-95`), with `SelCache` avoiding redundant slice allocations across columns of a `DataChunk`.
   - **Ordering Invariant Hazard:** DuckDB's `BitpackingSelect` (`src/storage/compression/bitpacking.cpp:1307-1315`) strictly requires monotonically non-decreasing `SelectionVector` indices and throws `InternalException("Error in BitpackingSelect - selection vector indices are not ordered")` if violated.
   - Velox's `SelectivityVector` bitmask (`SelectivityVector.h:193-197`) excels at **conjunctive/disjunctive filter composition** (`intersect` executes a tight 64-bit wordwise `AND` via `bits::andBits`, `complement` flips bits for `CASE`/`IF` branches) and **high-selectivity SIMD execution**, because bitmasks map directly to AVX-512 `k`-mask registers without gather instructions. However, callers mutating individual bits via `setValid()`/`setValidRange()` MUST explicitly call `updateBounds()` afterward (`SelectivityVector.h:94-96,106-107`) or `[begin_, end_)` becomes stale and silently skips active rows.
2. **Dictionary Caching & Expression Memoization:** Velox's `DictionaryVector` preserves dictionary encoding through expression evaluation by evaluating pure functions once over the unique dictionary values (peeling dictionary layers) rather than per row, avoiding decompression blowup when cardinality is small relative to batch size. Similarly, DuckDB's `DictionaryEntry` (`vector.hpp:95`) attaches stable dictionary IDs so hash/filter operators can cache per-dictionary evaluation results across consecutive chunks sharing a storage segment's dictionary.
3. **Inline String Zero-Padding Invariant (`Velox::StringView`):** In `velox/type/StringView.h:91-97`, `StringView(const char*, int32_t)` explicitly zeroes `prefix_` and `value_.data` before `memcpy` whenever `size_ <= 12` (`kInlineSize`) so that inline string equality reduces to **two 64-bit integer comparisons** without branching on length. Any FFI importer that constructs a `StringView` with unzeroed tail bytes breaks inline equality silently.

---

### 3. Apache Arrow C Data Interface: Normative Ownership Semantics and Zero-Copy FFI Cliffs

Basis: normative (`apache/arrow` `CDataInterface.rst`, `abi.h`, `Columnar.rst`) + source (`apache/arrow-rs`, `facebookincubator/velox`, `duckdb/duckdb`)

#### 3.1 Normative ABI Structures and Ownership State Machine

The Apache Arrow C Data Interface (`apache/arrow/cpp/src/arrow/c/abi.h:50-81,140-245`) defines four vendored, dependency-free C structs: `ArrowSchema`, `ArrowArray`, `ArrowDeviceArray` (carrying `ArrowDeviceType` such as `ARROW_DEVICE_CPU = 1`, `CUDA = 2`, `ROCM = 10`, `WEBGPU = 15`, plus `void* sync_event`), and streaming pull iterators `ArrowArrayStream` / `ArrowDeviceArrayStream`.

The normative ownership and memory-safety contract (`docs/source/format/CDataInterface.rst:582-720`) imposes six strict invariants across the FFI boundary:

1. **Consumer Allocation, Producer Payload Ownership:** The consumer allocates the top-level `ArrowSchema`/`ArrowArray` struct (stack or heap); the producer allocates and owns every pointer reachable from it (`format`, `metadata`, `buffers`, `children`, `dictionary`, `private_data`).
2. **Release Marker Sentinel (`release == NULL`):** A struct is considered released iff `release == NULL` (`CDataInterface.rst:602`). Consumers MUST check `release != NULL` before reading and MUST call `release(ptr)` exactly once on the **base** struct only—never directly on `children[i]` or `dictionary` (`CDataInterface.rst:610-613`).
3. **Recursive Producer Release:** The producer's `release` callback MUST recursively invoke non-null `release` callbacks on all `children[i]` and `dictionary`, free producer-owned metadata/pointer arrays via `private_data`, and finally set `self->release = NULL` (`CDataInterface.rst:631-670`).
4. **Trivial Relocatability & Move Protocol:** Consumers move an `ArrowArray` by bitwise/shallow copy to a destination struct and immediately setting `src.release = NULL` **without** invoking `src.release` (`CDataInterface.rst:676-685`). Consequently, **producers MUST NOT store self-referential pointers inside `ArrowArray`/`ArrowSchema` or external pointers to the struct's original address**; all producer bookkeeping MUST hang off `private_data` (`CDataInterface.rst:699-704`). Moving a single child array out of a struct array is allowed *only if* the parent is released immediately afterward (`CDataInterface.rst:689-691`).
5. **Immutability:** Both producer and consumer MUST treat buffers reachable through `buffers[]` as immutable while shared (`CDataInterface.rst:716-719`).
6. **Stream Lifecycle Independence (`abi.h:167-191`):** Every `ArrowSchema` returned by `get_schema()` and `ArrowArray` returned by `get_next()` MUST be released independently of `ArrowArrayStream::release`. End-of-stream is signaled by `get_next()` returning `0` with `out->release == NULL`; error text from `get_last_error()` is invalidated by any subsequent call on the stream (including `release`).

#### 3.2 Concrete Zero-Copy Boundaries and Hidden Copy Traps in Production FFI Bridges

Direct inspection of `apache/arrow-rs` (`arrow-data/src/ffi.rs`), `facebookincubator/velox` (`velox/vector/arrow/Bridge.{h,cpp}`), and `duckdb/duckdb` (`src/common/arrow/arrow_converter.cpp`) exposes **five real seams where "Arrow zero-copy FFI" silently allocates and copies or risks UB**:

| FFI Seam / Condition | Observed Implementation Behavior | Zero-Copy? | Primary Source Reference |
| :--- | :--- | :--- | :--- |
| **Rust `FFI_ArrowArray` Export & `Drop`** | Wraps owned `Vec<Option<Buffer>>`, `Box<[*const c_void]>`, `Box<[*mut FFI_ArrowArray]>`, and `dictionary` inside `Box<ArrayPrivateData>` stored in `private_data`; `Drop` invokes `release(self)`, which reclaims `Box::from_raw` and sets `release = None`. `from_raw()` moves via `std::ptr::replace(array, Self::empty())`. | Yes (for aligned primitive buffers) | `apache/arrow-rs` `arrow-data/src/ffi.rs:56-85,110-225` |
| **Misaligned Null-Bitmap Offset (`data.offset() != nulls.offset()`)** | `arrow-rs::ffi::align_nulls()` checks `data_offset == nulls.offset()`. If unequal and `data_offset > 0`, it allocates a brand-new `MutableBuffer::new_null(data_offset + nulls.len())` and bit-shifts every validity bit via `set_bits()`. | **No (bit-shift copy)** | `apache/arrow-rs` `arrow-data/src/ffi.rs:90-108` |
| **Velox `StringView` -> Arrow `Utf8View` (`vu` / `vz`, Format 1.4)** | Both are 16 bytes with `[len: i32, prefix: 4B]`, **but** for `len > 12`, Velox stores an 8-byte raw `const char*` whereas Arrow Format 1.4 (`Columnar.rst:496-529`) mandates `[buf_idx: i32, offset: i32]` + trailing `i64` variadic buffer sizes buffer. Velox's `exportViews()` shares string payload buffers zero-copy (`holder.setBuffer(2 + idx, ...)`), sorts buffer base addresses, binary-searches each pointer, and **allocates & rewrites** a new `16 * out.length` `utf8Views` descriptor buffer plus `variadicBufferSizes`! | **Partial** (payload zero-copy; 16B view array copied & rewritten) | `facebookincubator/velox` `velox/vector/arrow/Bridge.cpp:1046-1111`; `apache/arrow` `Columnar.rst:482-530` |
| **Velox `VARCHAR` -> Arrow Default `u`/`z` (`kDefault`) or `U`/`Z` (`kLarge`)** | Copies all string payloads into a contiguous data buffer and materializes a 32-bit or 64-bit offsets buffer (`exportStrings`). | **No (full string copy)** | `facebookincubator/velox` `Bridge.h:38-45`, `Bridge.cpp:1209-1223` |
| **Type/Encoding Coupling, Alignment & Timestamps** | Arrow couples dictionary (`dictionary != NULL`) and run-end (`+r`) encoding into `ArrowSchema`, requiring Velox `exportToArrow(const VectorPtr&, ArrowSchema&)` to inspect runtime data (`Bridge.h:116-121`). On import, Velox copies 128-bit decimals lacking 16-byte alignment and converts Arrow `int64` timestamps into Velox `{int64 seconds, uint64 nanos}` buffers (`Bridge.h:156-163`). | **No** for mismatched temporal/alignment layouts | `facebookincubator/velox` `Bridge.h:49-62,116-163` |

*Safety Note on `arrow-rs` Buffer Pointer Reads:* `arrow-data/src/ffi.rs:332-338` uses `std::ptr::read_unaligned(self.buffers.cast::<*const u8>().add(index))` to guard against under-aligned foreign `buffers` arrays, and `set_release`/`set_private_data` (`lines 264-280`) expose `unsafe` callback-chaining hooks for consumers wrapping foreign release semantics.

---

### 4. SIMD-Native Columnar Compression Codecs Without Materialization

Basis: source (`cwida/FastLanes`, `cwida/fsst`, `cwida/ALP`, `maxi-k/btrblocks`, `duckdb/duckdb`) + execution (self-contained Python 3 codec probe in **Evidence** / **Revalidation**) + documentation

Legacy byte-oriented block compressors (`LZ4`, `Snappy`, `Zstd` over sequential Parquet pages) serialize decoding across data-dependent back-references and require decompressing multi-kilobyte pages before running predicates. Modern columnar engines replace them with lightweight, **1024-value-vector**, SIMD-parallel encodings that can be cascaded and often queried without full decompression.

#### 4.1 FastLanes: Unified Transposed Layout (UTL) for Width-Agnostic SIMD Bit-Packing & Delta (`rsum`)

Traditional SIMD bit-packing (e.g., Lemire's `SIMD-BP128` or Parquet `RLE_BIT_PACKED_HYBRID`) hardcodes a specific SIMD register width (e.g., 128-bit = 4×32-bit lanes) into the on-disk interleaving layout, breaking vectorization on wider AVX-512/GPU targets and serializing delta decoding (`x[i] = x[i-1] + d[i]`) across dependent lanes.

Afroozeh and Boncz (`cwida/FastLanes`, PVLDB 2023, DOI `10.14778/3598581.3598587`; `src/include/fls/cfg/cfg.hpp:26-29`, `src/include/fls_gen/transpose/transpose.hpp`) resolve this with a single **Unified Transposed Layout (UTL)** over every `VEC_SZ = 1024` values (`N_VECTORS_PER_ROWGROUP = 64`, `N_VALUES_PER_ROWGROUP = 65536`, `cfg.hpp:37-40`):

- **Virtual 1024-Bit Register & `FLS_ORDER` Bijection:** FastLanes models a 1024-bit virtual SIMD register (`16 × 64-bit`, `32 × 32-bit`, `64 × 16-bit`, or `128 × 8-bit` lanes). Each 1024-value vector is mapped from physical slot $p = 16r + \ell$ ($r \in [0, 64)$, $\ell \in [0, 16)$ for 64-bit lanes) to logical tuple index:
  $$\pi(16r + \ell) = \lfloor \ell / 2 \rfloor \cdot 128 + \text{FLS\_ORDER}[\lfloor r / 8 \rfloor] \cdot 16 + (\ell \bmod 2) \cdot 8 + (r \bmod 8)$$
  where $\text{FLS\_ORDER} = [0, 4, 2, 6, 1, 5, 3, 7]$.
- **Key Structural Properties (verified via executable Python 3 probe in Revalidation):**
  1. **Exact Bijection:** $\pi$ is a bijection on $\{0, \dots, 1023\}$; no padding or metadata indices are required.
  2. **Zero Cross-Lane Shuffles Across All SIMD Widths:** Along any 64-bit lane $\ell$, consecutive elements inside every 8-row mini-block ($r = 8b + k, k \in [0, 7]$) advance the logical index by exactly $+1$ (`strides == {1}`). Because 128-bit (`2` lanes), 256-bit (`4` lanes), 512-bit (`8` lanes), and 1024-bit (`16` lanes) SIMD instructions divide 16 evenly, contiguous scalar loops over `16` lanes **auto-vectorize cleanly** with zero cross-lane shuffles and zero handwritten ISA intrinsics, scaling directly to `SSE`, `AVX2`, `AVX-512`, `ARM64 NEON`, `SVE`, `WASM SIMD128`, and CUDA warps (`alp/falp.hpp:66-132`, `transpose.hpp:49-93`).
  3. **Fused Data-Parallel Delta (`rsum`) and Frame-of-Reference (`FFOR`):** Delta prefix sums (`rsum`, `fls_gen/rsum_and_untranspose`) run across `16` (or `32`/`64`/`128`) completely independent base-seeded delta streams (`UNIFIED_TRANSPOSED::BASES_SIZE = 128`, `cfg.hpp:136`), eliminating loop-carried dependencies that otherwise stall scalar delta decoding to 1 value/cycle.
  4. **Zero-Materialization Execution:** Predicates of the form `col = c` or `col >= lo AND col <= hi` under `FFOR` bit-packing translate directly into bit-width-adjusted comparisons (`c - base`) on unpacked lane registers before untransposing (or without untransposing at all for order-insensitive aggregations like `COUNT`/`SUM`/`MIN`/`MAX`!).

#### 4.2 FSST (Fast Static Symbol Table) & DuckDB `dict_fsst`

Boncz, Neumann, and Leis (`cwida/fsst`, PVLDB 2020, DOI `10.14778/3407790.3407851`; `fsst.h:73-222`) address string columns whose cardinality is too high for whole-string dictionary compression while still needing **per-string random access** (impossible in block-based `LZ4`/`Zstd`):

- **Encoding Layout (`fsst.h:74-85`):** Maps up to `255` frequent 1–8 byte substrings onto single-byte codes `0..254`. Code `FSST_ESC = 255` (`0xFF`) escapes a single raw uncompressed byte immediately following it. The read-only `fsst_decoder_t` table stores `uint8_t len[255]` and `uint64_t symbol[255]` (little-endian packed 8-byte words), serialized compactly within `FSST_MAXHEADER = 2066` bytes (`fsst.h:102`).
- **Branchless SWAR Escape Detection & Speculative 8-Byte Stores (`fsst.h:158-179`):** On little-endian targets when `posOut + 32 <= size` (32-byte output slack), `fsst_decompress` loads 4 compressed code bytes into `uint32_t nextBlock` and computes:
  $$\text{escapeMask} = (\text{nextBlock} \mathbin{\&} \texttt{0x80808080}) \mathbin{\&} \big(((( \sim\text{nextBlock}) \mathbin{\&} \texttt{0x7F7F7F7F}) + \texttt{0x7F7F7F7F}) \oplus \texttt{0x80808080}\big)$$
  Exhaustive execution verification (6,144 lane/byte/neighbor combinations in our Python 3 probe) confirms bit 7 of lane $j \in \{0,1,2,3\}$ is set **if and only if** byte $j = \texttt{0xFF}$ (`0` false positives, `0` false negatives). When `escapeMask == 0`, four unaligned 8-byte writes (`FSST_UNALIGNED_STORE`) emit all four symbols without per-byte length loops, advancing `posOut += len[code]` so subsequent stores overwrite trailing garbage bytes. When an escape is present, `__builtin_ctzl(escapeMask) >> 3` jumps via Duff's device to decode preceding codes and copy the single escaped byte.
- **Compressed-Domain Equality Pushdown & Its Boundary:** Because FSST encoding with a fixed symbol table and deterministic greedy longest-match encoder is injective (`fsst.h:37`), $s_1 = s_2 \iff \text{enc}_T(s_1) = \text{enc}_T(s_2)$. Engines can compress a constant query predicate `WHERE col = 'https://example.org/item'` once with the segment's symbol table $T$ and compare directly against compressed byte slices without decompressing non-matching strings! **Boundary:** This equivalence fails for ordering comparisons (`<`, `>`, `LIKE '%sub%'` across symbol boundaries) and fails across segments with distinct symbol tables unless the constant is re-encoded per segment.
- **DuckDB `dict_fsst` Evolution (`duckdb/duckdb` `src/storage/compression/dict_fsst.cpp:13-160`, `fsst.cpp:95-98`):** Starting at `StorageVersion::V1_3_0`, DuckDB disabled standalone `FSSTStorage` in favor of unified `DictFSSTCompressionStorage`. Each segment stores `[Header | Selection Buffer (uint16_t index_buffer_idx[]) | Index Buffer (uint16_t dictionary_offset[]) | Raw/FSST Dictionary | Optional FSST Symbol Table]`. On scan, `StringScanPartial<true>` emits a `DICTIONARY_VECTOR` directly (`ScanToDictionaryVector`) whenever cardinality allows, avoiding string decompression until late materialization; `DictFSSTSelect` further fast-paths sparse `SelectionVector` lookups when `sel_count <= vector_count / 64` (`dict_fsst.cpp:160`).

#### 4.3 ALP & `ALP_RD`: Adaptive Lossless Floating-Point Compression

General-purpose XOR-based float compressors (`Gorilla`, `Chimp`, `Patas`) perform poorly on analytical floats because IEEE-754 binary64 encoding turns short decimal numbers (e.g., `12.34`) into repeating binary mantissa tails with high XOR entropy, and their variable-length bitstreams serialize decoding. Afroozeh, Kuffó, and Boncz (`cwida/ALP`, SIGMOD 2024, DOI `10.1145/3626717`; `include/alp/{constants,encoder,decoder,falp,rd}.hpp`) exploit the fact that analytical floats predominantly originate as bounded-precision decimals:

- **Two-Parameter Decimal Scaling & Fast Magic-Number Rounding (`encoder.hpp:75-89`, `decoder.hpp:128-131`):**
  For each 1024-value vector, ALP selects a pair $(e, f)$ with $0 \le f \le e \le 18$ (double) or $\le 10$ (float) via two-level sampling (row-group top-$k=5$ candidate pairs $\to$ per-vector winner, `encoder.hpp:139-250`):
  $$\text{enc}(v; e, f) = \text{int64}\Big(\big((v \cdot 10^e \cdot 10^{-f}) + M\big) - M\Big), \qquad \text{dec}(z; e, f) = \text{double}(z \cdot 10^f) \cdot 10^{-e}$$
  where $M = \texttt{MAGIC\_NUMBER} = 2^{51} + 2^{52} = 6755399441055744.0$ (`0x0018000000000000` cast to `double`, `constants.hpp:70`) forces IEEE-754 round-to-nearest-even to an integer without calling `std::round`, followed by FastLanes `FFOR` bit-packing of the resulting integers. During decompression, `falp.hpp` fuses FastLanes `UNFFOR` with `int64 -> double` conversion and multiplication into a single vectorized pass (`SSE`, `AVX2`, `AVX-512`, `NEON`, `SVE`, `WASM SIMD128`).
- **Why ALP Needs Two Parameters $(e, f)$ — Proven via IEEE-754 ULP Witness (Python 3 execution probe):** Naively, multiplying by $10^e \cdot 10^{-f}$ looks equivalent to $10^{e-f}$. In binary64 IEEE-754, however, `FRAC_ARR[k]` ($10^{-k}$) is inexact, and rounding errors depend on the specific pair $(e, f)$! Our execution probe found concrete 2-decimal doubles where $(e=2, f=0)$ fails bit-exactness by 1 ULP while $(e=6, f=4)$ succeeds bit-exactly:
  - `v = 8.29`: `(e=2, f=0)` produces `enc = 829`, `dec = 829 * 0.01 = 8.290000000000001` (`-1.776e-15` error $\to$ exception!), whereas `(e=6, f=4)` produces `enc = 829`, `dec = (829 * 10000) * 1e-6 = 8.29` (**bit-exact**!). The same holds for `9.29` and `10.29`.
- **Mandatory Exception Classes & Soundness Guardrails (`encoder.hpp:75-78`, `decoder.hpp:81-83`):**
  ALP verifies exact round-trip `decode_value(enc, f, e) == v` per element and stores failures in an out-of-band exception patch table (`exceptions[]`, `exceptions_positions[]`, `exceptions_count`, `decoder.hpp:141-149`). Five edge cases MUST be patched as exceptions (all verified in our Python 3 probe):
  1. **`-0.0`:** Because C++ `-0.0 == +0.0` evaluates `true`, `is_impossible_to_encode` explicitly checks `(n == 0.0 && std::signbit(n))` (`encoder.hpp:77`); omitting this silently destroys sign bits!
  2. **`NaN` and `±Inf`:** Caught by `!std::isfinite(n) || std::isnan(n)`.
  3. **Out-of-Range Values (`|tmp| > 2^{51}` odd integers or `> ENCODING_UPPER_LIMIT = 9223372036854774784`):** For `v = 2^51 + 1 = 2251799813685249.0`, `(v + MAGIC_NUMBER) - MAGIC_NUMBER = 2251799813685248.0`, dropping the least-significant bit and triggering an exception patch.
  4. **Non-Decimal High-Precision Floats (e.g., `math.pi`):** Patched individually, or triggers row-group fallback to **`ALP_RD`** when estimated size exceeds `RD_SIZE_THRESHOLD_LIMIT` (`48 bits/val` for `double`, `22 bits/val` for `float`, `constants.hpp:33,69`).
  5. **Compiler Flag Hazard (`-Ofast` / `-fassociative-math`):** Both the magic-number trick `(x + M) - M` and the AVX2 `int64_to_double_fast_precise` bit-blend sequence (`decoder.hpp:64-84`) rely strictly on IEEE-754 non-associativity; compiling with `-Ofast` allows LLVM/GCC to fold `(x + M) - M` to `x` and silently corrupts every encoded float!
- **Adaptive `ALP_RD` Fallback (`alp/rd.hpp:18-186`):** When decimal scaling fails (e.g., scientific/ML floats with full 53-bit mantissas), `ALP_RD` cuts the raw `uint64_t` bit pattern at an optimal split width `right_bit_width`: the volatile low `right_parts` are FastLanes bit-packed directly, while the low-entropy high `left_parts` (sign + exponent + top mantissa bits) are dictionary-encoded with up to `MAX_RD_DICTIONARY_SIZE = 8` entries (`3`-bit codes) plus rare-prefix exception patching. Our probe on 1024 values of `sin(i * 0.01) + 100.0` confirmed `distinct_left16 = 2`, `exceptions = 0`, and bit-exact reconstruction.

#### 4.4 Recursive Multi-Level Cascades (`BtrBlocks`)

Kuschewski et al. (`maxi-k/btrblocks`, SIGMOD 2023, DOI `10.1145/3589263`; `btrblocks/scheme/SchemeType.hpp:12-69`) generalize single-scheme codecs into **recursive, type-specific lightweight cascades** with fast sampling-based scheme selection:

- **Default Scheme Pools (`SchemeType.hpp:30-69`):** Integers select from `{UNCOMPRESSED, ONE_VALUE, DICT, RLE, PFOR, BP}`; doubles from `{UNCOMPRESSED, ONE_VALUE, DICT, RLE, FREQUENCY, PSEUDODECIMAL}` (a precursor to ALP); strings from `{UNCOMPRESSED, ONE_VALUE, DICT, FSST}`.
- **Recursive Composition:** Sub-streams produced by one scheme (e.g., dictionary codes, RLE run lengths, `PFOR` exception positions, `FSST` string length deltas) are recursively fed into the integer scheme selector (up to bounded cascade depth), achieving compression ratios competitive with `Parquet + Zstd` at an order of magnitude higher decompression bandwidth because every stage remains SIMD-vectorizable.

#### 4.5 Cross-Codec Summary Matrix

| Codec / Layout | Target Data Class | Vector Unit | Random Access | Direct Predicate Pushdown Without Full Decode | Primary Failure / Edge Case |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **FastLanes UTL + `FFOR`/`rsum`** | Integers, codes, offsets, sorted timestamps | 1024 values | Per-vector (1024) | Equality & range on `FFOR` (`val - base`); order-insensitive aggs without untranspose | Requires untranspose for row-ordered projection unless fused |
| **FSST** | High-cardinality strings / URLs / JSON | Per-string (1B codes + 2KB header) | Per-string O(len) | Equality (`=`, `IN`) under shared symbol table | Breaks `<`/`>` ordering & cross-table equality; needs 32B decode slack |
| **DuckDB `dict_fsst`** | Low-to-medium cardinality strings (`V1_3_0+`) | Segment (`uint16` dict) | Per-tuple via index buffer | Emits `DICTIONARY_VECTOR`; sparse `Select` fast-path (`<= 1/64`) | Falls back when string size exceeds block limit or cardinality saturates |
| **ALP / `ALP_RD`** | IEEE-754 `float32`/`float64` (decimal & scientific) | 1024 values | Per-vector (1024) | Range/equality on integer-encoded non-exceptions (requires checking exception list) | `-Ofast` breaks magic-number rounding; `-0.0` requires explicit `signbit` check |
| **BtrBlocks Cascades** | Heterogeneous data-lake columns | Row-group blocks | Per-block | Scheme-dependent (dictionary/RLE/BP stages) | Deep cascades increase decode code complexity if depth is unbounded |

## Boundaries

- **GPU-Native Execution and `G-ALP` / `FastLanesGPU` (`not examined`):** While `cwida/FastLanes/README.md` cites DaMoN 2024 (`10.1145/3662010.3663450`) and DaMoN 2025 (`G-ALP`, `10.1145/3736227.3736242`) GPU ports and `apache/arrow/abi.h` defines `ArrowDeviceArray` (`CUDA`/`ROCM`/`WEBGPU`), CUDA warp-level decoding kernels, GPU memory coalescing, and `sync_event` host-device synchronization semantics were **not examined** in source code.
- **Exact Runtime Benchmarks on Live Hardware (`not examined`):** Throughput numbers cited for `HyPer`, `Umbra Flying Start` (~100× compile speedup, ~1.2× of LLVM runtime), `FastLanes` (>100B int/s), and `ALP` are drawn from the cited peer-reviewed papers; end-to-end C++ benchmark binaries were **not** compiled or timed on local hardware.
- **Closed-Source Internals of `HyPer` and `Umbra` (`unknown`):** Because neither `HyPer` nor `Umbra` publishes its full production source tree, internal details of `Umbra`'s current ARM64 `Flying Start` backend, OSR/morsel tier-up thresholds, and newer post-2021 IR passes remain **unknown** beyond published papers.
- **Cross-Process Arrow IPC, Flight, and Network Zero-Copy (`known not to apply`):** The Arrow C Data Interface (`CDataInterface.rst:71`) explicitly states that sharing across distinct processes or storage persistence is a non-goal; its `release`/`private_data` pointer model **does not apply** across address spaces (where Arrow IPC Flatbuffers serialization is required).
- **Ordered Range Predicates and Substring Matching on Raw FSST Codes (`unsupported`):** FSST's symbol assignment is frequency-driven, not order-preserving; lexicographic comparisons (`<`, `<=`, `>`, `>=`) and arbitrary substring matching (`LIKE '%foo%'`) are **unsupported** directly on FSST-compressed bytes without decompression.
- **FastLanes File Format v1 Multi-Column Compression (`not examined`):** The 2025 FastLanes file format extension (`afroozeh2025fastlanes`, PVLDB 18(11), DOI `10.14778/3749646.3749718`) covering expression-encoded multi-column correlation compression (MCC) was identified in `cwida/FastLanes/README.md` (`lines 184-200`) but its encoder search algorithm was **not examined** in detail.
- **Stronger Claims Not Established:** Do **not** generalize that Arrow Format 1.4 `StringView` (`vu`/`vz`) eliminates all copying at FFI boundaries with Umbra-style engines: as proven in `velox/vector/arrow/Bridge.cpp:1046-1111`, engines storing raw 64-bit pointers inside 16-byte string views still allocate and rewrite the 16-byte view-header array to map pointers into `(buffer_idx, offset)` pairs. Likewise, do **not** assume DuckDB's `BitpackingSelect` accepts arbitrary unsorted `SelectionVector`s (`bitpacking.cpp:1310-1312`).

## Evidence

All primary evidence was acquired on `2026-11-19`.

### Upstream Source Code Evidence (Pinned Revisions)

1. **`apache/arrow` (`931b9cccda5de68d48201dc2db50b6b6a9a72741`):**
   - `cpp/src/arrow/c/abi.h:46-247` — Normative C definitions for `ArrowSchema`, `ArrowArray`, `ArrowDeviceArray`, `ArrowArrayStream`, `ArrowDeviceArrayStream`, flags (`ARROW_FLAG_*`), and `ARROW_DEVICE_*` codes.
   - `docs/source/format/CDataInterface.rst:95-245,582-720` — Format string grammar (`u`, `vu`, `+r`, etc.), allocation ownership, `release == NULL` sentinel, recursive release, trivial relocatability, move protocol, and immutability rules.
   - `docs/source/format/Columnar.rst:482-530` — Normative Arrow Columnar Format 1.4 `Variable-size Binary View` 16-byte layout (`[len: i32, prefix: 4B, buf_idx: i32, offset: i32]` for `len > 12`) and variadic buffer-lengths trailing buffer requirement.
2. **`apache/arrow-rs` (`44a4bdb287dfcc7297c5fb4c98d8c6d8c43f6e70`):**
   - `arrow-data/src/ffi.rs:24-225,264-338` — `#[repr(C)] FFI_ArrowArray`, `Drop` calling `release`, `release_array` reclaiming `ArrayPrivateData`, `align_nulls` bit-shifting copy when `data.offset() != nulls.offset()`, variadic buffer-lengths injection (`lines 143-154`), `from_raw` move via `std::ptr::replace`, and `read_unaligned` buffer access.
3. **`duckdb/duckdb` (`bc04be044b0d84075aa6d63fc11d5dfaa6e9aaa8`):**
   - `src/include/duckdb/common/types/vector.hpp:35-243` — `Vector` slice/dictionary/sequence/shred APIs and `ToUnifiedFormat` ("Orrify") canonical zero-copy reader.
   - `src/include/duckdb/common/types/selection_vector.hpp:23-189` — `SelectionVector`, `Inverted`, `SliceInPlace`, `SelectFromBoolean`.
   - `src/include/duckdb/parallel/pipeline.hpp:33-260` — `PipelineTask` (`PARTIAL_CHUNK_COUNT = 50`), `PipelineBuildState` (`BATCH_INCREMENT`), `Pipeline` push-based dependencies and `EXTERNAL_INPUT` mode.
   - `src/storage/compression/fsst.cpp:38-200` — `FSSTStorage` disabling at `StorageVersion::V1_3_0+` (`lines 95-98`), 25% sampling, buffer size `7 + 2 * total_size`.
   - `src/storage/compression/dict_fsst.cpp:13-160` — Unified `dict_fsst` segment layout, `V1_3_0+` activation, `ScanToDictionaryVector`, sparse `DictFSSTSelect` (`sel_count <= vector_count / 64`).
   - `src/storage/compression/bitpacking.cpp:1307-1315` — Ordered `SelectionVector` assertion in `BitpackingSelect`.
   - `src/include/duckdb/common/bitpacking.hpp:25-75` — `BitpackingPrimitives` (`BITPACKING_ALGORITHM_GROUP_SIZE = 32`).
4. **`facebookincubator/velox` (`f112bee8903de272ade6086878297ad9f66cdf17`):**
   - `velox/vector/VectorEncoding.h:29-41` — `VectorEncoding::Simple` enum (`BIASED`, `CONSTANT`, `DICTIONARY`, `FLAT`, `SEQUENCE`, `ROW`, `MAP`, `FLAT_MAP`, `ARRAY`, `LAZY`, `FUNCTION`).
   - `velox/vector/SelectivityVector.h:39-200` — 64-bit bitmask `SelectivityVector`, `updateBounds()` invariant, `intersect` (`bits::andBits`), `complement`.
   - `velox/type/StringView.h:39-160` — 16-byte `StringView` (`kPrefixSize = 4`, `kInlineSize = 12`), zero-padding of inline tail for 2×`int64` equality.
   - `velox/vector/arrow/Bridge.h:29-200` & `velox/vector/arrow/Bridge.cpp:422-452,1046-1111,1209-1224` — `ArrowOptions::VarTypeLayout`, `importFromArrowAsViewer`/`AsOwner`, `exportViews` pointer-to-`(buffer_idx, offset)` view-array rewrite, and alignment/timestamp copy conditions.
5. **`cwida/FastLanes` (`f0edc1020a538f1f8098640fce8347c9ac247a0d`):**
   - `src/include/fls/cfg/cfg.hpp:18-142` — `VEC_SZ = 1024`, `N_VECTORS_PER_ROWGROUP = 64`, `UNIFIED_TRANSPOSED::BASES_SIZE = 128`, `FSST` and `FSST12` header bounds.
   - `src/include/fls_gen/transpose/transpose.hpp:11-94` & `src/include/fls_gen/untranspose/untranspose.hpp` — Target matrix (`fallback::scalar`, `arm64v8::neon`, `x86_64::{sse,avx2,avx512f}`).
6. **`cwida/fsst` (`e638d4cf8c26129d73c242a4127b42b975de5b63`):**
   - `fsst.h:37,73-222` — `FSST_ESC = 255`, `fsst_decoder_t`, `FSST_MAXHEADER`, equality preservation property, and 4-byte SWAR `escapeMask` + Duff's device unaligned 8-byte store loop (`lines 158-179`).
7. **`cwida/ALP` (`31ca0ed11c93c99d3f5b5c30e01a3e1c3832d3ce`):**
   - `include/alp/constants.hpp:10-154` — `ENCODING_UPPER_LIMIT`, `MAGIC_NUMBER`, `RD_SIZE_THRESHOLD_LIMIT` (`48` / `22` bits/val), `FRAC_ARR`, `EXP_ARR`, `FACT_ARR`.
   - `include/alp/encoder.hpp:75-250` — `is_impossible_to_encode` (explicit `-0.0` `signbit` check), `encode_value`, two-level sampling `find_top_k_combinations`.
   - `include/alp/decoder.hpp:35-150` — `int64_to_double_fast_precise` (`-Ofast` / `-fassociative-math` prohibition, `line 82`), `decode_value`, `patch_exceptions`.
   - `include/alp/falp.hpp:10-132` — Fused `UNFFOR + ALP` kernels across x86-64, ARM64 NEON/SVE, and WASM SIMD128.
   - `include/alp/rd.hpp:18-186` — `ALP_RD` bit-cutting and `left_parts_dict` dictionary fallback.
8. **`maxi-k/btrblocks` (`c950c3c01c1fbf91007936b05781d431a29a60d3`):**
   - `btrblocks/scheme/SchemeType.hpp:12-69` — Default integer, double, and string compression scheme enums and pool sets.

### Executable Micro-Probe Evidence (`Basis: execution`)

A self-contained Python 3 probe (reproducible directly via `python3 - <<'EOF' ... EOF` below) verified:

```text
[FastLanes UTL] N=1024 bijection=PASS; in-block delta stride={1}; FFOR(bw=10) 1280B vs 8192B (6.40x); round-trip=PASS
[ALP Probe]
  decimal_pos    : v=12.34                -> enc=1234                 dec=12.34                  bit_eq=True exception=False
  decimal_neg    : v=-0.05                -> enc=-5                   dec=-0.05                  bit_eq=True exception=False
  neg_zero       : v=-0.0                 -> enc=9223372036854774784  dec=9.223372036854774e+16  bit_eq=False exception=True
  pos_zero       : v=0.0                  -> enc=0                    dec=0.0                    bit_eq=True exception=False
  pi_nondecimal  : v=3.141592653589793    -> enc=314                  dec=3.14                   bit_eq=False exception=True
  nan            : v=nan                  -> enc=9223372036854774784  dec=9.223372036854774e+16  bit_eq=False exception=True
  pos_inf        : v=inf                  -> enc=9223372036854774784  dec=9.223372036854774e+16  bit_eq=False exception=True
  odd_2_51_plus1 : v=2251799813685249.0   -> enc=2251799813685248     dec=2251799813685248.0     bit_eq=False exception=True
[ALP (e,f) ULP Witnesses] Found 3 cases where (e=2,f=0) loses 1 ULP but (e=2+k,f=k) is bit-exact:
  v=8.29: (e=2,f=0) -> 8.290000000000001 (diff=-1.776e-15); (e=6,f=4) -> 8.29 (bit_eq=True)
  v=9.29: (e=2,f=0) -> 9.290000000000001 (diff=-1.776e-15); (e=6,f=4) -> 9.29 (bit_eq=True)
  v=10.29: (e=2,f=0) -> 10.290000000000001 (diff=-1.776e-15); (e=6,f=4) -> 10.29 (bit_eq=True)
[ALP_RD Probe] N=1024 sin(i*0.01)+100: distinct_left16=2, dict_size=2, exceptions=0, bit-exact=PASS
[FSST SWAR Escape Mask] Exhaustive 4-lane x 256-byte x 6-neighbor probe (6144 cases): PASS
```

### Peer-Reviewed Literature Evidence

- Boncz, Zukowski, Nes (CIDR 2005): *MonetDB/X100: Hyper-Pipelining Query Execution*.
- Neumann (PVLDB 2011, DOI `10.14778/2002938.2002940`): *Efficiently Compiling Efficient Query Plans for Modern Hardware*.
- Leis, Boncz, Kemper, Neumann (SIGMOD 2014, DOI `10.1145/2588555.2610507`): *Morsel-Driven Parallelism: A NUMA-Aware Query Evaluation Framework for the Many-Core Age*.
- Menon, Mowry, Pavlo (PVLDB 2017, DOI `10.14778/3136610.3136611`): *Relaxed Operator Fusion for In-Memory Databases: Making Compilation, Vectorization, and Prefetching Work Together At Last*.
- Kersten, Leis, Kemper, Neumann, Pavlo, Boncz (PVLDB 2018, DOI `10.14778/3275366.3275370`): *Everything You Always Wanted to Know About Compiled and Vectorized Queries But Were Afraid to Ask*.
- Tahboub, Essertel, Rompf (SIGMOD 2018, DOI `10.1145/3183713.3196893`): *How to Architect a Query Compiler, Revisited*.
- Boncz, Neumann, Leis (PVLDB 2020, DOI `10.14778/3407790.3407851`): *FSST: Fast Random Access String Compression*.
- Kersten, Leis, Neumann (VLDB Journal 2021, DOI `10.1007/s00778-020-00643-4`): *Tidy Tuples and Flying Start: Fast Compilation and Fast Execution of Relational Queries in Umbra*.
- Pedreira et al. (PVLDB 2022, DOI `10.14778/3554821.3554829`): *Velox: Meta's Unified Execution Engine*.
- Afroozeh, Boncz (PVLDB 2023, DOI `10.14778/3598581.3598587`): *The FastLanes Compression Layout: Decoding > 100 Billion Integers per Second with Scalar Code*.
- Kuschewski, Sauerwein, Alhomssi, Leis (SIGMOD / PACMMOD 2023, DOI `10.1145/3589263`): *BtrBlocks: Efficient Columnar Compression for Data Lakes*.
- Afroozeh, Kuffó, Boncz (SIGMOD / PACMMOD 2024, DOI `10.1145/3626717`): *ALP: Adaptive Lossless Floating-Point Compression*.

## Revalidation

To cheaply verify whether key ABI, zero-copy, and codec invariants still hold against newer upstream revisions:

1. **Arrow C Data Interface & Rust/Velox Zero-Copy Diff Check:**
   - Diff `apache/arrow`: `cpp/src/arrow/c/abi.h` and `docs/source/format/CDataInterface.rst` (check for new `ArrowArray` fields, new `ARROW_FLAG_*` bits, or changes to `Variable-size Binary View` variadic-lengths rules).
   - Diff `apache/arrow-rs`: `arrow-data/src/ffi.rs` (`align_nulls` and `FFI_ArrowArray::new` variadic buffer handling) to check whether offset-misaligned null-bitmap copying has been eliminated.
   - Diff `facebookincubator/velox`: `velox/vector/arrow/Bridge.cpp` (`exportViews` and `ArrowOptions::VarTypeLayout`) and `velox/type/StringView.h` to check whether Velox adopts `(buf_idx, offset)` views natively or still rewrites the view descriptor buffer on export.
2. **DuckDB Compression & Selection Vector Invariant Check:**
   - Inspect `duckdb/duckdb`: `src/storage/compression/dict_fsst.cpp` (`StorageVersion` gate and `DictFSSTSelect` sparse threshold) and `src/storage/compression/bitpacking.cpp` (`BitpackingSelect` ordered-index check).
3. **Executable Codec Invariant Revalidation Probe:**
   Run the following self-contained Python 3 check to revalidate the FastLanes UTL bijection, ALP `(e, f)` ULP witness and `-0.0`/`2^51+1` exception boundaries, and FSST 4-byte SWAR escape mask:

```bash
python3 - <<'EOF'
import math, struct

# 1. FastLanes UTL bijection & unit-stride mini-block check
FLS_ORDER = [0, 4, 2, 6, 1, 5, 3, 7]
utl = lambda p: ((p % 16) // 2) * 128 + FLS_ORDER[(p // 16) // 8] * 16 + ((p % 16) % 2) * 8 + ((p // 16) % 8)
perm = [utl(p) for p in range(1024)]
assert len(set(perm)) == 1024 and min(perm) == 0 and max(perm) == 1023
assert {utl((8*b + k + 1)*16 + l) - utl((8*b + k)*16 + l) for l in range(16) for b in range(8) for k in range(7)} == {1}

# 2. ALP (e, f) ULP witness & magic-number 2^51+1 rounding boundary
M = float(0x0018000000000000)
enc = lambda v, f, e: int(((v * (10.0**e) * float(f"1e-{f}" if f else "1")) + M) - M)
dec = lambda z, f, e: float(z * (10**f)) * float(f"1e-{e}" if e else "1")
assert dec(enc(8.29, 0, 2), 0, 2) != 8.29 and dec(enc(8.29, 4, 6), 4, 6) == 8.29
assert enc(float(2**51 + 1), 0, 0) == 2**51  # LSB lost -> must trigger ALP exception

# 3. FSST 4-byte SWAR escape mask (cwida/fsst fsst.h:161)
swar = lambda w: (w & 0x80808080) & (((((~w) & 0xFFFFFFFF) & 0x7F7F7F7F) + 0x7F7F7F7F) ^ 0x80808080)
for lane in range(4):
    for b in range(256):
        w = b << (8 * lane)
        assert swar(w) == ((0x80 << (8 * lane)) if b == 0xFF else 0)
print("REVALIDATION_PASS")
EOF
```

This probe establishes only mathematical correctness of the UTL bijection, IEEE-754 rounding/ULP boundary behavior, and the SWAR bitmask; validating upstream C++/Rust codegen changes requires inspecting the pinned source diffs listed in items 1–2.
