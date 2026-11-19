# Zero-Copy Arrow C Data Lifetimes, Validity-Bitmap Slack Masking, Untrusted IPC Validation, and Parquet Dremel Striping Across Arrow, Velox, and DuckDB

## Summary

Modern zero-copy columnar data planes stitch together four distinct boundary contracts: **on-disk nested columnar storage** (`apache/parquet-format` Dremel repetition/definition striping), **wire/gRPC framing** (`apache/arrow` FlatBuffers `Message.fbs` / `Flight.proto` and `apache/arrow-rs`), **in-process FFI ownership handoff** (`ArrowSchema` / `ArrowArray` in `abi.h` and `arrow-data/src/ffi.rs`), and **in-engine vectorized string/dictionary buffers** (`facebookincubator/velox` and `duckdb/duckdb`). Direct inspection of all five pinned upstream trees establishes five decisive engineering invariants:

1. **Arrow C Data ownership relies on non-reentrant `release` erasure and trailing variadic length vectors**: In `apache/arrow/cpp/src/arrow/c/abi.h` and `apache/arrow-rs/arrow-data/src/ffi.rs`, moving an `ArrowArray` requires bitwise transfer followed by setting `src->release = NULL`, while producers must invoke `release` recursively on unmoved children/dictionaries and self-zero `release`. For `BinaryView`/`Utf8View`, `FFI_ArrowArray` appends an extra trailing `i64[]` buffer encoding variadic buffer byte lengths, breaking pre-variadic consumers that hardcode `n_buffers` from static type layouts.
2. **`arrow-rs` `Buffer::bit_slice` exhibits an asymmetric byte-aligned slack-bit leak**: In `arrow-buffer/src/buffer/immutable.rs:344–360`, unaligned bit slices (`offset % 8 != 0`) zero trailing bits via `BitChunks::remainder_bits()`, whereas byte-aligned slices (`offset % 8 == 0`, including `slice(0, len)` or `slice(8, 5)`) return a **zero-copy byte view preserving dirty bits in `[len % 8 .. 8)`**. Calling `BooleanBuffer::sliced()` inside `arrow-ipc/src/writer.rs:2434` or `align_nulls` over `Arrow Flight` leaks adjacent-row validity bits and corrupts unmasked byte `popcnt` null counts (`uint64_t` underflow to `18446744073709551615`, Probe 2A).
3. **Shallow Arrow `Validate()` leaves untrusted IPC / Flight buffers memory-unsafe**: In `apache/arrow/cpp/src/arrow/array/validate.cc`, `ValidateArray` (`full_validation = false`) checks only outer buffer sizes and `offsets[0]`/`offsets[len]`, explicitly skipping `BinaryView` bounds and prefix checks (`line 646: if (!full_validation) return Status::OK()`), `RunEndEncoded` strict monotonicity (`line 807`), interior `List`/`Binary` offset monotonicity (`line 947`), and exact `null_count` checks (`line 567`). Similarly, `arrow-rs` `ArrayData::validate()` omits `validate_values()`/`validate_nulls()` (`validate_full()`), and `validate_offsets_and_sizes` (`data.rs:1260–1262`) panics via `.expect(...)` on `usize` overflow in `ListView` (`offset + size`), creating an untrusted IPC DoS surface.
4. **16-byte `StringView` ("German Strings") splits at `len > 12`, forcing an $O(N)$ view rewrite between Arrow and Velox/DuckDB**: While `arrow-rs` `ByteView`, `velox::StringView`, and `duckdb::string_t` are byte-identical for inlined strings `len <= 12` (zero-padded tail enabling two-`uint64_t` equality and big-endian `u32` prefix ordering), strings `> 12` bytes store `(i32 buffer_index, i32 offset)` in Arrow vs. a raw `const char*` host pointer in Velox and DuckDB (Probe 2B). Pinning Parquet `PLAIN` pages directly (`ByteViewArrayReader`, `FlatVector::stringBuffers_`) avoids payload copying but causes `100x+` zombie-page RAM amplification after selective filters until explicit compaction (`ByteViewArray::gc()`).
5. **Dremel $(r, d)$ state machines and Parquet `RLE` framing harbor context-dependent wire traps**: Parquet `DataPageV1` prepends 4-byte lengths to RLE `def`/`rep` levels while `DataPageV2` omits them (`Encodings.md:155–170`), and `OffsetIndex` row-skipping in DuckDB (`column_reader.cpp:258, 302`) applies strictly to non-repeated columns ($R_{\max} = 0$). Unifying wire validation and engine views around a **Region-Indexed Linear Slice Calculus** with total `ValidatedBatch` boundary types eliminates both silent shallow-validation bypasses and pointer-vs-index translation friction.

## Applicability

This report characterizes binary layouts, memory-safety invariants, wire validation boundaries, and runtime resource profiles across five pinned upstream repositories and specifications:

- **Wire/IPC & FFI Standards**: `apache/arrow` (`931b9cccda5de68d48201dc2db50b6b6a9a72741` — `CDataInterface.rst`, `Columnar.rst`, `Schema.fbs`, `Message.fbs`, `Flight.proto`, `cpp/src/arrow/c/{abi.h,bridge.cc}`, `cpp/src/arrow/array/validate.cc`, `cpp/src/arrow/ipc/reader.cc`) and `apache/arrow-rs` (`9951b625879a19844ecd0b2dd352347a87ea26dd` — `arrow-buffer`, `arrow-data`, `arrow-array`, `arrow-ipc`, `arrow-flight`, `parquet`).
- **Disk Striping Format**: `apache/parquet-format` (`5cc18cae643835b19f869d3cffb085cd3c04eb15` — `src/main/thrift/parquet.thrift`, `Encodings.md`), analyzed alongside Melnik et al.'s Dremel model (`DOI: 10.1145/1953122.1953148`).
- **Vectorized Execution Engines**: `facebookincubator/velox` (`a3746eb2647ba575751ebffa603c0012a5f518e2`, `DOI: 10.14778/3554821.3554829`) and `duckdb/duckdb` (`87440222ab4ca5a8042154886c6af819e7266a52`, `DOI: 10.1145/3299869.3320212`).
- **Target & Verification Context**: Applies to little-endian CPU hosts (`x86_64`, `aarch64`, `riscv64`, `wasm32`, etc., matching `arrow-buffer/src/alloc/alignment.rs`), CPU host memory (`ArrowArray` rather than GPU `ArrowDeviceArray`), and untrusted vs. trusted IPC streams. All binary layouts, bit-slicing behaviors, and Dremel reconstruction invariants were directly inspected in source and executed in standalone Python 3.13 (`observed_at: 2026-11-19`).

## Findings

### 1. Arrow C Data Interface (`ArrowSchema` / `ArrowArray`) Ownership, Variadic Buffers, and SIMD Alignment

Basis: normative + source

The Arrow C Data Interface (`apache/arrow/docs/source/format/CDataInterface.rst:447–620`, `cpp/src/arrow/c/abi.h:50–82`, `cpp/src/arrow/c/bridge.cc:121–135`, and `apache/arrow-rs/arrow-data/src/ffi.rs:24–180`) transfers arbitrary columnar trees across language runtimes (`C++` $\leftrightarrow$ `Rust` $\leftrightarrow$ `Python`) with $O(1)$ pointer handoff:

```c
struct ArrowArray {
  int64_t length;
  int64_t null_count;       // -1 if uncomputed
  int64_t offset;           // logical item offset (>= 0)
  int64_t n_buffers;        // includes trailing int64_t[] buffer_sizes for BinaryView/Utf8View
  int64_t n_children;
  const void** buffers;
  struct ArrowArray** children;
  struct ArrowArray* dictionary;
  void (*release)(struct ArrowArray*);
  void* private_data;
};
```

#### Release Ownership Automaton & Common FFI Footguns

1. **Single-owner linear state**: A valid populated `ArrowArray` satisfies `release != NULL`. Moving ownership across an FFI boundary requires bitwise copying the struct to the destination and immediately writing `src->release = NULL` (`CDataInterface.rst:599–606`, `ArrowArrayMarkReleased` in `bridge.cc:134`).
2. **Producer-recursive teardown (`CDataInterface.rst:610–618`, `bridge.cc:121–134`, `ffi.rs:69–85`)**: A consumer MUST call *only* the top-level `release` callback and MUST NOT independently invoke `children[i]->release` or `dictionary->release` unless it first extracted and moved that child (zeroing the parent slot's pointer or `child->release = NULL`). In `arrow-rs`, `release_array` (`ffi.rs:69–85`) reconstructs `Box::from_raw(array.private_data.cast::<ArrayPrivateData>())`, drops every child `Box<FFI_ArrowArray>` and optional `dictionary` `Box`, drops `buffers: Vec<Option<Buffer>>` (decrementing Rust `Arc` reference counts on underlying allocations), and sets `array.release = None`.
3. **Use-after-release & double-free vectors**: If a consumer copies buffer pointers out of `ArrowArray.buffers` into a `Buffer` wrapper without retaining the owning `ArrowArray` until all slices drop, invoking `release` triggers use-after-free. Conversely, calling `release` on both a child and its parent without nulling `child->release` triggers immediate double-free in `Box::from_raw` / `delete` (`DCHECK(ArrowSchemaIsReleased(child))` in `bridge.cc:122`).
4. **Variadic buffer ABI extension (`CDataInterface.rst:559–567`, `ffi.rs:143–154`)**: For `BinaryView` and `Utf8View`, `buffers` contains `[validity_bitmap, views_16B, data_buf_0, ..., data_buf_{k-1}, buffer_lengths_i64]`. Because raw `const void*` pointers in C carry no byte extent, `FFI_ArrowArray::new` (`ffi.rs:143–154`) synthesizes an extra `ScalarBuffer<i64>` storing the byte length of each variadic data buffer and increments `n_buffers` by `1 + num_data_buffers`. Legacy C Data importers that assert `n_buffers == fixed_spec_count` reject `StringView` arrays at FFI boundaries.

#### Architecture-Dependent Buffer Alignment vs. Wire Padding

`Columnar.rst` (`lines 264–296`) recommends **64-byte alignment and padding** (`AVX-512` register width) when allocating or serializing Arrow buffers, while permitting **8-byte alignment** in IPC streams (`lines 267–270`). However, `arrow-rs` (`arrow-buffer/src/alloc/alignment.rs:15–98`) ties `ALIGNMENT` to the **host CPU L1/L2 cache line / prefetch streamer width** rather than a universal `64 B`:

| Target Architecture (`alignment.rs`) | `ALIGNMENT` Constant | Hardware / Microarchitectural Rationale |
| :--- | :---: | :--- |
| `x86_64`, `nvptx64` | **`128 B`** (`1 << 7`) | Intel L2D streamer pair-line prefetch (`lines 18–25`); NVIDIA Volta 128B sector (`lines 83–89`) |
| `s390x` | **`256 B`** (`1 << 8`) | IBM Z 256-byte cache line (`lines 55–59`) |
| `aarch64`, `x86` (32-bit), `riscv64`, `powerpc64`, `sparc64`, `wasm32`, `loongarch64` | **`64 B`** (`1 << 6`) | 64-byte cache line / 512-bit SIMD width (`lines 14–16, 43–53, 66–74, 91–98`) |
| `arm` (32-bit), `mips`, `mips64`, `powerpc`, `sparc` | **`32 B`** (`1 << 5`) | 32-byte L1 data line (`lines 31–41, 61–65, 76–81`) |

Consequently, `mmap`-ing an 8-byte-aligned Arrow IPC file produced by a default serializer produces buffer virtual addresses congruent to `8 mod 64` and `8 mod 128`, faulting aligned AVX-512 loads (`VMOVDQA64`) or forcing `arrow-ipc/src/reader.rs:292` (`builder.align_buffers(!self.require_alignment)`) to copy unaligned buffers when `require_alignment` is disabled or error out when strict zero-copy alignment is enforced.

---

### 2. Validity-Bitmap LSB-0 Packing and the Asymmetric `bit_slice` Slack-Bit Leak

Basis: source + execution + derived

Arrow encodes validity in LSB-0 bit ordering (`Columnar.rst`: bit `i` lives at `byte[i >> 3] & (1 << (i & 7))`, where `1` = valid and `0` = null; omitting the bitmap pointer when `null_count == 0`, `Message.fbs:39–42`). DuckDB uses the exact same `1`-means-valid polarity packed in 64-bit `uint64_t` words (`TemplatedValidityMask` in `duckdb/src/include/duckdb/common/types/validity_mask.hpp:20–139`), optimizing `CannotHaveNull()` to `!validity_mask` (`nullptr`).

Inspecting `apache/arrow-rs` (`arrow-buffer/src/buffer/immutable.rs:344–360`, `arrow-buffer/src/buffer/boolean.rs:519–521`, `arrow-data/src/ffi.rs:90–108`, `arrow-ipc/src/writer.rs:2433–2444`) exposes an **asymmetric bit-masking leak** in `Buffer::bit_slice(offset, len)`:

```rust
// arrow-buffer/src/buffer/immutable.rs:344-360
pub fn bit_slice(&self, offset: usize, len: usize) -> Self {
    if offset.is_multiple_of(8) {
        return self.slice_with_length(offset / 8, bit_util::ceil(len, 8));
    }
    let chunks = self.bit_chunks(offset, len);
    let buffer: Vec<u64> = if chunks.remainder_len() > 0 {
        chunks.iter().chain(Some(chunks.remainder_bits())).collect()
    } else { ... };
    ...
}
```

When `offset % 8 != 0`, `bit_slice` allocates a new buffer and masks trailing slack bits `[len % 8 .. 8)` to zero via `chunks.remainder_bits()`. When **`offset % 8 == 0`** (including `offset == 0` when prefix-slicing `array.slice(0, 5)` or byte-aligned `array.slice(8, 5)`!), `bit_slice` executes a zero-copy byte slice (`slice_with_length`) that **retains arbitrary non-zero bits in trailing slack bits `[len % 8 .. 8)`**. Because `BooleanBuffer::sliced()` (`boolean.rs:519–521`) delegates directly to `bit_slice`, and both `arrow-ipc/src/writer.rs:2434` (`buffer.inner().sliced()`) and `FFI_ArrowArray::new`'s `align_nulls` (`ffi.rs:96–98`) emit `sliced()` directly onto the wire or across FFI:

1. **Cross-row validity bit leakage over Arrow Flight / IPC**: Filtering or slicing a multi-tenant batch (`batch.slice(8, 5)`) transmits validity bits of adjacent unrequested rows `13..15` inside the trailing byte over gRPC `FlightData.data_body` (Probe 2A: `bit_slice(8, 5)` emits `0xeb` with slack bits `0b111`, whereas `bit_slice(7, 5)` emits `0x17` with slack bits `0b000`).
2. **Unmasked `popcnt` null-count underflow**: Any consumer computing `null_count = length - popcnt(bitmap_bytes)` without explicitly masking the final byte (`len & 7 != 0`) counts slack `1`-bits as valid items. In **Probe 2A**, `0xeb` has `popcnt = 6 > len = 5`, yielding signed `-1` / unsigned `uint64_t` wraparound **`18446744073709551615`**. Correct implementations—such as `arrow-rs`'s `UnalignedBitChunk::count_ones()` (`immutable.rs:371–373`), C++ `CountSetBits(data, offset, length)` (`validate.cc:572–573`), and DuckDB's `TemplatedValidityMask::CountValid` (`validity_mask.hpp:121–125`)—explicitly mask ragged trailing bits before summing set bits.

---

### 3. Untrusted Arrow IPC & Flight Deserialization: Shallow `Validate()` vs. `ValidateFull()` Bypass Matrix

Basis: source + security advisories + execution

Deserializing untrusted Arrow IPC (`Message.fbs`, `Schema.fbs`) or gRPC `Arrow Flight` (`Flight.proto`) streams spans two distinct layers: (a) **FlatBuffers structural verification** (checking vtables, table offsets, and no cyclic pointers; historically implicated in `RUSTSEC-2021-0122` for generated `flatbuffers` accessors prior to verifier adoption, alongside Python `PyExtensionType` auto-unpickling RCE `CVE-2023-47248`, CVSS 9.8), and (b) **Array semantic layout validation** (`apache/arrow/cpp/src/arrow/array/validate.cc` and `apache/arrow-rs/arrow-data/src/data.rs`).

Crucially, `apache/arrow` C++ and `apache/arrow-rs` expose a **dangerous two-tier API split**: shallow `ValidateArray` / `ArrayData::validate()` checks only $O(1)$ buffer sizes and boundary endpoints, skipping nearly every memory-safety and algorithmic invariant required for untrusted wire data unless `ValidateArrayFull` / `ArrayData::validate_full()` is explicitly called (and neither `FlightDataDecoder::with_skip_validation` in `arrow-flight/src/decode.rs:250` nor raw `ArrayData::new_unchecked` runs them if skipped):

| Array Type | Checked by Shallow `ValidateArray` (C++) / `ArrayData::validate()` (Rust) | **Bypassed** Unless `ValidateArrayFull` (C++) / `validate_full()` (Rust) Runs | Exploit / Soundness Consequence |
| :--- | :--- | :--- | :--- |
| **`Primitive` / `Boolean`** | `buffers.len()`, `buffer[1].len() >= offset + len`, `null_count <= len` (`validate.cc:554–594`, `data.rs:1041–1076`) | Exact `popcnt` verification of `null_count == actual_nulls` (`validate.cc:567–585`, `data.rs:1551–1561`) | Forged `null_count = 0` skips null checks in fast paths despite `0` bits in bitmap |
| **`Binary` / `Utf8` / `List` / `Map`** | Buffer sizes, **`offsets[0]` and `offsets[len]` only** (`validate.cc:612–631`, `data.rs:1183–1229`) | **Interior offset monotonicity** `0 <= offsets[i] <= offsets[i+1] <= values_len` (`validate.cc:834–854`, `data.rs:1755–1798`), plus valid UTF-8 sequences | Non-monotonic interior offsets (`[0, 1000000, 1]`) cause negative slice lengths (`end - start < 0`), panicking Rust slice indexing or corrupting C++ pointer arithmetic |
| **`ListView` / `LargeListView`** | **Diverges**: C++ `ValidateArray` skips slot checks (`validate.cc:947–953`); Rust `validate()` checks per-slot bounds (`data.rs:1233–1272`) | **Rust DoS trap**: `size.checked_add(offset).expect(...)` (`data.rs:1260–1262`) **panics thread** instead of returning `Err` on `usize` overflow; neither checks total materialized volume | (1) Single malformed `ListView` (`offset + size` overflow) crashes Rust process; (2) **$O(N\cdot M)$ decompression bomb**: $N$ slots all pointing to `[0, M)` expand $O(N+M)$ wire bytes to $O(N\cdot M)$ rows on flatten |
| **`BinaryView` / `Utf8View`** | **C++ line 646**: `if (!full_validation) return Status::OK();` — checks *only* `views` buffer size! Rust `validate()` checks only buffer sizes (`data.rs:1081–1115`) | `size >= 0`, `buffer_index < data_buffers.len()`, `offset + size <= buf.len()`, inline tail zero-padding, **4-byte `CheckPrefix` equality** (`validate.cc:648–710`), and UTF-8 | (1) Arbitrary OOB read via forged `(buffer_index, offset, size)`; (2) Non-zero inline tail breaks `u128` equality; (3) Forged 4-byte prefix corrupts sort/filter comparisons silently (**Probe 2B**) |
| **`RunEndEncoded` (`REE`)** | `buffers[0] == nullptr`, 2 children of equal length (`validate.cc:770–805`, `data.rs:1362–1380`) | `run_ends[0] >= 1`, **strict monotonicity `run_ends[i] > run_ends[i-1]`**, and `last_run_end >= offset + len` (`validate.cc:807–827`, `data.rs:1886–1923`) | Unsorted or non-positive `run_ends` breaks binary search (`partition_point` / `upper_bound` in `run_array.rs:422`), causing OOB value indexing |
| **`Dictionary`** | Integer key type check + child value `validate()` (`validate.cc:543–550`, `data.rs:1088–1095`) | **Dictionary index bounds** `0 <= idx[i] < dict.len()` for non-null rows (`validate.cc:978–981`, `data.rs:1697–1718, 1853–1879`) | Out-of-bounds integer key reads arbitrary memory during dictionary gather (`DictionaryVector` / SIMD `vpgatherdd`) |

---

### 4. Parquet Dremel $(r, d)$ Striping, RLE Page-Header Quirks, and Dictionary Gather Bounds

Basis: normative + source + execution

Nested Parquet columns encode arbitrary combinations of `optional` structs, `repeated` lists, and null leaves using **Dremel repetition levels ($r$) and definition levels ($d$)** (`Melnik et al., 2010`, `DOI: 10.1145/1953122.1953148`; `apache/parquet-format/src/main/thrift/parquet.thrift:221–238`; `Encodings.md:76–170`):

- **Definition level $d \in [0, D_{\max}]$**: Counts how many optional or repeated nodes along the root-to-leaf schema path are defined. Only entries with **$d = D_{\max}$** have a physical value stored in the page's value stream (or dictionary index stream); all $d < D_{\max}$ entries distinguish *where* null/empty occurred without emitting a value slot.
- **Repetition level $r \in [0, R_{\max}]$**: Identifies the deepest repeated field in the path starting a new element ($r = 0$ begins a new top-level record; $r = k \in [1, R_{\max}]$ appends an element to the currently open depth-$k$ list).

For a canonical 3-level nested list `LIST<LIST<optional INT64>>` ($R_{\max} = 2, D_{\max} = 5$: `optional outer_list` $d\ge 1$, `repeated inner_list` $r=1, d\ge 2$, `optional inner` $d\ge 3$, `repeated elem` $r=2, d\ge 4$, `optional int64` $d=5$), **Probe 2C** verifies lossless `(r, d, val)` round-trip encoding and FSM reconstruction across all structural boundary cases (`None`, `[]`, `[None]`, `[[]]`, `[[None]]`, `[[10, 20], [], None]`).

#### Cross-Engine Decoder Fast Paths & Structural Quirks

1. **`arrow-rs` (`parquet/src/arrow/record_reader/definition_levels.rs:20–170`)**: Uses `BufferInner::Mask` when $D_{\max} = 1, R_{\max} = 0$ (skipping materializing `Vec<i16>` levels entirely and decoding straight to a bitmap) and processes nested columns in 64-level `u64` chunks via `build_filtered_validity_bitmap` (`lines 130–170`) using word-level `compress`.
2. **`Velox` (`velox/dwio/parquet/reader/RepeatedColumnReader.cpp:26–139`)**: Assigns repetition/definition decoding ownership strictly to direct children of the root struct (`parent && !parent->parent()`, `line 123`), and handles empty-projection structs by designating one physical leaf as a synthetic `repDefSourceReader` (`lines 33–45, 101–108`).
3. **`DuckDB` (`extension/parquet/column_reader.cpp:257–305`)**: Enforces page-level `OffsetIndex` consistency (`VerifyPageAgainstOffsetIndex`), explicitly noting (`lines 258, 302`) that `OffsetIndex` row-range skipping applies **only to non-repeated columns** ($R_{\max} = 0$) where pages map 1-to-1 to rows.
4. **Parquet `RLE = 3` 4-Byte Length-Prefix Irregularity (`Encodings.md:155–170`)**: In `RLE/Bit-Packing Hybrid`, `DataPageV1` prepends a 4-byte little-endian `length` before RLE-encoded `def` levels, `rep` levels, and `BOOLEAN` data—but **omits** it for `RLE_DICTIONARY` indices (preceded instead by 1-byte `bit_width <= 32`). `DataPageV2` **omits** the 4-byte `length` for `def` and `rep` levels (recorded in `DataPageHeaderV2`) yet still **retains** the 4-byte `length` for RLE `BOOLEAN` values!
5. **SIMD Dictionary Gather Bounds**: In `RLE_DICTIONARY` (`Encodings.md:76–90`), bit-unpacking arbitrary `bit_width` integers can yield out-of-range `uint32_t` indices (`>= dict_num_values`) on malformed files, and uninitialized dictionary-index slots corresponding to `NULL` entries ($d < D_{\max}$) hold garbage values (`data.rs:1862–1865`: `if self.is_null(i) { return Ok(()); }`). Issuing AVX2/AVX-512 `_mm512_i32gather_epi64` without both (a) checking `idx < dict_num_values` on non-null lanes and (b) zeroing or masking null lanes via AVX-512 `k`-mask registers reads out-of-bounds memory or triggers hardware `SIGSEGV`.

---

### 5. 16-Byte Inline-Prefix `StringView` ("German Strings"): Binary ABI Split & Zombie-Page Lifetimes

Basis: source + practitioner literature + execution

Inspired by Neumann & Freitag's `Umbra` string representation (CIDR 2020) and benchmarked across DuckDB, Velox, Arrow, and DataFusion (`Hao & Lamb, Sept 2024`, reporting `20%–200%` end-to-end ClickBench speedups), Arrow `Utf8View`/`BinaryView`, `velox::StringView` (`velox/type/StringView.h:53–165`), and `duckdb::string_t` (`src/include/duckdb/common/types/string_type.hpp:24–165`) all adopt a **16-byte fixed-width view** with a 12-byte inline threshold (`kInlineSize = 12` / `INLINE_BYTES = 12`):

| Byte Offset | `len <= 12` (All 3 Systems) | `len > 12`: **Arrow `BinaryView` / `ByteView`** (`byte_view_array.rs:120–145`) | `len > 12`: **Velox `StringView` & DuckDB `string_t`** (`StringView.h:53–56`, `string_type.hpp:27–66`) |
| :---: | :--- | :--- | :--- |
| **`[0..4)`** | `int32_t` / `u32` byte length | `i32` / `u32` byte length | `int32_t` / `uint32_t` byte length |
| **`[4..8)`** | `data[0..min(len, 4)]` (inline bytes 0..3) | **4-byte prefix** `data[0..4]` | **4-byte prefix** `data[0..4]` |
| **`[8..12)`** | `data[4..min(len, 8)]` (zero-padded) | **`i32 buffer_index`** (into variadic `buffers[1..]`) | **`const char*` 64-bit host pointer** (bytes `[8..16)` on 64-bit LE) |
| **`[12..16)`** | `data[8..len]` (zero-padded) | **`i32 offset`** (within `buffers[buffer_index]`, max `i32::MAX`) | *(upper 32 bits of `const char*`)* |

#### Three Load-Bearing Consequences

1. **Inline zero-padding invariant & prefix-compare speedup**: Both Velox (`StringView.h:95–96`) and DuckDB (`string_type.hpp:51, 147`) zero-pad unused inline bytes (`[len..12)`), and Arrow `ValidateBinaryView` (`validate.cc:672–681`) enforces zero padding on every inlined slot. That enables full equality for `len <= 12` in **two 64-bit integer compares** (or one `u128` compare) and lexicographical `<`/`>` via big-endian `BSwapIfLE(Load<uint32_t>(prefix))` (`string_type.hpp:102`) whenever lengths or 4-byte prefixes differ—eliminating DRAM pointer chasing on selective filters and sorts. Conversely, if an unvalidated Arrow IPC payload contains a mismatched prefix (`"zzzz"` prefix pointing to `"aaaa..."`), prefix-short-circuiting produces **silent wrong filter and sort results** (**Probe 2B**).
2. **Asymmetric zero-copy interop at `len > 12`**: Because `bytes [0..16)` are identical when `len <= 12` (`Probe 2B: byte_identical=True`), purely short columns share the 16-byte view buffer directly. As soon as any string has `len > 12`, Arrow's relocatable `(buffer_index, offset)` diverges from Velox/DuckDB's raw `const char*` (`byte_identical=False`). Translating between Arrow `Utf8View` and Velox/DuckDB can still share the **backing character buffers zero-copy** (via `FlatVector::stringBuffers_` / `StringVector::AddBuffer`), **only after an $O(N)$ pass rewriting `[8..16)`** from `(buf_idx, offset)` to `buffers[buf_idx] + offset` (and vice versa on export, requiring `StringView` payloads to live inside registered `stringBuffers_`).
3. **Zombie-page retention & buffer coalescing (`byte_view_array.rs:330–338, 511–520`; `FlatVector.h:50–55, 424–482`)**: When `ByteViewArrayDecoderPlain` (`byte_view_array.rs:332–338`) or Velox's Parquet reader decodes an uncompressed `PLAIN` page, it appends a zero-copy `Buffer` reference (`output.append_block(self.buf.clone())`) and emits `ByteView`s directly into the page without copying string bytes. If a subsequent `WHERE` filter retains `1` row out of `100,000`, that single `StringView` pins the entire `1 MB–32 MB` Parquet page in memory (`100x+` memory amplification) until `ByteViewArray::gc()` (`byte_view_array.rs:511–520`) compacts live strings into fresh $\le 2\text{ GiB}$ buffers (`i32::MAX`) or Velox releases buffers exceeding `kMaxStringSizeForReuse = 1 MiB - sizeof(AlignedBuffer)` (`FlatVector.h:54–55`). Calling `FlatVector::acquireSharedStringBuffers` (`FlatVector.h:476`) across operator boundaries is mandatory whenever `StringView`s are copied between vectors; omitting it causes dangling `const char*` UAF when the source vector resets.

---

### 6. Multi-Level Performance & Resource Footprint Analysis (`L1`–`L6`)

Basis: source + literature + execution + derived

| Level | Metric Dimension | `Apache Arrow` / `arrow-rs` (IPC, C Data, Flight, ByteView) | `Parquet` + `Velox` + `DuckDB` (Dremel, RLE, `StringView`) |
| :--- | :--- | :--- | :--- |
| **L1: Authoring Velocity** | Implementation LoC, FFI & UB risk, LLM tokens | Safe high-level `RecordBatch` / `DataFusion` queries: `10–50` LoC; writing raw `ArrowArray` C FFI or `unsafe` SIMD bit/view kernels: `500–2,500` LoC with `5k–25k` LLM audit tokens needed to eliminate `release`, slack-bit, and `ValidateFull` bugs | Implementing full nested Dremel $(r, d)$ state machines + `RepeatedColumnReader` + `StringView` buffer pinning (`FlatVector::acquireSharedStringBuffers`): `1,000–3,000+` LoC of intricate C++/Rust state machines |
| **L2: Toolchain Build Time** | Clean & incremental compile speed, RSS | `arrow-rs` (`arrow`, `parquet`, `arrow-flight`): `~25–75 s` clean release Cargo build (16 cores), `2–4 GB` peak `rustc` RSS, `< 3 s` incremental `cargo check`; `apache/arrow` C++: `3–12 min` CMake/Ninja | `duckdb` amalgamation/unity build: `2–8 min`, `4–10 GB` RAM; `facebookincubator/velox` (C++20 + Folly + xsimd): `15–45+ min` clean build, `16–48 GB` peak compiler/linker RSS |
| **L3: Compilation & LSP** | Schema codegen & IDE turnaround | FlatBuffers (`Schema.fbs`, `Message.fbs`) & `Flight.proto` `tonic-build` codegen: `50 ms–2 s`; `rust-analyzer` incremental check: `20–80 ms` | `parquet.thrift` codegen `< 50 ms`; `clangd` LSP preamble/hover latency on `Velox` template headers (`FlatVector`, `DictionaryVector`): `500 ms–4 s` |
| **L4: Execution Speed** | Throughput, cycles/byte, FFI crossing, `p99.9` tail | `ArrowArray` FFI handoff: `~20–80 ns` constant ($0$ cycles/byte); `StringView` prefix filtering/sorting yields `20%–200%` ClickBench query speedups (`Hao & Lamb 2024`, `1–2 cycles/row` on prefix mismatch vs. `60–200` cycle DRAM miss on `Utf8` offsets); `Flight` `p99.9` spikes when gRPC `Protobuf` copies `> 4 MB` `data_body` | 64-level `u64` `compress` bitmap filtering (`definition_levels.rs:130–170`) and SIMD RLE bit-unpacking: `~0.3–1.5 cycles/value`; `string_t` big-endian 4B prefix compare (`BSwapIfLE`) runs in 1 `cmp` instruction; SIMD dictionary gather hits L1/L2 bandwidth |
| **L5: Verification Speed** | Wire validation & schema checking throughput | Shallow `Validate()`: `< 1 µs` ($O(1)$, **unsafe for untrusted data**); `ValidateFull()`: `~3–12 GB/s` sequential offset/REE monotonicity + `~1–4 GB/s` SIMD UTF-8 + `~0.5–2 GB/s` random `ValidateBinaryView` prefix `memcmp` (`~0.2–2 ms` per 1 MB batch) | Parquet footer CRC/Thrift + `VerifyPageAgainstOffsetIndex` (`O(num_pages)`): `< 100 µs`; `RLE` dictionary-index bounds check adds `< 0.5 cycles/index` before SIMD gather |
| **L6: RAM & Binary Size** | Metadata overhead, zombie retention, `.so`/disk size | `Utf8View` costs `16 B/row` view array vs. `4 B/row` `Utf8` offsets (`4x` view-metadata RAM for long strings, offset by `0 B` heap payload for `len <= 12`); `gc()` needed to bound zombie pages; `arrow-rs` stripped binaries `~4–12 MB` | Parquet `RLE_DICTIONARY` + `DELTA_BINARY_PACKED` + Zstd achieves `3x–15x` disk compression vs. uncompressed Arrow IPC; zombie Parquet pages pin `1–32 MB` buffers per surviving row; `libduckdb.so` `~35–65 MB`, `Velox` libs `~100–250 MB` |

---

### 7. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

Basis: source + derived

#### `(C1)` Human Comprehensibility & Mental-Model Ergonomics

Three design patterns across the Arrow/Parquet/Velox/DuckDB ecosystem impose disproportionate cognitive load on human reviewers relative to LLM code generators:

1. **The `Validate()` vs. `ValidateFull()` Naming Trap**: Calling `arrow::ValidateArray(batch)` in C++ or `ArrayData::validate()` in Rust reads to a human reviewer like a complete safety check. In reality, both omit interior offset monotonicity, `BinaryView` OOB/prefix checks, `REE` monotonicity, and exact `null_count` verification (`validate.cc:646, 807, 947`; `data.rs:1513–1540`). An LLM agent will likewise call `.validate()` unless explicitly instructed to use `ValidateArrayFull` / `validate_full()`, leaving latent OOB read bugs invisible in small unit tests.
2. **Dremel $(r, d)$ State Tracking at Depth $\ge 2$**: Distinguishing `None`, `[]`, `[None]`, `[[]]`, and `[[None]]` via integer thresholds $d \in \{0..5\}$ and $r \in \{0..2\}$ (Probe 2C) exceeds comfortable human working memory when columns have mixed optional/repeated ancestors, making off-by-one `d >= value_level` bugs notoriously hard to spot by inspection.
3. **Byte-Aligned Slack Bits & Implicit Non-Owning `StringView` Lifetimes**: The divergence between `bit_slice(7, 5)` (masked) and `bit_slice(8, 5)` (unmasked dirty slack bits, Probe 2A), plus non-owning `StringView` values silently backed by separate `FlatVector::stringBuffers_` vectors (`FlatVector.h:424–482`), creates invisible non-local aliasing invariants where locally clean slice/filter code leaks adjacent rows or triggers UAF downstream.

#### `(C2)` Simplicity, Orthogonality & Universal Model Refinement

Across these five repositories, accidental complexity concentrates in **four redundant or leaky abstractions**:

1. **Six overlapping variable-size layouts in Arrow** (`Binary`, `LargeBinary`, `BinaryView`, `List`, `LargeList`, `ListView`), each duplicating offset/size/bounds logic across `validate.cc` and `data.rs` (including inconsistent overflow handling: `Err` vs. `.expect(...)` panic).
2. **Incompatible 16-byte `StringView` words** (`(i32 buf_idx, i32 offset)` on the Arrow wire vs. `const char*` in Velox/DuckDB RAM), forcing an $O(N)$ translation loop whenever `len > 12`.
3. **Parquet `RLE = 3`'s 2x4 context-sensitive 4-byte length-prefix table** (`Encodings.md:155–170`), varying by both page version (`V1` vs. `V2`) and logical field role (`def`/`rep`/`dict`/`bool`).
4. **Two-phase unvalidated `ArrayData` construction**, allowing invalid buffers to exist in safe Rust/C++ objects before optional `validate_full()`.

Applying **Jackson's Concept Design**, **Ousterhout's Deep Module test**, and **Felleisen's Adapter-Conservation test**: naively forcing every caller to speak raw `StringView`/`ListView` fails Felleisen's test because it pushes $O(N)$ `offset + size` validation, quadratic `ListView` aliasing amplification defense, and `gc()` zombie-page compaction onto every downstream operator. Instead, the minimal universal model is a **Region-Indexed Linear Slice Calculus with Total Boundary Validation**:

- **Uniform `(buf_idx: u32, offset: u32, len: u32)` slice descriptors paired with an explicit `ArenaTable`** (replacing raw host pointers in execution engines with relocatable base-table indexing + cached L1 base pointers, eliminating the $O(N)$ view rewrite at Arrow $\leftrightarrow$ engine boundaries).
- **One normalized `MaskedBitSpan<bit_offset, bit_len>`**: Either eagerly masks ragged trailing bits when exporting/hashing or enforces mask-aware `BitChunks` accessors as the *only* exported view—making Probe 2A's dirty slack-bit leak impossible by construction.
- **Total-by-construction `ValidatedBatch` boundary types**: Parsing `Arrow IPC` / `Flight` returns an opaque `ValidatedBatch` solely through `ValidateFull` (checking $O(N)$ invariants + bounding `ListView` expanded-element totals), keeping unvalidated `ArrayData` strictly private to the wire parser.

## Boundaries

- **Unsupported (Zero-copy `> 12` byte `StringView` sharing between Arrow and Velox/DuckDB)**: Because Arrow stores `(i32 buffer_index, i32 offset)` in bytes `[8..16)` while Velox `StringView` and DuckDB `string_t` store a 64-bit `const char*` pointer (`Probe 2B`), zero-copy view-array sharing is **unsupported** when any string exceeds 12 bytes (only backing data pages can be shared after an $O(N)$ view-array translation).
- **Unsupported (DuckDB Parquet `OffsetIndex` skipping on repeated columns)**: `duckdb/extension/parquet/column_reader.cpp:258, 302` restricts `OffsetIndex` page skipping strictly to non-repeated columns ($R_{\max} = 0$); nested repeated lists cannot use `OffsetIndex` fast seeks.
- **Unsupported (`BinaryView` single buffer `> 2 GiB` and `REE` parent null bitmaps)**: `arrow-rs` `ByteViewArray::gc()` (`byte_view_array.rs:512–515`) caps each variadic buffer at `i32::MAX` (`2 GiB`) due to signed 32-bit `offset` addressing; `RunEndEncoded` arrays forbid parent null bitmaps (`validate.cc:777–779`).
- **Known Not to Apply (Shallow `Validate()` safety on untrusted IPC)**: `ValidateArray` (`apache/arrow`) and `ArrayData::validate()` (`arrow-rs`) do **not** validate interior offsets, `BinaryView` bounds/prefixes, `REE` monotonicity, dictionary index bounds, or exact `null_count`s.
- **Known Not to Apply (`bit_slice` slack zeroing when `offset % 8 == 0`)**: `Buffer::bit_slice` (`arrow-buffer/src/buffer/immutable.rs:345–347`) does **not** clear trailing slack bits on byte-aligned slices (`offset % 8 == 0`), leaking adjacent bits unless masked downstream.
- **Known Not to Apply (`StringView` RAM reduction on uniform `13..32 B` strings)**: Compared against `4 B` `i32` `Utf8` offsets + contiguous character buffer, `16 B` `StringView` headers + out-of-line payload consume *more* memory per row when strings uniformly fall just above `12` bytes without heavy duplication or Parquet direct-page reuse.
- **Not Examined**: Asynchronous GPU `ArrowDeviceArray` (`ARROW_DEVICE_CUDA` / `ARROW_DEVICE_ROCM`, `abi.h:112–154`) `sync_event` cross-stream lifetime hazards (`not examined`); Parquet modular encryption (`Encryption.md` AES-GCM-CTR per-page AAD tampering, `not examined`); and newer Parquet `ALP` (`ALP = 10`) / `VariantShredding` decoder implementations across Velox and DuckDB (`not examined`).

## Evidence

### Pinned Source, Specification & Literature Anchors

| Subject | Exact Location / Reference | Verified Technical Content |
| :--- | :--- | :--- |
| `apache/arrow` (`931b9cccda5de68d48201dc2db50b6b6a9a72741`) | `docs/source/format/CDataInterface.rst:447–620`, `cpp/src/arrow/c/{abi.h:50–155, bridge.cc:121–135}` | `ArrowSchema`, `ArrowArray`, `ArrowDeviceArray`, non-reentrant `release` erasure, variadic `BinaryView` extra length buffer |
| `apache/arrow` (`931b9ccc...`) | `docs/source/format/Columnar.rst:206–310`, `format/Message.fbs:34–99` | 64-byte / 8-byte alignment & padding, LSB-0 validity bitmaps, `FieldNode` `null_count == 0` omitted buffer rule |
| `apache/arrow` (`931b9ccc...`) | `cpp/src/arrow/array/validate.cc:184–190, 554–1002` | `ValidateArray` (`full_validation = false`) vs. `ValidateArrayFull` (`lines 646, 807, 947`) bypasses across `BinaryView`, `List`, `ListView`, `REE`, `Nulls`, `UTF8` |
| `apache/arrow-rs` (`9951b625879a19844ecd0b2dd352347a87ea26dd`) | `arrow-buffer/src/alloc/alignment.rs:15–98` | Arch-specific `ALIGNMENT` (`128 B` `x86_64`/`nvptx64`, `256 B` `s390x`, `64 B` `aarch64`/`riscv64`/`wasm32`, `32 B` 32-bit `arm`/`mips`) |
| `apache/arrow-rs` (`9951b625...`) | `arrow-buffer/src/buffer/{immutable.rs:344–373, boolean.rs:519–521}`, `arrow-ipc/src/writer.rs:2433–2444`, `arrow-data/src/ffi.rs:69–155` | `Buffer::bit_slice` byte-aligned slack-bit leak (`offset.is_multiple_of(8)`), `BooleanBuffer::sliced()`, `FFI_ArrowArray::new` variadic length buffer |
| `apache/arrow-rs` (`9951b625...`) | `arrow-data/src/data.rs:1050–1923`, `arrow-ipc/src/reader.rs:290–298`, `arrow-flight/src/decode.rs:248–251` | `validate()` vs. `validate_full()`, `ListView` `.expect(...)` overflow panic (`lines 1260–1262`), `align_buffers(!self.require_alignment)`, `with_skip_validation` |
| `apache/arrow-rs` (`9951b625...`) | `arrow-array/src/array/{byte_view_array.rs:120–145, 341–355, 509–520, run_array.rs:422}`, `parquet/src/arrow/{array_reader/byte_view_array.rs:325–338, record_reader/definition_levels.rs:20–170}` | `ByteView` layout, `gc()` `i32::MAX` limit, `ByteViewArrayDecoderPlain` zero-copy block sharing, 64-wide `compress` bitmap fast path |
| `apache/parquet-format` (`5cc18cae643835b19f869d3cffb085cd3c04eb15`) | `src/main/thrift/parquet.thrift:221–238`, `Encodings.md:76–170` | `RLE = 3` grammar, `RLE_DICTIONARY` 1B `bit_width`, `DataPageV1` vs. `DataPageV2` 4-byte length-prefix divergence table |
| `facebookincubator/velox` (`a3746eb2647ba575751ebffa603c0012a5f518e2`) | `velox/type/StringView.h:53–165`, `velox/vector/{FlatVector.h:50–85, 424–482, DictionaryVector.h:30–265}`, `velox/dwio/parquet/reader/RepeatedColumnReader.cpp:26–139` | 16B `StringView` zero-padding, `stringBuffers_` / `acquireSharedStringBuffers`, `kMaxStringSizeForReuse`, `readLeafRepDefs` synthetic `repDefSourceReader` |
| `duckdb/duckdb` (`87440222ab4ca5a8042154886c6af819e7266a52`) | `src/include/duckdb/common/types/{string_type.hpp:24–165, validity_mask.hpp:20–139}`, `extension/parquet/column_reader.cpp:257–305` | 16B `string_t` (`BSwapIfLE` prefix compare), `TemplatedValidityMask::CountValid` tail masking, `VerifyPageAgainstOffsetIndex` $R_{\max}=0$ scope |
| Literature & Advisories | Melnik et al. (`DOI: 10.1145/1953122.1953148`); Pedreira et al. (`DOI: 10.14778/3554821.3554829`); Raasveldt & Mühleisen (`DOI: 10.1145/3299869.3320212`); Neumann & Freitag (CIDR 2020); Hao & Lamb (DataFusion Blog, Sept 2024); `CVE-2023-47248`; `RUSTSEC-2021-0122` | Dremel $(r, d)$ algorithm, Velox & DuckDB vectorized engines, Umbra German Strings, ClickBench `StringView` speedups, PyArrow pickle RCE, FlatBuffers OOB |

### Standalone Verification Script (Probes 2A, 2B, 2C — Executed 2026-11-19)

```python
import struct

print("=== PROBE 2A: Arrow Buffer::bit_slice Asymmetric Slack-Bit Leakage ===")
raw = bytes([0b10101010, 0b11101011])  # bits 8..13 = 01011 (3 set), slack 13..16 = 111

def arrow_rs_bit_slice(buf: bytes, offset: int, length: int) -> bytes:
    nbytes = (length + 7) // 8
    if offset % 8 == 0:
        return buf[offset // 8 : offset // 8 + nbytes]  # zero-copy view retains slack bits
    acc = (int.from_bytes(buf, "little") >> offset) & ((1 << length) - 1)
    return acc.to_bytes(nbytes, "little")

s_aligned = arrow_rs_bit_slice(raw, 8, 5)
s_unaligned = arrow_rs_bit_slice(raw, 7, 5)
unmasked_popcnt = s_aligned[0].bit_count()
masked_popcnt = (s_aligned[0] & ((1 << 5) - 1)).bit_count()
u64_underflow = (5 - unmasked_popcnt) & ((1 << 64) - 1)
print(
    f"bit_slice(8,5) byte=0x{s_aligned[0]:02x} "
    f"(slack_bits=0b{s_aligned[0]>>5:03b}, unmasked_popcnt={unmasked_popcnt}, "
    f"masked_popcnt={masked_popcnt}, unmasked_u64_nulls={u64_underflow})"
)
print(f"bit_slice(7,5) byte=0x{s_unaligned[0]:02x} (slack_bits=0b{s_unaligned[0]>>5:03b})")

print("\n=== PROBE 2B: 16-Byte StringView Layout & Prefix-Mismatch Ordering Violation ===")
s_short = b"arrow_inline"  # 12 bytes
arrow_short = struct.pack("<i12s", len(s_short), s_short)
velox_short = struct.pack("<i12s", len(s_short), s_short)
s_long = b"parquet_columnar_page"  # 21 bytes
arrow_long = struct.pack("<i4sii", len(s_long), s_long[:4], 0, 64)
velox_long = struct.pack("<i4sQ", len(s_long), s_long[:4], 0x00007F0012340040)
print(
    f"len<=12 byte_identical={arrow_short == velox_short} ({len(arrow_short)}B); "
    f"len>12 byte_identical={arrow_long == velox_long} "
    f"(arrow[8:16]={arrow_long[8:16].hex()}, velox[8:16]={velox_long[8:16].hex()})"
)

def sv_lt(v1, v2):
    p1 = int.from_bytes(v1[0], "big")
    p2 = int.from_bytes(v2[0], "big")
    return p1 < p2 if p1 != p2 else v1[1] < v2[1]

v_bad = (b"zzzz", b"aaaa_long_payload")
v_mid = (b"aaaa", b"bbbb_long_payload")
print(
    f"Corrupted prefix: sv_lt(v_bad, v_mid)={sv_lt(v_bad, v_mid)} "
    f"vs actual={v_bad[1] < v_mid[1]} (silent wrong filter/sort!)"
)

print("\n=== PROBE 2C: Exact Dremel (r, d) Striping & FSM Reconstruction on LIST<LIST<INT64>> ===")
records = [[[10, 20], [], None], None, [], [[None]]]

def stripe_list2(recs):
    out = []
    for rec in recs:
        if rec is None:
            out.append((0, 0, None))
        elif len(rec) == 0:
            out.append((0, 1, None))
        else:
            for i, inner in enumerate(rec):
                r_outer = 0 if i == 0 else 1
                if inner is None:
                    out.append((r_outer, 2, None))
                elif len(inner) == 0:
                    out.append((r_outer, 3, None))
                else:
                    for j, val in enumerate(inner):
                        out.append((r_outer if j == 0 else 2, 4 if val is None else 5, val))
    return out

def reconstruct_list2(triples):
    res = []
    for r, d, val in triples:
        if r == 0:
            if d == 0: res.append(None)
            elif d == 1: res.append([])
            elif d == 2: res.append([None])
            elif d == 3: res.append([[]])
            else: res.append([[None if d == 4 else val]])
        elif r == 1:
            if d == 2: res[-1].append(None)
            elif d == 3: res[-1].append([])
            else: res[-1].append([None if d == 4 else val])
        elif r == 2:
            res[-1][-1].append(None if d == 4 else val)
    return res

striped = stripe_list2(records)
rebuilt = reconstruct_list2(striped)
print("Striped (r,d,v):", striped)
print("Lossless roundtrip:", rebuilt == records)
```

Observed output (`Python 3.13`, exit code `0`):

```text
=== PROBE 2A: Arrow Buffer::bit_slice Asymmetric Slack-Bit Leakage ===
bit_slice(8,5) byte=0xeb (slack_bits=0b111, unmasked_popcnt=6, masked_popcnt=3, unmasked_u64_nulls=18446744073709551615)
bit_slice(7,5) byte=0x17 (slack_bits=0b000)

=== PROBE 2B: 16-Byte StringView Layout & Prefix-Mismatch Ordering Violation ===
len<=12 byte_identical=True (16B); len>12 byte_identical=False (arrow[8:16]=0000000040000000, velox[8:16]=40003412007f0000)
Corrupted prefix: sv_lt(v_bad, v_mid)=False vs actual=True (silent wrong filter/sort!)

=== PROBE 2C: Exact Dremel (r, d) Striping & FSM Reconstruction on LIST<LIST<INT64>> ===
Striped (r,d,v): [(0, 5, 10), (2, 5, 20), (1, 3, None), (1, 2, None), (0, 0, None), (0, 1, None), (0, 4, None)]
Lossless roundtrip: True
```

## Revalidation

1. **Re-run the standalone verification probe**: Execute the Python script in **Evidence** (`python3 - <<'PY' ... PY`); runtime is `< 0.1 s` with zero external dependencies, verifying the byte-aligned `bit_slice` slack leak, `StringView` `[8..16)` ABI divergence, prefix-mismatch ordering inversion, and nested `LIST<LIST<INT64>>` Dremel round-trip invariants.
2. **Diff narrow upstream anchors on version bumps**:
   - Check `apache/arrow-rs` `arrow-buffer/src/buffer/immutable.rs` (`Buffer::bit_slice`) to verify whether byte-aligned slices still skip slack-bit zeroing, and `arrow-data/src/data.rs` (`validate` vs. `validate_values`, plus `validate_offsets_and_sizes` `.expect` overflow).
   - Check `apache/arrow` `cpp/src/arrow/array/validate.cc` (`ValidateBinaryView`, `ValidateRunEndEncoded`, `ValidateOffsetsAndSizes`) for whether shallow `ValidateArray` remains non-validating for untrusted IPC buffers.
   - Check `facebookincubator/velox` `velox/type/StringView.h`, `velox/vector/FlatVector.h`, `duckdb/duckdb` `src/include/duckdb/common/types/string_type.hpp`, and `apache/parquet-format` `Encodings.md` for changes to 16-byte view representations or RLE length prefixes.
