# DuckDB and DataFusion IEEE 754 NaN/-0.0 Grouping, Out-of-Core Radix Spills, and Decimal128 Scale-Widening Joins

## Summary

Modern vectorized analytical query engines—exemplified by `DuckDB`, `Apache DataFusion`, `Polars`, and `Apache Arrow` (`arrow-rs`)—achieve multi-gigabyte-per-second per-core throughput by evaluating morsel-sized columnar batches through SIMD-friendly hash tables, radix-partitioned out-of-core spill managers, and fixed-width 128-bit integer decimal kernels (`Basis: documentation, source`). Across those four engines, four subtle semantic and security hazards arise whenever hardware bit-level representations diverge from relational equivalence classes:

1. **Hash/Equality/Radix-Partition Split-Brain on `IEEE 754` `-0.0` and Multi-Payload `NaN`s (`Basis: normative, source, execution`)**: In `IEEE Std 754-2019`, `+0.0` (`0x0000000000000000`) and `-0.0` (`0x8000000000000000`) compare equal under `==` (`-0.0 == +0.0`) yet differ in bit bit-pattern, while $2^{53}-2$ distinct `f64` bit patterns represent quiet or signaling `NaN`s (`0x7ff8000000000000`, x86 hardware `0.0/0.0` indefinite `0xfff8000000000000`, tagged payloads `0x7ff8000000000042`). Any hash table or radix-partitioned spill operator requires the congruence invariant $\text{eq}(a, b) \implies \text{hash}(a) = \text{hash}(b)$. Raw SIMD `u64` bit-hashing violates this invariant, routing `-0.0` and `+0.0` (or distinct `NaN` payloads) into **disjoint radix spill files** so `HASH JOIN` silently drops matching rows and `GROUP BY` emits duplicate `0.0` or `NaN` groups (`Basis: execution`). Even across mature engines, normalization policies diverge: `DuckDB` (`src/common/types/hash.cpp:33-58`) and `Polars` (`crates/polars-utils/src/total_ord.rs:40-48`) canonicalize both `-0.0 -> +0.0` and all `NaN` payloads to `0x7ff8000000000000`, whereas `DataFusion` (`datafusion/common/src/float_semantics.rs:5-76`) normalizes `-0.0 -> +0.0` for hashing/grouping while **retaining distinct `NaN` payload bits** to match `arrow-rs`'s `f64::total_cmp` (`IEEE 754 totalOrder`) and leaving `-0.0 < +0.0` unnormalized in `ORDER BY` (`Basis: source`).
2. **Three-Valued Logic (`3VL`) Poisoning in `NULL`-Aware `LEFT ANTI JOIN` (`NOT IN`) vs. `ON`-Clause Anti-Joins (`Basis: source, execution`)**: Relational `LEFT ANTI JOIN ... ON p.k = b.k` (`NOT EXISTS`) treats `NULL = anything` as `UNKNOWN` (not matched), so build-side `NULL`s never suppress probe rows. By contrast, SQL `p.k NOT IN (SELECT b.k FROM build)` desugars to `p.k <> b_1 AND p.k <> b_2 AND ...`: a **single** `NULL` anywhere on the build side poisons the conjunction to `UNKNOWN` for every non-matching probe row, requiring the physical operator (`DuckDB` `JoinHashTable::has_null` / `mark_join_info` in `src/execution/join_hashtable.cpp:97, 193-225, 676-685`; `DataFusion` `null_equals_null` / anti-join null-aware flags) to short-circuit to the empty set whenever `build` is non-empty and `build_has_null == true`, yet emit *all* probe rows (including `NULL`s) when `build` is empty (`Basis: source, execution`).
3. **`Decimal128(38, s1) = Decimal128(38, s2)` Scale-Alignment Precision Overflow (`Basis: source, execution, derived`)**: Joining or comparing two `Decimal128` columns of precisions `(p1, s1)` and `(p2, s2)` requires precision $P_{\text{req}} = \max(s_1, s_2) + \max(p_1 - s_1, p_2 - s_2)$ at common scale $S = \max(s_1, s_2)$ (`DataFusion` `datafusion/expr-common/src/type_coercion/binary.rs:1233-1235, 1343-1347`). For `Decimal128(38, 4) = Decimal128(38, 18)`, $P_{\text{req}} = 18 + \max(34, 20) = 52 > 38$ (`DECIMAL128_MAX_PRECISION`). Coercing both inputs to `Decimal128(38, 18)` (`binary.rs:1316-1321`, where `create_decimal128_type` clamps precision to `38`) multiplies the `s=4` operand by $10^{14}$, overflowing signed `i128` ($\max \approx 1.7014 \times 10^{38}$) on valid 34-integer-digit inputs whose mathematical equality result is trivially `false`—requiring promotion to `Decimal256` (`arrow-data/src/decimal.rs:24-45`, `i256` up to $P = 76$) or overflow-free `(quotient, normalized_remainder)` decomposition (`Basis: source, execution`).
4. **Plaintext Multi-Tenant Leakage vs. Authenticated Encryption in Out-of-Core Radix Spill Files (`Basis: source, documentation, execution`)**: Under morsel-driven memory pressure, radix hash joins, grouped aggregations, and external sorts evict intermediate tuples or Arrow IPC `RecordBatch`es to local NVMe scratch directories (`DataFusion` `DiskManager` / `SpillManager` in `datafusion/execution/src/disk_manager.rs:103-160` and `datafusion/physical-plan/src/spill/spill_manager.rs:37-110`; `DuckDB` `StandardBufferManager::WriteTemporaryBuffer` in `src/storage/standard_buffer_manager.cpp:547-689`). Default unencrypted spills write sensitive plaintext rows to OS temporary files (`DiskManagerMode::OsTmpDirectory`), exposing tenant data to post-crash forensics or co-tenant `/tmp` inspection unless protected by per-block `AES-256-GCM` authenticated encryption (`DuckDB` `EncryptTemporaryFiles()` / `EncryptionEngine::EncryptTemporaryBuffer` at `standard_buffer_manager.cpp:547-598, 669-679`) with ephemeral per-query keys zeroized on teardown (`Basis: source, execution`).

## Applicability

This report applies to columnar OLAP engines, DataFrame runtimes, streaming SQL aggregators, financial/ledger join pipelines, and type systems or formal specifications governing equivalence relations, fixed-point arithmetic, and confidential scratch storage (`Basis: derived`).

- **Engine Implementers and Query Optimizers**: Any engine combining vectorized SIMD hashing, radix-partitioned external spilling, sort-merge operators, and rewrite rules (`NOT IN` -> anti-join, decimal cast pushdown) must enforce identical equivalence classes across hash, equality, radix-routing, bloom-filter, and sort-grouping boundaries.
- **Performance and Footprint Hierarchy (`L1`–`L6`)**: Vectorized hash probing, radix scatter, `i128`/`i256` multiplication, and NVMe spill encryption directly govern CPU instruction throughput (`L1`), LLC/TLB radix fan-out (`L2`), memory-pool spill thresholds (`L3`), row vs. columnar tuple layouts (`L4`), NVMe bandwidth (`L5`), and tail-latency OOM resilience (`L6`).
- **Human Comprehensibility and Core-Model Simplicity (`C1`–`C2`)**: Ad-hoc per-operator float normalization, implicit SQL `3VL` null flags, silent decimal precision clamping, and opt-in global spill encryption flags create combinatorial edge cases that collapse cleanly when modeled via explicit equivalence-key traits, null-semantics join algebra, range-checked fixed-point widening, and RAII cryptographic spill capabilities (`Basis: derived`).

## Findings

### 1. Morsel-Driven Radix Partitioning and the `IEEE 754` `-0.0` / `NaN` Split-Brain Trap

#### 1.1 Radix-Partitioned Hash Aggregation and Hash Join Invariants
**Basis: `documentation, source, execution`**

Under morsel-driven parallelism (Leis et al., `DOI: 10.1145/2588555.2593666`, ACM SIGMOD 2014) and `DuckDB`'s vectorized execution engine (Raasveldt & Mühleisen, `DOI: 10.1145/3299869.3320212`, ACM SIGMOD 2019; `src/execution/radix_partitioned_hashtable.cpp:24-90` and `src/execution/join_hashtable.cpp:95-235`), worker threads process fixed-size vectors (typically `2048` tuples in `DuckDB` `STANDARD_VECTOR_SIZE` or `8192` rows in `DataFusion` `HASH_BUFFER`, `datafusion/common/src/hash_utils.rs:104-106`):

1. Each worker computes a 64-bit hash column `hashes[0..N)` over the join or grouping keys (`LogicalType::HASH` stored alongside tuple data at `radix_partitioned_hashtable.cpp:43`).
2. High-order `radix_bits` ($R \in [4, 10]$, yielding $2^R = 16 .. 1024$ partitions) scatter tuples into cache-sized, partition-disjoint buckets—and when memory exceeds `memory_limit`, evict whole radix partitions to temporary disk blocks (`Basis: source, documentation`).
3. During finalize/probe, partition $p$ on the probe side inspects **only** partition $p$ of the build side (plus any published Bloom filter, `join_hashtable.cpp:227-231`), short-circuiting full key comparison whenever stored 64-bit hashes differ.

This architecture relies on a **strict two-tier soundness law** for every key domain $(K, \equiv)$:
$$\forall x, y \in K:\quad x \equiv y \implies \operatorname{hash}_{64}(x) = \operatorname{hash}_{64}(y) \implies \operatorname{radix}_R(x) = \operatorname{radix}_R(y)$$

If $\operatorname{hash}_{64}$ inspects raw 64-bit IEEE 754 words (`u64`) while $\equiv$ implements SQL/DataFrame float grouping:
- `+0.0` (`0x0000000000000000`) and `-0.0` (`0x8000000000000000`) hash to completely uncorrelated 64-bit digests; across a 256-partition ($R=8$) radix spill, $255/256$ (`99.6%`) of hash functions route `-0.0` and `+0.0` to **different spill files**, causing `INNER JOIN` to return `0` rows instead of matching and `GROUP BY` to emit two `0.0` groups (`Basis: execution`).
- Worse, `IEEE 754` `binary64` contains $2 \times (2^{52} - 1) = 9{,}007{,}199{,}254{,}740{,}990$ distinct `NaN` bit patterns (`exponent = 0x7FF`, `mantissa != 0`, sign `0` or `1`). Even within a single process, x86 `0.0 / 0.0` hardware division yields negative quiet `NaN` (`0xfff8000000000000`), Rust `f64::NAN` / C++ `quiet_NaN()` yields positive quiet `NaN` (`0x7ff8000000000000`), and R/Arrow/sensor feeds propagate payload-tagged `NaN`s (`0x7ff8000000000042`). Unnormalized bit-hashing scatters `NaN` rows across up to $2^R$ partitions and creates one `GROUP BY` group per distinct `NaN` bit pattern (`Basis: execution`).

#### 1.2 Divergence Across `DuckDB`, `Polars`, `Arrow-rs`, and `DataFusion`
**Basis: `source, normative`**

Inspecting the four engines at their pinned revisions reveals **three distinct floating-point equivalence contracts**:

| Engine & Exact Source Location | `-0.0` vs. `+0.0` | Distinct `NaN` Payloads (`0x7ff8...01` vs. `0xfff8...00`) | Ordering (`ORDER BY` / `totalOrder`) |
| :--- | :--- | :--- | :--- |
| **`DuckDB`** (`src/common/types/hash.cpp:33-58`) | Equal & identical hash (`if (val == 0.0) val = 0.0;`) | Equal & identical hash (`if (std::isnan(val)) val = quiet_NaN();`) | `NaN` sorts greatest (above `+Inf`), all `NaN`s equal |
| **`Polars`** (`crates/polars-utils/src/total_ord.rs:40-48, 131-160`) | Equal & identical hash (`let convert_zero = x + 0.0;`) | Equal & identical hash (`0x7ff8000000000000` via `canonical_f64`) | `TotalOrdWrap` orders `canonical_f64` consistently |
| **`arrow-rs`** (`arrow-ord/src/cmp.rs`, `f64::total_cmp`) | **Not equal** (`-0.0 < +0.0` per `IEEE 754-2019` §5.10 `totalOrder`) | **Not equal** (`-qNaN < -sNaN < -Inf < ... < +Inf < +sNaN < +qNaN`) | Pure bit-level `IEEE 754 totalOrder` bijection |
| **`DataFusion`** (`datafusion/common/src/float_semantics.rs:5-76`, `hash_utils.rs:250-264`) | Equal & identical hash (`self.to_bits() == 1 << 63` -> `0.0`) | **Distinct!** Comment at `float_semantics.rs:75-76`: *"including NaN payloads, are kept as they are"* | Hybrid: `compare_floats` uses `total_cmp` (`-0.0 < +0.0` in `ORDER BY`, `float_semantics.rs:11-22`)! |

Two critical engineering lessons follow directly from these sources (`Basis: source, derived`):
1. **Cross-Engine Federation Hazard**: Moving a Parquet/Arrow dataset containing `-NaN` (`0xfff8000000000000` from C++/x86 SIMD `0.0/0.0`) and `+NaN` (`0x7ff8000000000000`) between `DuckDB`/`Polars` and `DataFusion` changes `SELECT COUNT(DISTINCT x)` and `GROUP BY x` cardinality because `DataFusion`'s `FloatSemantics::normalize` (`float_semantics.rs:61-63`) canonicalizes only `-0.0` while `DuckDB` and `Polars` canonicalize all `NaN` bit patterns!
2. **Intra-Engine Sort vs. Hash Asymmetry**: As documented in `DataFusion`'s own module header (`float_semantics.rs:11-12, 21-22`), normalizing `-0.0 -> +0.0` in `hash_input` (`hash_utils.rs:256`) while delegating `compare_floats` to unnormalized `self.total_cmp(&other)` (`float_semantics.rs:67`) means `-0.0 == +0.0` under equality/hash-grouping yet `compare_floats(-0.0, +0.0) == Ordering::Less`. Any sort-based grouping, `SortMergeJoin`, or range-partitioned spill that relies on `compare_floats(..) == Ordering::Equal` without calling `normalize_float` first will split `-0.0` and `+0.0` into adjacent distinct runs (`Basis: source, derived`). Note also that Polars's `let convert_zero = x + 0.0;` (`total_ord.rs:42`) relies on IEEE 754 round-to-nearest-even (`RN`, where `-0.0 + +0.0 = +0.0`), whereas under `FE_DOWNWARD` (round toward $-\infty$), `-0.0 + +0.0 = -0.0`! Bitwise masking (`if (bits << 1) == 0 { 0 }`) is immune to FPU rounding modes (`Basis: normative, derived`).

---

### 2. Three-Valued Logic (`3VL`) Traps in `NULL`-Aware `LEFT ANTI JOIN`

**Basis: `source, execution`**

Vectorized SQL engines lower two superficially similar queries onto `JoinHashTable` (`DuckDB` `src/execution/join_hashtable.cpp:95-225, 676-685`; `DataFusion` `datafusion/physical-plan/src/joins/hash_join/exec.rs`):

1. **Relational `LEFT ANTI JOIN` (`NOT EXISTS`)**:
   $$\text{SELECT } p.* \text{ FROM } P \text{ WHERE NOT EXISTS (SELECT 1 FROM } B \text{ WHERE } P.k = B.k\text{)}$$
   Here `WHERE P.k = B.k` filters out `UNKNOWN` before `NOT EXISTS` tests emptiness. Build-side `NULL` rows can never satisfy `P.k = B.k`, so build `NULL`s are harmlessly ignored and probe `NULL` rows are **preserved** in the output.
2. **`NULL`-Aware Anti-Join (`NOT IN` / `MARK` Join)**:
   $$\text{SELECT } p.* \text{ FROM } P \text{ WHERE } P.k \text{ NOT IN (SELECT } B.k \text{ FROM } B\text{)}$$
   Per ISO SQL three-valued logic, $x \notin \{b_1, \dots, b_m\}$ is $\bigwedge_{i=1}^m (x \neq b_i)$, evaluated in `WHERE` (which keeps only `TRUE`, discarding both `FALSE` and `UNKNOWN`):
   - **Case A ($B = \emptyset$)**: The empty conjunction is vacuously `TRUE` for **every** row of $P$, *including* rows where $P.k \text{ IS NULL}$ (`Basis: execution`).
   - **Case B ($B \neq \emptyset \land \exists b \in B.\; b \text{ IS NULL}$)**: For every probe row $x$, either $x = b_j$ (`FALSE`) or $x \neq \text{NULL}$ (`UNKNOWN`). The entire query **must return 0 rows** (`Basis: execution`).
   - **Case C ($B \neq \emptyset \land \forall b \in B.\; b \text{ IS NOT NULL}$)**: Any probe row with $P.k \text{ IS NULL}$ evaluates $P.k \neq b_1$ to `UNKNOWN` and is **discarded**, whereas non-null probe rows not in $B$ return `TRUE`.

In `DuckDB` (`src/execution/join_hashtable.cpp:97, 216, 676-685`), `JoinHashTable` tracks `bool has_null` across parallel thread-local build tables and merges it atomically under `mj_lock` (`has_null = has_null || other.has_null;` at `line 216`, and `info.uncorrelated_has_null` at `line 222`). A subtle distributed/partitioned radix-join bug occurs if an engine radix-partitions $P$ and $B$ by `hash(k)` and evaluates `NULL`-aware anti-join *independently per partition*: `NULL` build rows hash to a single partition $p^*$ (`DataFusion` `hash_utils.rs:211` hashes nulls with constant seed `1`), leaving partitions $p \neq p^*$ unaware that `build_has_null == true` so those `255` partitions erroneously emit non-empty results! **`build_has_null` and `build_is_empty` are global barrier reductions across all build partitions before any probe partition emits a single tuple (`Basis: source, derived`)**.

---

### 3. `Decimal128(P, s)` Cross-Scale Join Overflow and `i256` / Quotient-Remainder Exactness

#### 3.1 Why Common-Scale `i128` Coercion Overflows on Valid `Decimal128` Inputs
**Basis: `source, execution`**

In `Apache Arrow` (`apache/arrow-rs` @ `9f87453338091a0cf078300f01b8eb0a84a99f10`, `arrow-data/src/decimal.rs:18-45`), `Decimal128(p, s)` stores fixed-point values $v \cdot 10^{-s}$ as signed two's-complement 128-bit integers (`i128`) with maximum precision `DECIMAL128_MAX_PRECISION = 38` ($10^{38} - 1 < 2^{127} - 1 \approx 1.7014 \times 10^{38}$), while `Decimal256(p, s)` uses signed 256-bit `i256` up to `DECIMAL256_MAX_PRECISION = 76` ($10^{76} - 1 < 2^{255} - 1 \approx 5.7896 \times 10^{76}$).

Consider an equality join or predicate between a macro-ledger balance column `L: Decimal128(38, 4)` (up to $34$ integer digits, $4$ fractional digits) and a per-unit micro-rate or token column `R: Decimal128(38, 18)` (up to $20$ integer digits, $18$ fractional digits):
- Representing all values of both columns losslessly at a single common scale $S = \max(s_1, s_2) = 18$ requires integer digits $\max(p_1 - s_1, p_2 - s_2) = \max(34, 20) = 34$, hence total precision:
  $$P_{\text{req}} = \max(s_1, s_2) + \max(p_1 - s_1, p_2 - s_2) = 18 + 34 = 52 > 38$$
- In `apache/datafusion` (`657d2cab48a5c3586fcfcb1bec416c333de9e966`, `datafusion/expr-common/src/type_coercion/binary.rs:1316-1322`), `get_wider_decimal_type` matches `(Decimal128(p1, s1), Decimal128(p2, s2))` and calls `create_decimal128_type(required_decimal_precision(*p1, *s1, *p2, *s2), s)`, which **clamps the target type to `Decimal128(38, 18)`** rather than widening homogeneous `Decimal128` inputs to `Decimal256(52, 18)` (cross-variant widening in `get_wider_decimal_type_cross_variant` at `binary.rs:1256-1260` triggers only when one side is *already* `Decimal256`!).
- Even inside `required_decimal_precision` (`binary.rs:1337-1347`), DataFusion's comment explicitly records a prior integer-overflow bug: computing `(p1 - s1) + s` in `i8` panicked in debug builds (`attempt to add with overflow`) when negative scales caused `p1 - s1` to exceed `127`, requiring widening the precision metadata calculation itself to `i32` (`Basis: source`)!

When `L` contains a completely legal 34-integer-digit `Decimal128(38, 4)` row (e.g., $1.2345 \times 10^{33}$, stored as $v_1 \approx 1.2345 \times 10^{37} < 10^{38}$), casting `L` to `Decimal128(38, 18)` multiplies $v_1 \times 10^{14} \approx 1.2345 \times 10^{51} \gg \text{i128::MAX}$, **aborting the entire `SELECT ... JOIN` query with a cast overflow error (`ArrowError::CastError`) even though no `Decimal128(38, 18)` value (bounded by $< 10^{20}$) could possibly equal $1.2345 \times 10^{33}$ (`Basis: source, execution`)!**

#### 3.2 Two Sound Solutions: `Decimal256` Widening ($P_{\text{req}} \le 76$) and `(Quotient, Remainder)` Canonical Keys
**Basis: `derived, execution`**

1. **Automatic Variant Promotion to `Decimal256`**: Whenever $38 < P_{\text{req}} \le 76$, widening both join keys to `Decimal256(P_req, max(s1, s2))` (`i256`) makes $v_1 \times 10^{s_2 - s_1}$ exact without overflow. However, note that if $s_1 = 0$ on `Decimal128(38, 0)` and $s_2 = 38$ on `Decimal128(38, 38)`, $P_{\text{req}} = 38 + 38 = 76$ hits the exact ceiling of `Decimal256`; and for `Decimal256(76, 0) = Decimal256(76, 38)`, $P_{\text{req}} = 114 > 76$ exceeds even `Decimal256`!
2. **Universal Overflow-Free `(IntPart, NormFrac)` Decomposition (Exact for All $0 \le s \le 38$ in `i128 × i128`)**:
   Every `Decimal128(p, s)` with $0 \le s \le 38$ decomposes uniquely via Euclidean/truncating division by $10^s$ into:
   $$q = \operatorname{trunc}(v / 10^s) \in (-10^{38}, 10^{38}), \qquad r_{\text{norm}} = (v - q \cdot 10^s) \cdot 10^{38 - s} \in (-10^{38}, 10^{38})$$
   Because $|v - q \cdot 10^s| < 10^s$, $|r_{\text{norm}}| < 10^s \cdot 10^{38 - s} = 10^{38} < 2^{127}$ **never overflows `i128` for any scale $s \in [0, 38]$**! Two decimals across *any* scales $(s_1, s_2)$ are mathematically equal if and only if $(q_1, r_{\text{norm},1}) = (q_2, r_{\text{norm},2})$, providing **both** an overflow-free equality predicate **and** a scale-invariant canonical hash key $\operatorname{hash}(q, r_{\text{norm}})$ without ever failing on out-of-overlap rows (`Basis: derived, execution`). Alternatively, range-pruning rows where $|v_1| \ge 10^{38 - s_2}$ on `INNER JOIN` (since they can never match any `Decimal128(38, s2)` row, though `LEFT JOIN` must emit them with `NULL` right columns rather than dropping or crashing!) avoids `i256` arithmetic on the fast path (`Basis: derived`).

---

### 4. Out-of-Core Radix Spill Confidentiality and Authenticated Block Encryption

**Basis: `source, documentation, execution`**

When a multi-tenant analytical service (embedded `DuckDB` worker pool or `DataFusion` Ballista/FlightSQL cluster) executes a memory-intensive `HASH JOIN`, `GROUP BY`, or `ORDER BY`, spilling moves live intermediate relational tuples onto shared NVMe volumes:

- **`DataFusion` (`datafusion/execution/src/disk_manager.rs:44-160`, `datafusion/physical-plan/src/spill/spill_manager.rs:37-110`)**: Defaults to `DiskManagerMode::OsTmpDirectory` (`disk_manager.rs:47, 152-153`) with a `100 GiB` quota (`DEFAULT_MAX_TEMP_DIRECTORY_SIZE`, `line 21`) and optional LZ4/ZSTD `SpillCompression` (`spill_manager.rs:34`), writing unencrypted Arrow IPC streams unless an embedder injects a custom `Arc<dyn TempFileFactory>` via `DiskManagerBuilder::with_temp_file_factory` (`disk_manager.rs:69-81`). Compression *never* substitutes for encryption—in fact, compression ratios over attacker-controlled join payloads can leak crime-style side-channel structure if untagged.
- **`DuckDB` (`src/storage/standard_buffer_manager.cpp:547-689`)**: Provides `StandardBufferManager::EncryptTemporaryFiles()` (`Settings::Get<TempFileEncryptionSetting>(db)`, `line 548`). When enabled, `WriteTemporaryBuffer` (`lines 572-598`) reserves `DEFAULT_ENCRYPTED_BUFFER_HEADER_SIZE` bytes for per-block nonce + authentication tag metadata and encrypts each evicted buffer via `EncryptionEngine::EncryptTemporaryBuffer` (`AES-GCM`), while `ReadTemporaryBuffer` (`lines 647-679`) validates block header bounds against actual file size (`lines 652-661`) before calling `EncryptionEngine::DecryptTemporaryBuffer`. However, unless `SET temp_file_encryption = true` (or encrypted database propagation) is active, evicted `.block` files land on `temp_directory` in plaintext (`Basis: source, documentation`).

A hardened spill subsystem must enforce three cryptographic invariants (`Basis: derived, execution`):
1. **Ephemeral Per-Query Key + Deterministic Monotonic Nonce**: Generate a fresh CSPRNG 256-bit key $K_q$ per query execution context in non-swappable memory (`mlock`/zeroize-on-drop), and construct each 96-bit `AES-256-GCM` (or `ChaCha20-Poly1305`) nonce from `(spill_file_id: u32, monotonic_block_seq: u64)` so 96-bit nonce reuse is structurally impossible without random-IV birthday bounds.
2. **Context-Bound `AAD` Against Cross-Partition Replay**: Authenticate `(query_id, operator_id, partition_id, block_seq, uncompressed_byte_len)` as Additional Authenticated Data (`AAD`), preventing a local attacker with `/tmp` write access from swapping spill block `B_3` of tenant A with block `B_7` or truncating trailing spill batches.
3. **Cryptographic Erasure on Cancellation / Panic**: Zeroize $K_q$ synchronously in `Drop` when a query completes, fails, or cancels; even if `unlink`ed NVMe flash pages linger prior to SSD wear-leveling garbage collection, all spilled tuples become computationally indistinguishable from random bits.

---

### 5. Multi-Level Performance/Footprint (`L1`–`L6`) and Comprehensibility/Simplicity (`C1`–`C2`) Analysis

#### 5.1 `L1`–`L6` Hardware-Software Performance and Footprint Matrix
**Basis: `source, documentation, derived`**

| Level | Subsystem Dimension | Vectorized Fast-Path Mechanism & Cost | Spill / Widening / Misconfiguration Penalty |
| :--- | :--- | :--- | :--- |
| **`L1`** | CPU Pipeline & SIMD Vectorization | Branchless float bit normalization (`(bits << 1) == 0` mask + `NaN` blend, ~2–3 SIMD ops/vector) + vectorized `MurmurHash64` / `foldhash` (`hash.cpp:45-58`, `hash_utils.rs:30`) at ~0.5–1.5 ns/tuple; AES-NI / VAES encrypts spill blocks at `8–20+ GB/s` per core (<3% CPU overhead relative to NVMe I/O). | Software `i256` division or per-row dynamic `ScalarValue` boxing adds 10x–30x ALU overhead; scalar `std::isnan` branches with high `NaN` entropy incur branch-misprediction penalties (~15 cycles). |
| **`L2`** | Cache Hierarchy (`L1d`/`L2`/`LLC`) & TLB | Radix fan-out $2^R$ (`R = 6..8`, `64–256` partitions) keeps scatter write-combining buffers inside `L1d`/`L2` and fits each finalized partition's hash directory inside `L2`/`L3` without random LLC/TLB thrashing (Leis et al. SIGMOD 2014). | Excessive single-pass radix fan-out ($R \ge 11$, `>2048` active write streams) exceeds hardware TLB entries (~64–128 `L1 dTLB` pages) and cache-line write buffers, degrading scatter throughput by 4x–8x; engines must use 2-pass radix partitioning above `R = 8`. |
| **`L3`** | Buffer Pool, Thread-Local Reuse & Allocator | `DataFusion` reuses a `64 KiB` thread-local `HASH_BUFFER` (`8192 × u64`) capped at `4 MiB` (`MAX_BUFFER_SIZE = 524,288`, `hash_utils.rs:99-107`) to prevent allocator churn and unbounded high-water-mark retention. | Slicing a `RecordBatch` to 10 rows while retaining an `Arc` to an `8 MiB` backing Arrow buffer inflates spill memory accounting (`spill_manager.rs:103-105` explicitly warns callers to pass *non-sliced* batches!). |
| **`L4`** | Tuple / Columnar Layout & Width | `DuckDB` `TupleDataLayout` (`radix_partitioned_hashtable.cpp:42-48`) packs normalized keys + precomputed `LogicalType::HASH` (`8 B`) contiguously in row-major blocks so probe hash-mismatch skips pointer chasing; `Decimal128` uses `16 B`/value vs. `32 B`/value for `Decimal256`. | Unconditionally widening all `Decimal128` columns to `Decimal256` doubles key memory footprint (`16 B -> 32 B`), halving effective hash-table capacity before out-of-core spill triggers. |
| **`L5`** | NVMe I/O Amplification & Compression | `DuckDB` writes `>= 256 KiB` (`DEFAULT_BLOCK_ALLOC_SIZE`, `standard_buffer_manager.cpp:553`) sequential `.block` extents; `LZ4`/`ZSTD` spill compression (`SpillManager::compression`) cuts NVMe read+write amplification by 2x–5x before `AES-GCM` encryption. | Small unbuffered `4 KiB` spill writes saturate NVMe IOPS limits well below sequential PCIe Gen4/Gen5 bandwidth (`7–14 GB/s`). |
| **`L6`** | Tail Latency, Disk Quotas & Multi-Tenancy | Atomic `used_disk_space` reservation against `max_temp_directory_size` (`disk_manager.rs:108-110`, `maximum_swap_space` in `standard_buffer_manager.cpp:86, 581`) bounds noisy-neighbor disk exhaustion deterministically. | Unbounded or unencrypted `/tmp` spills cause node-wide disk-full cascades or silent post-query PII persistence on shared cloud hosts. |

#### 5.2 `C1`–`C2` Human Comprehensibility and Conceptual Simplicity Synthesis
**Basis: `derived, source`**

- **`C1` Cognitive Load Diagnosis (Why Query Engines Accumulate Subtle Bugs Here)**:
  1. *Implicitly Coupled Trait Triples (`Eq`, `Hash`, `Ord`)*: Standard-library `f64` omits `Eq`/`Hash`/`Ord` because `NaN != NaN`, tempting engine authors to slap `.to_bits()` onto hashers in one module while calling `total_cmp` in sorting and `==` in filter pushdown—silently breaking the relational equivalence law across operators.
  2. *Overloaded Join Enums*: Representing `NOT IN` and `LEFT ANTI JOIN ... ON` as a single `JoinType::Anti` with boolean side-flags (`null_equals_null`, `mark_join`, `null_aware`) scatters SQL `3VL` invariants across planner, partitioner, and hash-probe loops.
  3. *Conflating Storage Type with Comparison Algebra*: Treating `Decimal128(38, 4) = Decimal128(38, 18)` as *"cast both sides to one common storage type, then run homogeneous `eq`"* manufactures a synthetic precision overflow (`52 > 38`) that does not exist in mathematical rational comparison.
- **`C2` Minimal Orthogonal Core Abstractions**:
  Four small, composable invariants eliminate all four bug classes by construction:
  1. **Single Sealed `CanonicalKey` Projection (`normalize -> bytes`)**: Define every grouping, hash-join, radix-partition, Bloom-filter, and sort-grouping operator over a single canonical key wrapper (`SqlFloatKey` collapsing `-0.0 -> +0.0` and `is_nan -> CANON_QNAN`, distinct from `IeeeTotalOrderKey` used only when strict bit-level `totalOrder` is explicitly requested). Hashing, equality, and ordering derive exclusively from the normalized representation, making hash/equality/radix/sort split-brain unrepresentable.
  2. **Explicit `AntiJoinSemantics::NullIgnored | NullPoisoned3VL` Sum Type**: Require `NullPoisoned3VL` to consume a globally reduced `BuildNullSummary { is_empty: bool, has_null: bool }` token before constructing any partitioned probe cursor.
  3. **Heterogeneous Fixed-Point Comparison Kernel**: Dispatch `decimal_eq_and_hash(Decimal128(p1, s1), Decimal128(p2, s2))` to common-scale `i128` when $P_{\text{req}} \le 38$, `i256` when $38 < P_{\text{req}} \le 76$, and `(q, r_norm)` otherwise—never mutating or overflowing input storage columns via lossy/clamped cast coercion.
  4. **Type-Enforced `EncryptedSpillPool` Capability**: Make `SpillWriter` constructible only from a `QueryCryptoContext` holding an ephemeral `Zeroizing<[u8; 32]>` AEAD key and atomic `(partition_id, block_seq)` nonce generator, so plaintext disk writes cannot occur by omission.

## Boundaries

- **`not examined`**: Distributed shuffle network transport (`Apache Arrow Flight` TLS framing, Spark/Comet shuffle service blocks) and GPU OLAP hash tables (`cuDF` / `Velox` GPU kernels) were **not examined**; this report focuses on single-node vectorized CPU execution and local temporary disk spilling.
- **`unknown`**: Exact wall-clock break-even thresholds between `i256` multiplication vs. `i128` Euclidean `divmod` (`(q, r_norm)`) across ARM64 Neoverse V2 vs. x86-64 Zen 5 microarchitectures for skewed `Decimal128` hash-join keys remain **unknown** without target-specific microbenchmarks.
- **`known not to apply`**: Canonicalizing all `NaN` bit patterns to `0x7ff8000000000000` is **known not to apply** when implementing strict `IEEE Std 754-2019` §5.10 `totalOrder` predicates (such as `arrow-rs` `arrow-ord` bit-level `total_cmp` when diagnostic `NaN` payloads intentionally carry distinct missing-value tags, e.g., R `NA` `0x7ff80000000007a2` vs. IEEE `NaN`). Engines supporting tagged missingness must promote `NA` to Arrow's validity bitmap (`NULL`) at ingestion rather than relying on `NaN` payload preservation through SQL operators.
- **`unsupported`**: Losslessly storing the union of `Decimal128(38, 4)` and `Decimal128(38, 18)` inside any `Decimal128(p, s)` column (`p <= 38`) is mathematically **unsupported** ($P_{\text{req}} = 52 > 38$); materialized `UNION ALL` or arithmetic projections (`L + R`) must either widen the output schema to `Decimal256(52, 18)` or document precision-loss rounding rules.

## Evidence

1. **`DuckDB` Canonical Float Hashing, Radix Hash Tables, `MARK`/`ANTI` Null Tracking, and Spill Encryption (`Basis: source`)**:
   - Repository: `https://github.com/duckdb/duckdb` @ `05de6cb973b60b102849d155bf1665e208bad7fa`
   - `src/common/types/hash.cpp:32-58`: `FloatingPointEqualityTransform<T>::OP` canonicalizes `-0.0` to `+0.0` (`if (val == (T)0.0) val = (T)0.0;`) and all `NaN`s to `std::numeric_limits<T>::quiet_NaN()` prior to `MurmurHash64` bit-hashing.
   - `src/execution/radix_partitioned_hashtable.cpp:24-90`: Appends `LogicalType::HASH` to `TupleDataLayout` and partitions grouped aggregation state across `radix_bits`.
   - `src/execution/join_hashtable.cpp:95-225, 676-685`: Tracks `has_null` and `mark_join_info.uncorrelated_has_null` across merged thread-local hash tables to enforce SQL `NOT IN` / `MARK` join 3VL semantics.
   - `src/storage/standard_buffer_manager.cpp:547-689`: `EncryptTemporaryFiles()` (`TempFileEncryptionSetting`), `WriteTemporaryBuffer` (`EncryptionEngine::EncryptTemporaryBuffer` + `DEFAULT_ENCRYPTED_BUFFER_HEADER_SIZE`), and header-validated `ReadTemporaryBuffer` (`EncryptionEngine::DecryptTemporaryBuffer`).
2. **`Apache DataFusion` Float Semantics, Thread-Local Hash Buffers, Decimal Coercion, and Spill Manager (`Basis: source`)**:
   - Repository: `https://github.com/apache/datafusion` @ `657d2cab48a5c3586fcfcb1bec416c333de9e966`
   - `datafusion/common/src/float_semantics.rs:5-76`: Documents `DataFusion`'s `-0.0 -> 0.0` normalization (`self.to_bits() == 1 << (<$bits>::BITS - 1)`), explicit preservation of `NaN` payload bits (`lines 74-76`), and unnormalized `total_cmp` ordering (`lines 11-22, 66-68`).
   - `datafusion/common/src/hash_utils.rs:81, 99-107, 210-217, 250-264`: Hashes `hash_input(*self).to_bits()` via `foldhash`, hashes nulls to constant seed `1`, and bounds thread-local `HASH_BUFFER` at `MAX_BUFFER_SIZE = 524_288`.
   - `datafusion/expr-common/src/type_coercion/binary.rs:1211-1347`: Implements `get_wider_decimal_type_cross_variant`, `get_wider_decimal_type` (clamping homogeneous `(Decimal128, Decimal128)` via `create_decimal128_type` at `lines 1316-1321`), and `i32`-widened `required_decimal_precision` (`max(s1, s2) + max(p1 - s1, p2 - s2)` at `lines 1343-1347`).
   - `datafusion/execution/src/disk_manager.rs:21-160` & `datafusion/physical-plan/src/spill/spill_manager.rs:31-110`: Implements `DiskManagerMode::OsTmpDirectory` (`100 GiB` cap), `TempFileFactory` custom spill hook, and `SpillManager` batch spilling.
3. **`Polars` and `Apache Arrow` (`arrow-rs`) Canonical Ordering and Decimal Bounds (`Basis: source`)**:
   - `https://github.com/pola-rs/polars` @ `e02c237a6b9055f23f33ae632b0490286a579e2e`: `crates/polars-utils/src/total_ord.rs:14-160` (`canonical_f16`/`f32`/`f64` mapping `-0.0` to `+0.0` and `NaN` to `0x7ff8000000000000`, wrapped by `TotalOrdWrap<T>` implementing `Eq`, `Ord`, and `TotalHash`).
   - `https://github.com/apache/arrow-rs` @ `9f87453338091a0cf078300f01b8eb0a84a99f10`: `arrow-data/src/decimal.rs:14-75` (`DECIMAL128_MAX_PRECISION = 38`, `DECIMAL256_MAX_PRECISION = 76`, `i256` precision bounds) and `arrow-ord/src/cmp.rs` (`total_cmp` float kernels).
4. **Peer-Reviewed Literature and Standards (`Basis: normative, documentation`)**:
   - Mark Raasveldt and Hannes Mühleisen, *DuckDB: An Embeddable Analytical Database*, ACM SIGMOD 2019 (`DOI: 10.1145/3299869.3320212`).
   - Viktor Leis, Peter Boncz, Thomas Neumann, and Alfons Kemper, *Morsel-Driven Parallelism: A NUMA-Aware Query Evaluation Framework for the Many-Core Age*, ACM SIGMOD 2014 (`DOI: 10.1145/2588555.2593666`).
   - *IEEE Standard for Floating-Point Arithmetic*, `IEEE Std 754-2019`, §5.10 (`totalOrder` and `totalOrderMag` predicates) and §6.2 (`NaN` payload propagation).
5. **Executable Verification Probe (`Basis: execution`)**:
   The standalone Python 3 probe below reproduces 256-way radix-spill partition divergence under raw `u64` float bit-hashing vs. SQL canonicalization and `IEEE 754 totalOrder`, verifies `NOT IN` vs. `ON` anti-join 3VL semantics, proves `Decimal128(38, 4) == Decimal128(38, 18)` `i128` rescaling overflow vs. exact `(quotient, normalized_remainder)` equality, and verifies `AES-256-GCM` authenticated spill block encryption + key zeroization:

```python
import math
import os
import struct
from cryptography.hazmat.primitives.ciphers.aead import AESGCM


def f64_to_u64(x: float) -> int:
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def splitmix64(x: int) -> int:
    x = (x + 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
    x = ((x ^ (x >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
    x = ((x ^ (x >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
    return (x ^ (x >> 31)) & 0xFFFFFFFFFFFFFFFF


def canonical_f64_bits_sql(bits: int) -> int:
    if (bits << 1) & 0xFFFFFFFFFFFFFFFF == 0:
        return 0x0000000000000000
    exp = (bits >> 52) & 0x7FF
    mant = bits & ((1 << 52) - 1)
    if exp == 0x7FF and mant != 0:
        return 0x7FF8000000000000
    return bits


def ieee754_total_order_key(bits: int) -> int:
    return ((~bits) & 0xFFFFFFFFFFFFFFFF) if (bits >> 63) else (bits ^ (1 << 63))


POS_ZERO = 0x0000000000000000
NEG_ZERO = 0x8000000000000000
QNAN_STD = 0x7FF8000000000000
QNAN_NEG = 0xFFF8000000000000
QNAN_PAY = 0x7FF8000000000042

# Raw bit-hashing scatters equal SQL keys into disjoint 256-way radix spill partitions:
assert (splitmix64(POS_ZERO) >> 56) != (splitmix64(NEG_ZERO) >> 56)
assert len({splitmix64(b) >> 56 for b in (QNAN_STD, QNAN_NEG, QNAN_PAY)}) == 3

# Canonicalized SQL hashing maps +/-0.0 and all NaN bit patterns consistently:
assert (splitmix64(canonical_f64_bits_sql(POS_ZERO)) >> 56) == (
    splitmix64(canonical_f64_bits_sql(NEG_ZERO)) >> 56
)
assert len({splitmix64(canonical_f64_bits_sql(b)) >> 56 for b in (QNAN_STD, QNAN_NEG, QNAN_PAY)}) == 1

assert (
    ieee754_total_order_key(QNAN_NEG)
    < ieee754_total_order_key(f64_to_u64(-math.inf))
    < ieee754_total_order_key(NEG_ZERO)
    < ieee754_total_order_key(POS_ZERO)
    < ieee754_total_order_key(f64_to_u64(math.inf))
    < ieee754_total_order_key(QNAN_STD)
    < ieee754_total_order_key(QNAN_PAY)
)


# 3VL NULL-aware anti-join (`NOT IN`) vs ON-clause anti-join (`NOT EXISTS`)
def sql_not_in_anti_join(probe: list[int | None], build: list[int | None]) -> list[int | None]:
    if not build:
        return list(probe)
    if any(b is None for b in build):
        return []
    non_null = {b for b in build if b is not None}
    return [x for x in probe if x is not None and x not in non_null]


def sql_on_anti_join(probe: list[int | None], build: list[int | None]) -> list[int | None]:
    non_null = {b for b in build if b is not None}
    return [x for x in probe if x is None or x not in non_null]


assert sql_not_in_anti_join([1, 2, None], [2, None]) == []
assert sql_on_anti_join([1, 2, None], [2, None]) == [1, None]
assert sql_not_in_anti_join([1, None], []) == [1, None]

# Decimal128(38, 4) == Decimal128(38, 18) overflow vs exact (quotient, norm_rem)
I128_MAX = (1 << 127) - 1
I128_MIN = -(1 << 127)


def naive_i128_decimal_eq(v1: int, s1: int, v2: int, s2: int) -> bool | str:
    scaled = v1 * (10 ** (s2 - s1)) if s1 < s2 else v2 * (10 ** (s1 - s2))
    if not (I128_MIN <= scaled <= I128_MAX):
        return "OVERFLOW"
    return (scaled == v2) if s1 < s2 else (v1 == scaled)


def exact_quot_rem_decimal_eq(v1: int, s1: int, v2: int, s2: int) -> bool:
    def split_dec(v: int, s: int) -> tuple[int, int]:
        scale = 10 ** s
        q, r = divmod(abs(v), scale)
        if v < 0:
            q, r = -q, -r
        return (q, r * (10 ** (38 - s)))

    return split_dec(v1, s1) == split_dec(v2, s2)


val_s4 = 1234567890123456789012345678901234 * 10000 + 1234
val_s18 = 99999999999999999999 * (10 ** 18)
assert val_s4 <= I128_MAX and val_s18 <= I128_MAX
assert naive_i128_decimal_eq(val_s4, 4, val_s18, 18) == "OVERFLOW"
assert exact_quot_rem_decimal_eq(val_s4, 4, val_s18, 18) is False
assert exact_quot_rem_decimal_eq(425000, 4, 42500000000000000000, 18) is True
assert exact_quot_rem_decimal_eq(-425000, 4, -42500000000000000000, 18) is True

# Per-query AES-256-GCM spill block encryption + cryptographic erasure
key = bytearray(os.urandom(32))
aead = AESGCM(bytes(key))
nonce = struct.pack("<QI", (7 << 16) | 19, 0)
aad = struct.pack("<QII", 7, 19, 0)
pt = b"SSN=123-45-6789|SALARY=245000.00"
ct = aead.encrypt(nonce, pt, aad)
assert b"123-45-6789" not in ct and aead.decrypt(nonce, ct, aad) == pt
for i in range(len(key)):
    key[i] = 0
assert all(b == 0 for b in key)
```

## Revalidation

Revalidate this package when any of the following change (`Basis: derived`):

1. **`DataFusion` Float Normalization and Decimal Coercion Updates**:
   - Inspect `datafusion/common/src/float_semantics.rs` (`FloatSemantics::normalize`, `compare_floats`) to check whether `DataFusion` unifies `ORDER BY` (`compare_floats`) with `-0.0 -> +0.0` normalization or adopts `NaN` payload canonicalization matching `DuckDB` and `Polars`.
   - Inspect `datafusion/expr-common/src/type_coercion/binary.rs` (`get_wider_decimal_type`) to check whether homogeneous `(Decimal128(p1, s1), Decimal128(p2, s2))` comparisons with $P_{\text{req}} > 38$ are automatically promoted to `Decimal256(P_req, max(s1, s2))`.
2. **`DuckDB` and `DataFusion` Out-of-Core Spill Encryption Defaults**:
   - Re-check `duckdb/src/storage/standard_buffer_manager.cpp` (`EncryptTemporaryFiles`) and `datafusion/execution/src/disk_manager.rs` (`DiskManagerBuilder` / `TempFileFactory`) if default temporary spill encryption or built-in AEAD spill writers land upstream.
3. **Automated Executable Check**:
   - Extract and run the Python 3 verification script in `## Evidence` (`python3 -c ...`), confirming zero assertion failures across 256-way radix-spill float partitioning, 3VL `NOT IN` vs. `ON` anti-joins, `Decimal128(38, s)` scale-alignment edge cases, and `AES-256-GCM` spill encryption.
