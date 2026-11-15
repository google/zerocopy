# CSR Flat `ByteArray` Arenas and Audited `@[extern]` Word-Slice Primitives for `1.0x` Lean-vs-Rust Compiler Substrate Parity

## Summary

Prior unboxed Struct-of-Arrays (SoA) refactoring in
`reports/lean-unboxed-bytearray-bitset-and-soa-compiler-substrate-bridge`
reduced the Lean `v4.34.1` (`5045d0056413`) vs. `rustc 1.99.1` (`58cf8f9c35b3`)
compiler-substrate gap from `4.51x–28.34x` down to `0.49x–1.56x` on four
kernels, but left residual slowdowns on e-graph union-find (`egraph_uf` at
`3.06x` vs. Rust: `15.822 ms` vs. `5.170 ms`), linear-scan register allocation
(`regalloc` at `4.64x` vs. Rust: `1.751 ms` vs. `0.377 ms`), and iterative
dominator trees (`dom_ssa` at `1.56x` vs. Rust: `0.403 ms` vs. `0.259 ms`),
along with an IEEE-754 signaling-NaN canonicalization hazard when packing
arbitrary 64-bit tags into `FloatArray` (`bits 52..62 == 0x7FF`).

This report closes those remaining substrate gaps and eliminates the
`FloatArray` NaN hazard by replacing boxed `Array UInt32` (`lean_array_object`
storing 8-byte `lean_object*` slots with tagged-pointer shifts `v >> 1` and
`(v << 1) | 1`), nested `Array (Array UInt32)` adjacency lists, and
`FloatArray` buffers with **Compressed Sparse Row (CSR) flat `ByteArray`
arenas** (`lean_sarray_object` with 8-byte-aligned `m_data` at byte offset
`24`), paired with a **61-line audited C11 inline word-slice shim
(`anneal_substrate_shim.h`)** and zero-`sorry` Lean `v4.34.1` read-over-write
and CSR equivalence proofs (`ByteWordSlice.lean`, `CSRGraph.lean`). Across all
six canonical compiler-substrate kernels, Lean `v4.34.1` now runs within
**`0.31x–1.20x`** of `rustc 1.99.1 -O3` while reproducing identical 64-bit
deterministic checksums and reducing peak RSS from `44.30 MB` to `32.38 MB`:

| Compiler Kernel | `rustc 1.99.1` (`-O3`, ms) | Idiomatic Lean `v4.34.1` (ms) | Unboxed SoA `Array UInt32` / `FloatArray` (ms) | CSR `ByteArray` Arena + Word-Slice (`K1Bench`, ms) | `K1Bench` P95 (ms) | `K1Bench` / Rust Ratio | Speedup vs. Idiomatic Lean | Speedup vs. Unboxed SoA | Verified 64-Bit Checksum |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `dom_ssa` (`20k` blocks) | `0.259` | `1.261` | `0.403` | **`0.141`** | `0.430` | **`0.54x`** | `8.94x` | `2.86x` | `2621001246` |
| `hashmap_intern` (`500k` syms) | `27.014` | `141.192` | `13.230` | **`8.351`** | `11.247` | **`0.31x`** | `16.91x` | `1.58x` | `3874992250000` |
| `egraph_uf` (`200k` classes) | `5.170` | `44.105` | `15.822` | **`6.188`** | `6.952` | **`1.20x`** | `7.13x` | `2.56x` | `25239800000` |
| `regalloc` (`100k` vregs) | `0.377` | `10.685` | `1.751` | **`0.351`** | `0.380` | **`0.93x`** | `30.47x` | `4.99x` | `7813181233` |
| `inst_encode` (`2M` insts) | `6.390` | `28.792` | `7.445` | **`3.757`** | `4.060` | **`0.59x`** | `7.66x` | `1.98x` | `17000000` |
| `ir_parser` (`500k` lines) | `9.198` | `76.809` | `11.292` | **`9.983`** | `10.021` | **`1.09x`** | `7.69x` | `1.13x` | `2147484415133360` |

## Applicability

These findings apply to:
- **Lean 4:** `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`
  (`v4.34.1`), specifically the LCNF-to-C code generator (`src/Lean/Compiler/LCNF`),
  the C runtime scalar array representation (`lean_sarray_object` in
  `include/lean/lean.h`), and the kernel typechecker (`[propext, Quot.sound]`
  only, zero `sorryAx`, zero `Lean.ofReduceBool`).
- **Rust:** `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`
  (`1.99.1`), compiled with `-C opt-level=3 -C target-cpu=native` on 64-bit
  little-endian Linux (`x86_64-unknown-linux-gnu`).
- **Relationship among subjects:** The report compares native execution speed,
  generated C code structure, memory footprint, and IEEE-754 bit-pattern safety
  of Lean `v4.34.1` compiler passes against `rustc 1.99.1`, and establishes the
  TCB boundary between kernel-checked pure `WordArena`/`CSRGraph` proofs and
  native `leanc -O3` `@[extern]` execution.

## Findings

### 1. Why `Array UInt32` and `FloatArray` Hit an LCNF Ceiling

`Basis: source + execution`

Inspecting `include/lean/lean.h` (`5045d0056413`) and the generated C output
of `X3Bench.c` vs. `K1Bench.c` isolates three structural causes for the
residual slowdowns in `egraph_uf` (`3.06x`), `regalloc` (`4.64x`), and
`dom_ssa` (`1.56x`):

1. **`Array UInt32` (`lean_array_object`) Doubles Cache Footprint and Shifts Every Element:**
   Unlike `ByteArray` (`lean_sarray_object`), Lean `v4.34.1` compiles
   `Array UInt32` as a boxed pointer array (`lean_object* m_data[]`, 8 bytes
   per slot on 64-bit targets). Every `Array.uget` executes
   `lean_unbox_uint32(lean_array_uget(a, i))` (`(size_t)(o) >> 1`), and every
   `Array.uset` executes `lean_box_uint32(v)` (`(lean_object*)(((size_t)(v) << 1) | 1)`)
   after checking `lean_is_exclusive(a)` (`m_rc == 1`). In `egraph_uf`
   (`200,000` e-classes), `Array UInt32` consumes `1.6 MB` (exceeding a
   `1 MB` L2 cache slice) instead of `800 KB` for packed `uint32_t` slots, and
   the two-pass functional `findRoot` + `compressPath` traversal doubles the
   number of random memory loads per `union` operation.
2. **Heap-Allocated `Array UInt32` vs. L1 Register-File Residency in `regalloc`:**
   In linear-scan register allocation (`100,000` virtual registers over `16`
   physical registers), `rustc 1.99.1` keeps `phys_end: [u32; 16]` (`64` bytes,
   one cache line) on the stack and vectorizes the 16-way expiry scan. Using a
   heap `Array UInt32` in Lean executes `lean_is_exclusive` + tagged shifts on
   a 128-byte object-pointer buffer across 1,600,000 inner-loop iterations.
3. **`FloatArray` IEEE-754 NaN Hazard vs. 8-Byte-Aligned `ByteArray` (`lean_sarray_object`):**
   In `include/lean/lean.h`, `lean_sarray_object` has layout:
   ```c
   typedef struct {
       lean_object m_header; // 8 bytes (m_rc: 4B, m_cs_sz: 2B, m_other: 1B, m_tag: 1B)
       size_t      m_size;   // 8 bytes
       size_t      m_capacity; // 8 bytes
       uint8_t     m_data[]; // offset 24 (0x18), 8-byte aligned on 64-bit platforms
   } lean_sarray_object;
   ```
   Because `offsetof(lean_sarray_object, m_data) == 24` (`3 × 8` bytes) and
   `lean_alloc_sarray` returns 8-byte-aligned heap blocks, `lean_sarray_cptr(ba)`
   is unconditionally 8-byte aligned on 64-bit targets. Accessing `ByteArray`
   through `uint32_t*` and `uint64_t*` word slices (`anneal_ba_uget32`/`uset32`
   and `anneal_ba_uget64`/`uset64`) operates on raw integer registers (`GP`)
   without touching the floating-point unit, eliminating IEEE-754 signaling-NaN
   (`0x7FF0000000000001`) canonicalization while running `1.58x` faster than
   `FloatArray` on `hashmap_intern` (`8.351 ms` vs. `13.230 ms`, `0.31x` of
   Rust's `27.014 ms`).

### 2. CSR Graph Arenas, Single-Pass Path Halving, and 64-Byte Register Arenas

`Basis: source + execution`

Refactoring the six compiler kernels in `support/k1_csr_arena/K1Bench.lean`
and `anneal_substrate_shim.h` (`61` code lines) yields:

- **`dom_ssa_csr` (`0.141 ms` vs. `0.403 ms` in SoA and `0.259 ms` in Rust — `0.54x` of Rust):**
  Stores the 2-predecessor CFG (`V = 20,000` blocks, `E = 40,000` edges) in a
  flat `ByteArray` CSR edge table (`csrEdges` at word indices `2*b` and
  `2*b + 1`), and stores the fixed-point `changed` flag in word slot `nU` of
  the `doms` `ByteArray` (`(nU + 1) * 4` bytes), eliminating all `Prod`/`MProd`
  return-pair allocations in `domStep`.
- **`egraph_uf_ba32` (`6.188 ms` vs. `15.822 ms` in SoA and `5.170 ms` in Rust — `1.20x` of Rust):**
  Stores all `200,000` `(rank <<< 24) ||| parent` entries in an `800 KB`
  `ByteArray` (halving the `1.6 MB` `Array UInt32` footprint) and performs
  single-pass path halving (`arr[cur] = (ex & 0xFF000000u) | (arr[p] & 0xFFFFFFu)`),
  cutting median latency by `2.56x`.
- **`regalloc_ba16` (`0.351 ms` vs. `1.751 ms` in SoA and `0.377 ms` in Rust — `0.93x` of Rust):**
  Packs the 16 physical register end-points into a single 64-byte L1
  cache-line `ByteArray` arena (`anneal_ba_regalloc_arena`), achieving a
  `4.99x` speedup over `X3` (`30.47x` over idiomatic Lean) and outperforming
  `rustc 1.99.1` (`0.93x`).
- **`inst_encode_u32` (`3.757 ms` vs. `7.445 ms` in SoA and `6.390 ms` in Rust — `0.59x` of Rust):**
  Replaces four consecutive byte-level `lean_byte_array_set` calls per 4-byte
  instruction with a single 32-bit word store (`baUset32 buf i word32`),
  halving encoding time (`1.98x` speedup).

| Metric | Idiomatic Lean (`K4`) | Unboxed SoA (`X3`) | CSR `ByteArray` + Word-Slice (`K1Bench`) |
| :--- | ---: | ---: | ---: |
| Generated C lines (`K1Bench.c`) | `9,598` | `4,250` | **`3,299`** |
| `lean_alloc_ctor` call sites | `134` | `24` | **`22`** |
| `lean_inc` call sites | `261` | `54` | **`48`** |
| `lean_dec` call sites | `846` | `282` | **`239`** |
| `lean_is_exclusive` call sites | `47` | `11` | **`11`** |
| Peak benchmark RSS (`MB`) | `49.10` | `44.30` | **`32.38`** |

### 3. Kernel-Checked `WordArena` and `CSRGraph` Equivalence Proofs

`Basis: source + execution`

To ensure that `@[extern]` word-slice accessors never weaken the Lean 4 kernel
trust boundary (`TrustedBoundary`), `support/k1_csr_arena/ByteWordSlice.lean`
and `CSRGraph.lean` mechanize pure functional specifications (`WordArena`,
`CSRGraph`, `ValidCSR`, `ufHalvingStep`) and prove with zero `sorry`, zero
`native_decide`, and `[propext, Quot.sound]` only:

- **`WordArena.read_write_same` & `WordArena.read_write_diff`:** Exact
  read-over-write lens laws for flat word arenas;
- **`WordArena.write_write_same` & `WordArena.write_write_comm`:** Overwrite
  idempotence and disjoint-index write commutativity;
- **`nan_payload_preserved_bit_exact`:** Proof that every 64-bit word
  satisfying `isIeee754NaNPattern w = true` (`exponent = 0x7FF`,
  `mantissa ≠ 0`) is preserved bit-for-bit across `WordArena (BitVec 64)`
  writes;
- **`csr_degree_eq_adjLen` & `csr_neighborAt_eq_adjGet`:** Proof that any flat
  `CSRGraph` satisfying `ValidCSR g adjLen adjGet` returns the exact degree and
  $k$-th neighbor of functional adjacency lists;
- **`ufHalvingStep_preserves_root` & `ufHalvingStep_halves_distance`:** Proof
  that single-pass path halving preserves fixed-point union-find roots and
  redirects every child pointer to its grandparent in one step.

## Boundaries

- **Little-endian 64-bit host assumption (`known not to apply` to big-endian targets without byte-swap):**
  Direct `uint32_t*` and `uint64_t*` loads/stores in `anneal_substrate_shim.h`
  assume a 64-bit little-endian host (`x86_64` or `aarch64`) where
  `offsetof(lean_sarray_object, m_data) == 24`. On big-endian targets,
  `__builtin_bswap32` / `__builtin_bswap64` is required to match
  `packU32LE` / `packU64LE`.
- **Single-threaded exclusivity invariant for in-place `@[extern]` arena mutation (`unsupported` for shared multi-owner `ByteArray`s):**
  Functions `anneal_ba_uf_union_mut` and `anneal_ba_regalloc_arena` mutate a
  freshly allocated, function-local `ByteArray` (`baAllocZero`) whose reference
  count is guaranteed to be `m_rc == 1`. Passing a shared (`m_rc > 1`)
  `ByteArray` to a borrowed `@& ByteArray` mutator without calling
  `lean_is_exclusive` is unsupported; general functional updates must use
  `anneal_ba_uset32` / `anneal_ba_uset64`, which check `lean_is_exclusive(ba)`
  and copy on write.

## Evidence

- **Pure Lean `v4.34.1` formalization and proofs (`[propext, Quot.sound]` only):**
  - `support/k1_csr_arena/ByteWordSlice.lean` (`138` lines: `Bytes4`, `Bytes8`,
    `WordArena`, `read_write_same`, `read_write_diff`, `write_write_same`,
    `write_write_comm`, `nan_payload_preserved_bit_exact`).
  - `support/k1_csr_arena/CSRGraph.lean` (`128` lines: `CSRGraph`, `ValidCSR`,
    `csr_degree_eq_adjLen`, `csr_neighborAt_eq_adjGet`,
    `ufHalvingStep_preserves_root`, `ufHalvingStep_halves_distance`).
- **Audited C11 inline word-slice shim and 6-kernel benchmark suite:**
  - `support/k1_csr_arena/anneal_substrate_shim.h` (`70` total lines, `61` code
    lines: `anneal_ba_alloc_zero`, `anneal_ba_uget8`, `anneal_ba_uget32`,
    `anneal_ba_uset32`, `anneal_ba_uget64`, `anneal_ba_uset64`,
    `anneal_ba_uf_find_halving`, `anneal_ba_uf_union_mut`,
    `anneal_ba_regalloc_arena`).
  - `support/k1_csr_arena/K1Bench.lean` (`329` lines: all 6 kernels and 15-run
    monotonic-clock timer).
- **Benchmark runner and recorded telemetry:**
  - `support/run_k1_bench.py` and `support/metrics.json`.

## Revalidation

To revalidate the Lean `v4.34.1` proofs, C-codegen telemetry, and 6-kernel
benchmarks from this package directory:

```bash
python3 support/run_k1_bench.py
```

Check `support/metrics.json` to verify that:
1. `"uses_sorry_or_native_decide"` is `false` and `"axioms"` is
   `["propext", "Quot.sound"]`;
2. Every kernel checksum matches (`dom_ssa = 2621001246`,
   `hashmap_intern = 3874992250000`, `egraph_uf = 25239800000`,
   `regalloc = 7813181233`, `inst_encode = 17000000`,
   `ir_parser = 2147484415133360`);
3. All six `k1_vs_rust_ratio_x` values lie at or below `1.20x`.
