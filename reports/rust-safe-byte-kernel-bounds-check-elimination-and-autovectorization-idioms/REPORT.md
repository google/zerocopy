# Safe Rust Byte-Kernel Bounds-Check Elimination, Auto-Vectorization Idioms, and Hot-Path Outlining

## Summary

Evaluating safe `#![forbid(unsafe_code)]` Rust byte-processing idioms against
`rustc 1.102.0-nightly` (`3ef0c22cdb86`) and LLVM `23.1.5` on `x86-64` Ice Lake
(`-C opt-level=3 -C target-cpu=icelake-client`) isolates five concrete compiler
mechanisms separating scalar fallback code from bounds-check-free SIMD loops:

1. **Dynamic slice subranges destroy LLVM SLP vectorization (`2.28x` throughput drop):**
   In 4-lane Adler-32 checksum loops (`support/safe_bce_and_llvm_probe.rs`),
   reindexing the shared slice directly via `&bytes[i..]` (`adler_while_varindex4`)
   retains `4` bounds-check panics inside the body, spills `8` slots to
   `%rsp`, emits `0` vector `vpaddd` instructions, and runs at `2,479.9 MB/s`
   — nearly tied with serial scalar code (`1,664.9 MB/s` unaligned / `2,364.8
   MB/s` on 2 MiB). Reslicing a fixed `5552`-byte chunk and slicing a `[u8; 4]`
   window (`&chunk[i..i + 4]` or `chunks_exact(4)`) eliminates all `4` panic
   checks, triggers `9` `vpaddd` SIMD lanes (`0` spills), and accelerates
   throughput to `5,660.8 MB/s` (`5,228.9 MB/s` for `chunks_exact(4)`).
2. **Typed fixed-size containers (`[T; N]`, `Box<[T; N]>`, `as_chunks::<N>`) erase masked index checks:**
   Masking an index into a dynamic `&[u32]` (`tbl[k & 2047]`, `bce_slice_mask`)
   leaves a runtime bounds panic in LLVM assembly because slice length is a
   runtime value. Changing only the signature to `&[u32; 2048]` or
   `&Box<[u32; 2048]>` eliminates `100%` of bounds panics and unlocks `17`
   vector `%ymm` register operations. Similarly, `s.as_chunks::<4>()` (`72`
   insns, `0` panics) and `s.chunks_exact(4)` (`80` insns, `0` panics) both
   drop the `4` panic calls and reduce total instruction count by `2.0x–2.2x`
   below `while i + 4 <= s.len()` (`159` insns, `4` panics).
3. **Hot-loop cold outlining (`#[cold]`, `#[inline(never)]`) and `split_at_mut` shrink inflate fast-paths by `2.64x`:**
   On real DEFLATE fast-loop code (`decode_block_fast`), moving rare error and
   refill recovery behind `#[cold] #[inline(never)]` helpers, locking 16-byte
   lookahead windows to `&[u8; 16]`, and isolating output writes via `split_at_mut`
   cuts emitted assembly from `872` lines (`780` instructions, `23` panic calls,
   `117` `%rsp` stack references) down to `348` lines (`296` instructions, `0`
   bounds/slice panics, `36` `%rsp` references).
4. **Zipped slice iteration triggers AVX2 `vpminuq` DP relaxation (`dp_relax_zipped`):**
   Rewriting dynamic-programming edge relaxation as
   `dp[3..=hi].iter_mut().zip(&len_hi[3..=hi])` hoists slice range checks
   before the loop and compiles the inner relaxation into a 4-way unrolled AVX2
   vector loop (`79` insns total, `5` `vpaddq` + `5` `vpminuq` `ymm` ops, `0`
   stack spills). Meanwhile, double-literal decoding (`loop_safe_double_lit`:
   `109` insns, `1` `%rsp` spill) increases hot-loop instruction count and
   spilling relative to branchless unsafe pointer writes (`loop_unsafe_lit`: `72`
   insns, `0` panics, `0` spills), narrowing safe-vs-unsafe headroom when
   branch and bounds checks double inside inner literal loops.
5. **Linux `glibc` `mmap_threshold` zeroing asymmetry (`calloc` vs. incremental `Vec::resize`):**
   Above `glibc`'s `mmap_threshold` (`> 128 KiB`), `vec![0u8; 4 * 1024 * 1024]`
   routes through `calloc`/anonymous `mmap` with kernel demand-zero pages
   (`146.9 us` touching endpoints), whereas growing a small buffer via
   `Vec::with_capacity(1024)` + `.resize(4 MiB, 0)` pays eager `realloc` copies
   and `memset` page faults (`570.8 us`, `3.89x` slower).

---

## Applicability

These measurements apply to:

- **Compiler & target:** `rustc 1.102.0-nightly` (`3ef0c22cdb86`) / LLVM
  `23.1.5` targeting `x86-64` Ice Lake (`-C opt-level=3 -C target-cpu=icelake-client`).
- **Safe Rust hot kernels:** Applies to checksum loops, match-hash lookups,
  chain-walking matchfinders, Huffman fast-decode loops, and dynamic-programming
  cost relaxations under `#![forbid(unsafe_code)]`.
- **Complementary scope boundaries:** Cross-core wide-SIMD `AVX-512` width
  tradeoffs (`+prefer-256-bit` vs. `-prefer-256-bit`), L1/L2/L3 cache bandwidth
  walls, `vpdpbusd` multi-stream scaling, `MaybeUninit` Miri rules, and Lean 4
  lane overflow bounds are documented separately in
  [`x86-64-adler32-simd-lane-overflow-bounds-and-avx512-codegen-width`](../x86-64-adler32-simd-lane-overflow-bounds-and-avx512-codegen-width/REPORT.md).

---

## Findings

### 1. Bounds-Check Elimination and Auto-Vectorization in Safe Slice Kernels

`Basis: execution`

Compiling [`support/safe_bce_and_llvm_probe.rs`](support/safe_bce_and_llvm_probe.rs)
at `-C opt-level=3 -C target-cpu=icelake-client --emit=asm` quantifies how LLVM
`23.1.5` responds to syntactic slice proofs:

| Kernel Function (`safe_bce_and_llvm_probe.rs`) | Total Insns | Bounds Panics | `%rsp` Spills | `%ymm` Refs | Key Vector Ops | Observed Effect |
| :--- | :---: | :---: | :---: | :---: | :--- | :--- |
| `bce_while_index4` (`while i+4 <= s.len()`) | `159` | `4` | `0` | `125` | `10` `vpaddd`, `2` `vpminuq` | Retains 4 panic edges |
| `bce_chunks_exact4` (`chunks_exact(4)`) | `80` | **`0`** | `0` | `21` | `14` `vpaddd` | Cleanly vectorizes (`0` panics) |
| `bce_as_chunks4` (`as_chunks::<4>()`) | **`72`** | **`0`** | `0` | `21` | `14` `vpaddd` | Shortest zero-panic vector loop |
| `bce_slice_mask` (`&[u32]`, `k & 2047`) | `20` | `1` | `0` | `0` | `—` | Dynamic slice length preserves panic edge |
| `bce_box_array_mask` (`&Box<[u32; 2048]>`) | `93` | **`0`** | `0` | `17` | Vectorized gather/load | Type-level `2048` eliminates bounds panic |
| `bce_ref_array_mask` (`&[u32; 2048]`) | `92` | **`0`** | `0` | `17` | Vectorized gather/load | Identical zero-panic vectorization |
| `bce_shifted_read4` (`win = &s[..pos+4]`) | `122` | `5` | `0` | `0` | `—` | Loop condition `c < pos` alone cannot eliminate `win[c + 3]` unless `c` upper-bounds `c + 4` |
| `bce_first_chunk4` (`s.get(c..)?.first_chunk::<4>()`) | `139` | **`0`** | `0` | `48` | `7` `vpaddd` | Eliminates panics at higher `%ymm`/unroll footprint (`139` vs. `122` insns) |
| `dp_relax_zipped` (`dp[3..=hi].iter_mut().zip(...)`) | `79` | `3` *(entry only)* | **`0`** | `26` | **`5` `vpaddq`, `5` `vpminuq`** | Entry slice check hoists `0`-panic 4x AVX2 loop |

#### 1.1 Four-Way Adler-32 SLP Isolation (`2,479.9` vs. `5,660.8 MB/s`)

Benchmarking four implementations computing the identical checksum over `1 MiB`
pinned to core `4` (`taskset -c 4`) isolates bounds-check interference from
loop dependency structure:

| Implementation | Inner Indexing Idiom | Panic Calls | `%rsp` Spills | `vpaddd` SIMD Ops | Throughput (`1 MiB`, `taskset -c 4`) |
| :--- | :--- | :---: | :---: | :---: | :---: |
| `adler_serial_while` | Scalar `a += data[i]; b += a;` | `0` | `0` | `0` | `1,664.9 MB/s` |
| `adler_while_varindex4` | `bytes[i], ..., bytes[i+3]` on full slice | **`4`** | **`8`** | **`0`** (blocked!) | **`2,479.9 MB/s`** |
| `adler_chunks_exact_4lane` | `chunk.chunks_exact(4)` (`adler2`-style) | **`0`** | `0` | **`9`** | `5,228.9 MB/s` |
| `adler_while_fixed4` | `let chunk = &bytes[pos..pos+5552]; let s = &chunk[i..i+4];` | **`0`** | `0` | **`9`** | **`5,660.8 MB/s`** |

When LLVM sees variable offset additions (`i + 1`, `i + 2`, `i + 3`) checked
against a variable `bytes.len()` and an inner exit condition, LLVM retains four
separate panic edges (`panics = 4`) and refuses to pack the 4 lanes into
`vpaddd`, leaving throughput near scalar speed (`2,479.9 MB/s`). Isolating a
fixed `5552`-byte chunk and reslicing `&chunk[i..i + 4]` (or `chunks_exact(4)`)
collapses all four checks into one slice check per `4` bytes, restoring SLP
vectorization (`+2.28x` faster than `varindex4`).

---

### 2. Chain-Walk Matchfinders, Safe Prefilters, and Outlined Fast Inflate

`Basis: source + execution`

1. **Shifted slice views vs. `first_chunk` in hash-chain matchfinders:**
   Inside `chain_shifted_views` (`safe_bce_and_llvm_probe.rs`), pre-slicing
   `src_win = &src[..pos + 3]` and `end_slice = &src[best_len - 1..pos + best_len + 1]`
   produces `102` instructions and `2` `%rsp` spills, compared to `94`
   instructions and `3` `%rsp` spills for repeated `first_chunk::<2>()` /
   `first_chunk::<4>()` probes (`chain_subslice_first_chunk`). On full crate
   builds (`chain_walk_best`), indexing `&[u16; 32768]` with `cand & 32767`
   keeps table lookups bounds-check-free while remaining inner slice reads still
   account for `10` `slice_index_fail` cold paths across `411–412` instructions
   and `61–63` `%rsp` references.
2. **1-byte vs. 4-byte candidate prefilters (`prefilter_1b_safe` vs. `prefilter_4b_safe`):**
   Testing a 4-byte tail signature before matching the 4-byte head (`prefilter_4b_safe`:
   `65` instructions, `3` panics, `0` spills) compiles shorter and cleaner than
   checking one tail byte followed by a 4-byte slice comparison (`prefilter_1b_safe`:
   `73` instructions, `3` panics, `0` spills), while requiring an explicit
   `c + best_len + 1 <= src.len()` bound to avoid out-of-bounds panics.
3. **Cold outlining and fixed lookahead in fast DEFLATE decoding:**
   Inspecting compiled `x86-64` assembly across inflate fast-loop refactors
   establishes the effect of moving `Err` paths out of the hot loop via
   `#[cold] #[inline(never)]`, binding lookahead to `&[u8; 16]`, and writing
   through `out_buf.split_at_mut(out_pos)`: total emitted assembly for
   `decode_block_fast` drops from `872` lines (`780` instructions, `23` panic calls
   across `9` `slice_index_fail` + `14` `panic_bounds_check`, `117` `%rsp` refs)
   to `348` lines (`296` instructions, **`0` bounds/slice panics**, `36` `%rsp` refs).
4. **Safe vs. unsafe double-literal fusion (`loop_unsafe_lit` vs. `loop_safe_double_lit`):**
   Evaluating single-literal vs. double-literal Huffman table decoding on `1 MiB`:
   - `loop_unsafe_lit`: `72` instructions, `0` panics, `0` `%rsp` spills (`347.5
     MB/s` single-literal -> `594.8 MB/s` double-literal, `+71.2%` on synthetic
     high-hit literal traffic using branchless 16-bit unaligned writes).
   - `loop_safe_single_lit` -> `loop_safe_double_lit`: grows from `87` insns (`0`
     spills, `346.6 MB/s`) to **`109` insns (`+1` `%rsp` spill, `557.9 MB/s`)**
     because safe slice indexing cannot emit an unconditionally `dist = 1/2`-width
     unaligned store (`write_unaligned::<u16>`) without branching `(e & DBL_FLAG) != 0`
     into two separate `dst[d_idx]` / `dst[d_idx + 1]` writes—explaining why
     branch-heavy full decode loops can regress under double-literal fusion in safe
     Rust while gaining throughput in unsafe pointer loops.

---

### 3. `glibc` `mmap_threshold` Zeroing Asymmetry (`calloc` vs. `Vec::resize`)

`Basis: execution`

In `safe_bce_and_llvm_probe.rs`, allocating a `4 MiB` zeroed buffer via `vec![0u8;
4 * 1024 * 1024]` and touching its first and last bytes completes in **`146.9 us`**
(median of `15` runs), whereas starting from `Vec::with_capacity(1024)` and
calling `.resize(4 * 1024 * 1024, 0)` takes **`570.8 us`** (`3.89x` slower). Above
glibc's `mmap_threshold` (`> 128 KiB`), `vec![0u8; n]` lowers to `__rust_alloc_zeroed`
-> `calloc`, returning kernel demand-zero anonymous `mmap` pages without eager
memory stores; incremental `resize` after a smaller allocation must `realloc`
and explicitly zero-fill every byte synchronously.

---

## Boundaries

- **Target and toolchain specificity:** Instruction, spill, and SIMD vector
  counts reflect `rustc 1.102.0-nightly` / LLVM `23.1.5` on `-C
  target-cpu=icelake-client`. Earlier LLVM versions or non-AVX2 targets emit
  different unroll factors and scalar fallback patterns.
- **Standalone vs. whole-codec loop interaction:** While `loop_safe_double_lit`
  gains on the isolated synthetic literal stream in `safe_bce_and_llvm_probe.rs`,
  in full `decode_block_fast` state machines where match/refill arms share
  registers, adding that branch and `%rsp` spill degrades safe inflate throughput
  relative to single-literal tables.
- **`decode_block_fast` full-crate assembly metrics (`872 -> 348` lines):** Measured
  from compiled `.s` outputs on full inflate crates; standalone
  [`support/safe_bce_and_llvm_probe.rs`](support/safe_bce_and_llvm_probe.rs)
  directly verifies the `bce_*`, `prefilter_*`, `dp_relax_zipped`, `adler_*`,
  `loop_*`, `chain_*`, and `4 MiB` `calloc` vs. `resize` checks.

---

## Evidence

### 1. Primary Upstream Sources Examined

- **`rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `1.102.0-nightly`) & bundled LLVM `23.1.5`:**
  Directly inspected `-C opt-level=3 -C target-cpu=icelake-client --emit=asm` outputs.
- **`oyvindln/adler2` (`89a031a0f42eeff31c70dc598cbf31f1680f`, `2.0.1`) and `Frommi/miniz_oxide` (`4e582392df3a739d2b0dfd2c537dc33e8942be38`, `0.9.1`):**
  Baseline 4-lane `chunks_exact(4)` pattern and DEFLATE kernel structure.

### 2. Preserved Package Support Artifacts

- [`support/safe_bce_and_llvm_probe.rs`](support/safe_bce_and_llvm_probe.rs):
  Self-contained Rust benchmark and codegen suite covering BCE patterns,
  4-way Adler-32 SLP isolation, `dp_relax_zipped`, `prefilter_{1b,4b}_safe`,
  `chain_{shifted_views,subslice_first_chunk}`, `loop_{unsafe,safe_single,safe_double}_lit`,
  and `4 MiB` `vec![0u8; N]` vs. `resize` latency.
- [`support/verify_bce_asm_and_bench.py`](support/verify_bce_asm_and_bench.py):
  Automated harness compiling assembly (`--emit=asm`), asserting exact panic /
  spill / SIMD vector instruction invariants, and running pinned `taskset -c 4`
  throughput checks.

---

## Revalidation

Run the verification script on `x86_64` with AVX2/AVX-512 support (Ice Lake or
newer recommended for identical vectorization):

```console
python3 reports/rust-safe-byte-kernel-bounds-check-elimination-and-autovectorization-idioms/support/verify_bce_asm_and_bench.py
```

The command must exit `0` with `"status": "PASS"`, observing `0` panics on
`bce_chunks_exact4`, `bce_as_chunks4`, `bce_box_array_mask`,
`bce_ref_array_mask`, and `adler_while_fixed4`, AVX2 `vpminuq`/`vpaddq` in
`dp_relax_zipped`, `vpaddd == 0` in `adler_while_varindex4`, and `> 1.5x`
throughput advantage for `adler_while_fixed4` over `adler_while_varindex4` and
`adler_serial_while`.
