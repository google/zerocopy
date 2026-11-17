# x86-64 Ice Lake Streaming Checksums, Adler-32 Lane-Overflow Bounds, AVX-512 Width Selection, and `MaybeUninit` Overlap Rules

## Summary

Evaluating wide SIMD checksums, overlap string copies, and bit-reader
unpacking on `x86-64` Ice Lake (`rustc 1.102.0-nightly` / LLVM `23.1.5`) while
mechanizing lane arithmetic in Lean `v4.34.1` and aliasing rules under Miri
establishes five hardware and soundness boundaries:

1. **Ice Lake `+prefer-256-bit` defaults cap safe 64-lane checksums to `%ymm` unless `-prefer-256-bit` is passed:**
   Under `-C target-cpu=icelake-client`, LLVM defaults to `+prefer-256-bit`,
   emitting `908` `%ymm` references and `0` `%zmm` registers for safe
   64-lane `u16 -> u32` `adler_safe_64lane_u16_16` (`34.30 GB/s` at `32 KiB L1`,
   `35.61 GB/s` at `256 KiB L2`, and `16` IFMA52 `vpmadd52` ops in weight
   reduction). Disabling `+prefer-256-bit` unlocks `514` `%zmm` registers and
   lifts safe 64-lane throughput to **`48.69 GB/s` (`+42%`) in L1** and **`50.97
   GB/s` (`+43%`) in L2**, before both hit the **`~30 GB/s` L3/memory wall** at `2
   MiB` (`30.07–30.16 GB/s`).
2. **Multi-stream AVX-512 VNNI (`vpdpbusd` + `vpsadbw`) scales to `88.99 GB/s` in L1 yet saturates at `2 MiB`:**
   Explicit `avx512vnni` accumulation breaks scalar chain latency across `k = 1,
   2, 4` independent streams (`40.87 -> 76.86 -> 88.99 GB/s` at `32 KiB L1`;
   `39.22 -> 44.36 -> 49.82 GB/s` at `256 KiB L2`), whereas at `2 MiB L3` all
   three collapse onto `29.97–31.17 GB/s`, making `L3` DRAM/LLC bandwidth mask
   even a `2.25x` L1 arithmetic speedup over `+prefer-256-bit` safe code.
3. **Mechanized Lean 4 lane-overflow bounds and the signed `_mm512_reduce_add_epi32` wrap hazard:**
   `support/AdlerSimdOverflowBounds.lean` proves without `sorry` that:
   - Classic scalar `NMAX = 5552` keeps unreduced `s2 <= 4,294,690,200 < 2^32`
     while `5553` overflows (`adlerMaxB 5553 = 4,296,171,735`);
   - In source-ordered `u16` super-block lanes (`K = 16`), exact values satisfy
     `s1 <= 4,080` and `s2 <= 30,600 <= 65,535`, with true `u16` overflow first
     occurring at `K = 24` (`70,380` vs. crude quadratic `255*K^2` cutoff `K = 16`);
   - In 2-stream AVX-512 VNNI (`2048` 128-byte blocks), `vpsadbw` accumulates
     `8`-byte sums in `u64` lanes (`<= 4,276,101,120`) while `vpdpbusd`
     accumulates `4` weighted bytes per `u32` lane (`63,750` max/block ->
     `130,560,000 < 2^31`);
   - Using `_mm512_reduce_add_epi32(v_s2) as u64` over `5552` `0xFF` blocks
     triggers silent **32-bit signed sign-extension** when the lane total exceeds
     `i32::MAX`, corrupting `0xfc06e4fb` to `0xfb25e4fb`.
4. **Miri `MaybeUninit<u8>` bounds on wild-copy lookback vs. SSSE3 `pshufb` overlap smearing:**
   Under `cargo miri`, an unaligned `u64` lookback read at `out_pos - dist` is
   defined iff `dist >= 8`; at `dist = 4`, straddling initialized `[0..out_pos)`
   and uninitialized `[out_pos..)` fails Miri with `Undefined Behavior:
   encountered uninitialized memory`. For short distances `1 <= dist < 16`, once
   `out_pos >= 16`, loading strictly initialized `[out_pos - 16..out_pos)` and
   applying a precomputed SSSE3 `_mm_shuffle_epi8` period-smearing mask copies
   all `16` overlapping bytes cleanly across all `dist ∈ 1..=15` with zero Miri UB.
5. **Zero-ALU variable shifts (`BMI2` `shrx`/`bzhi`):**
   Combining variable table bit-shift advances `(bb >> (e & 63))` and bitmask
   extractions `bb & ((1 << extra) - 1)` compiles under `-C target-cpu=icelake-client`
   directly to `5` `shrx` and `5` `bzhi` instructions with zero register `cl` moves
   or shift-mask shifts (`bmi2_shrx_bzhi`).

---

## Applicability

These findings govern:

- **Compiler/target tuning on `x86-64` Intel Ice Lake+:** Applicable to `rustc
  1.102.0-nightly` / LLVM `23.1.5` targeting `-C target-cpu=icelake-client` or
  `avx512bw`/`avx512vnni`/`avx512ifma`/`bmi2`/`ssse3`. Contrast with short-loop
  512-bit profitability pitfalls (`1–16` byte loops) documented in
  [`x86-avx512-short-loop-regression-and-vector-width-profitability`](../x86-avx512-short-loop-regression-and-vector-width-profitability/REPORT.md).
- **Unsafe `MaybeUninit<u8>` inflate/LZ77 decoders:** Applies to any `unsafe`
  slice decoder maintaining live `[0..out_pos)` invariants checked under Miri.
- **Delayed-modulo `Adler-32` implementations:** Directly validates constants in
  `oyvindln/adler2` (`2.0.1`) and custom `u16 -> u32` or `AVX-512` VNNI kernels.

---

## Findings

### 1. AVX-512 Width Policy (`+prefer-256-bit` vs. `-prefer-256-bit`) and Ice Lake Cache Tiers

`Basis: execution`

Measuring [`support/adler32_vnni_and_bmi2_probe.rs`](support/adler32_vnni_and_bmi2_probe.rs)
pinned to core `4` (`taskset -c 4`) across L1-resident (`32 KiB`), L2-resident
(`256 KiB`), and L3/DRAM-backed (`2 MiB`) buffers reveals why vector-width gains
depend on cache tier:

| Working Set | Variant / Flag Policy | Safe 64-Lane Reg Usage (`ymm` / `zmm`) | Serial (`GB/s`) | Safe 64-Lane `u16 -> u32` (`GB/s`) | VNNI `k=1` (`GB/s`) | VNNI `k=2` (`GB/s`) | VNNI `k=4` (`GB/s`) |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **`32 KiB` (L1d)** | Default (`+prefer-256-bit`) | `908` / **`0`** | `3.21` | `34.30` | `40.87` | `76.86` | **`88.99`** |
| **`32 KiB` (L1d)** | `-C target-feature=-prefer-256-bit` | `52` / **`514`** | `3.21` | **`48.69` (`+42.0%`)** | `40.92` | `77.99` | `88.14` |
| **`256 KiB` (L2)** | Default (`+prefer-256-bit`) | `908` / `0` | `3.22` | `35.61` | `39.22` | `44.36` | **`49.82`** |
| **`256 KiB` (L2)** | `-C target-feature=-prefer-256-bit` | `52` / `514` | `3.21` | **`50.97` (`+43.1%`)** | `39.24` | `44.27` | `49.68` |
| **`2 MiB` (L3)** | Default (`+prefer-256-bit`) | `908` / `0` | `3.21` | `30.16` | `30.11` | `29.97` | **`30.44`** |
| **`2 MiB` (L3)** | `-C target-feature=-prefer-256-bit` | `52` / `514` | `3.20` | `30.07` | `28.67` | `28.48` | `29.10` |

Three hardware takeaways follow directly:
1. **Default `+prefer-256-bit` suppresses `%zmm` auto-vectorization:** LLVM keeps
   pure safe `u16 -> u32` inner loops at 256 bits (`908` `%ymm` refs, `0` `%zmm`).
   Even trailing `s1_32`/`s2_32` reductions (`adler_reduce_weights_only`) emit
   `16` AVX-512 IFMA52 `vpmadd52` instructions in `ymm` mode (`8` under `%zmm`).
2. **Accumulator ILP (`k=1 -> 2 -> 4`) breaks VNNI dependency latency in L1:**
   Because `_mm512_dpbusd_epi32` has 5-cycle Ice Lake latency on a single vector
   chain, advancing from `1` accumulator (`40.87 GB/s`) to `2` (`76.86 GB/s`,
   `+88%`) and `4` (`88.99 GB/s`, `+2.18x`) saturates L1 fetch ports.
3. **L3 cache/memory bandwidth equalizes wide SIMD at `2 MiB`:** At `2 MiB`,
   safe 64-lane `u16 -> u32` (`30.16 GB/s`) matches 4-stream VNNI (`30.44 GB/s`).
   Only inputs chunked inside L1/L2 (such as DEFLATE's `NMAX = 5552` bytes or
   inline deflate blocks) realize the `50–89 GB/s` arithmetic ceiling.

---

### 2. Formal Adler-32 Overflow Ceilings and the `_mm512_reduce_add_epi32` Sign Bug

`Basis: formal + execution`

All lane-width arithmetic invariants are proved without `sorry` in
[`support/AdlerSimdOverflowBounds.lean`](support/AdlerSimdOverflowBounds.lean):

| Regime / Formula | Verified Exact Threshold (`AdlerSimdOverflowBounds.lean`) | First Overflow Point / Contrast |
| :--- | :--- | :--- |
| **Delayed modulo homomorphism** | `adlerFold_delayed_correct`: `(a, b) mod 65521` commutes across chunk steps | Eliminates `% 65521` inside inner loops via `adlerReduceU32Nat_exact` (`2^16 ≡ 15 mod 65521`, valid for all `v < 2^32`) |
| **Scalar `NMAX = 5552` (`u32`)** | `adlerMaxB 5552 = 4,294,690,200 < 2^32` (`347 * 16 = 5552`) | `adlerMaxB 5553 = 4,296,171,735 >= 2^32` |
| **Nested `u16` super-block (`K = 16`)** | Source order (`s2 += s1; s1 += b`): `s1 <= 4,080`, `s2 <= 30,600 <= 65,535` | Crude quadratic bound `255*K^2` holds at `K = 16` (`65,280 <= 65,535 < 255*17^2`); exact worst case first overflows `u16` at **`K = 24`** (`70,380` vs. `64,515` at `K = 23`) |
| **AVX-512 `vpsadbw` (`u64`) + `vpdpbusd` (`u32`) (`N = 2048` × `128 B`)** | `vpsadbw` accumulates `8`-byte sums (`2,040`/vec -> prefix `<= 4,276,101,120 < 2^32`); `vpdpbusd` adds `4` weighted bytes (`255*(64+63+62+61) = 63,750`/vec -> `2048 * 63,750 = 130,560,000 < 2^31`, safe up to `33,686` vectors before `2^31`) | Unreproducible heuristic constant `4,275,969,680` matches neither `1020*2048^2` (`4,278,190,080`) nor `2040*2048*2047/2` (`4,276,101,120`) and is not divisible by `255` |

**Concrete `i32` sign-extension hazard (`adler_unsafe_vnni_signed_bug`):**
Intel's `_mm512_reduce_add_epi32(v_s2)` intrinsic has Rust return type `i32`, not
`u32`. Accumulating `5552` `64`-byte vectors of `0xFF` leaves an unsigned total
above `2^31` whose horizontal `i32` sum is negative. Casting `_mm512_reduce_add_epi32(v_s2)
as u64` performs `i32 -> i64 -> u64` sign extension (`0xFFFF_FFFF_...`), corrupting
the Adler-32 output from **`0xfc06e4fb`** to **`0xfb25e4fb`**. Splitting `dot`
via `_mm512_cvtepu32_epi64` and reducing with `_mm512_reduce_add_epi64` zero-extends
every 32-bit lane and matches `adler_serial_1lane` bit-for-bit (`0xfc06e4fb`).

---

### 3. Miri `MaybeUninit<u8>` Lookback Rules, SSSE3 `pshufb` Period Smearing, and BMI2 Shifts

`Basis: execution`

1. **`MaybeUninit<u8>` overlap lookback boundary (`support/miri_uninit_straddle_probe.rs`):**
   Running `cargo +nightly miri test` over a `[MaybeUninit<u8>; 64]` slice whose
   live initialized prefix is `[0..out_pos)`:
   - **`ok_dist8_initialized` (`dist = 8`, `out_pos = 12`):** Passes Miri cleanly
     (`out_pos - 8 = 4`, reading bytes `[4..12) ⊂ [0..12)`).
   - **`ub_dist4_straddles_uninit` (`dist = 4`, `out_pos = 12`):** Rejected by
     Miri with `error: Undefined Behavior: constructing invalid value of type
     std::ptr::Unaligned<u64>: at .0, encountered uninitialized memory` because
     the 8-byte read spans bytes `[8..16)`, touching uninitialized `[12..16)`.
   - **`ok_period_16b_dist3` (`out_pos >= 16`, `1 <= dist < 16`):** Passes Miri
     cleanly by copying strictly inside initialized `[out_pos - 16 .. out_pos)`
     without reading ahead of `out_pos`.
2. **SSSE3 `pshufb` overlap smearing (`pshufb_smear_16`):**
   Using `_mm_shuffle_epi8(src, mask)` with `mask[i] = 16 - dist + (i % dist)`
   on `[out_pos - 16 .. out_pos)` produces exact byte-by-byte LZ77 overlap
   output across all `15` short distances `dist = 1..=15` (`PSHUFB_1_TO_15=PASS`)
   while reading strictly initialized prefix memory.
3. **BMI2 zero-ALU bitfield ops (`bmi2_shrx_bzhi`):**
   Variable shifts `(bb >> (e & 63))` paired with variable-width masking `(bb as
   u32) & ((1 << extra) - 1)` emit `5` `shrx` and `5` `bzhi` instructions on Ice
   Lake, replacing `mov ecx` + `shr`/`shl`/`dec`/`and` sequences in Huffman bit
   readers.

---

## Boundaries

- **CPU microarchitecture scope:** Benchmarks and `prefer-256-bit` defaults
  reflect `x86-64` Intel Ice Lake (`-C target-cpu=icelake-client`). Server
  Skylake-X / Emerald Rapids cores or AMD Zen 4/5 exhibit different L1/L2 port
  ratios and AVX-512 frequency-licensing behavior.
- **Unaligned write validity under Miri:** `ok_dist8_initialized` and
  `ok_period_16b_dist3` assume `out_pos + width <= buf.len()` slack is allocated
  in `[out_pos .. buf.len())` as valid `MaybeUninit<u8>` bytes.

---

## Evidence

### 1. Primary Upstream Sources Examined

- **`rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `1.102.0-nightly`) & LLVM `23.1.5`:**
  Directly assembled and executed on Ice Lake with `+prefer-256-bit` and `-prefer-256-bit`.
- **`oyvindln/adler2` (`89a031a0f42eeff31c70dc598cbf31f1680f`, `2.0.1`):**
  Baseline `NMAX = 5552` delayed-modulo design.

### 2. Preserved Package Support Artifacts

- [`support/AdlerSimdOverflowBounds.lean`](support/AdlerSimdOverflowBounds.lean):
  Standalone Lean `v4.34.1` proofs of delayed-modulo equivalence, `5552` scalar
  ceiling, nested `u16` `K = 16` exact & `K = 24` overflow thresholds, division-free
  `adlerReduceU32Nat_exact`, and `vpsadbw`/`vpdpbusd` ceilings.
- [`support/adler32_vnni_and_bmi2_probe.rs`](support/adler32_vnni_and_bmi2_probe.rs):
  Benchmarks L1/L2/L3 cache tiers, `k = 1, 2, 4` VNNI streams, `+prefer-256-bit`
  vs. `-prefer-256-bit`, `vpmadd52`, `_mm512_reduce_add_epi32` `i32` wrap bug,
  SSSE3 `pshufb` `1..=15`, and BMI2 `shrx`/`bzhi`.
- [`support/miri_uninit_straddle_probe.rs`](support/miri_uninit_straddle_probe.rs):
  `MaybeUninit<u8>` overlap aliasing probes verified with `cargo +nightly miri test`.
- [`support/verify_simd_and_miri.py`](support/verify_simd_and_miri.py):
  Master verification runner executing Lean, both Rust width profiles, and both
  passing and failing Miri tests.

---

## Revalidation

Run the combined Lean + Ice Lake SIMD + Miri verification suite:

```console
python3 reports/x86-64-adler32-simd-lane-overflow-bounds-and-avx512-codegen-width/support/verify_simd_and_miri.py
```

The command must exit `0` with `"status": "PASS"`, confirming empty Lean proof
output, `%zmm == 0` vs. `%zmm > 0` under `+prefer-256-bit` vs. `-prefer-256-bit`,
`expected=0xfc06e4fb` vs. `signed_bug=0xfb25e4fb`, `PSHUFB_1_TO_15=PASS`,
`shrx`/`bzhi` & `vpmadd52` emission, `2 passed` under Miri, and Miri rejection
of `ub_dist4_straddles_uninit`.
