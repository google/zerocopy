<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Compression Benchmarking Methodology and Rust vs. Lean 4 Pareto Analysis

## Summary

Comparing DEFLATE codecs across languages requires controlling three frequent
measurement distortions: aggregate vs. geometric-mean file weighting, pointwise
level-by-level comparisons vs. the true time-sharing Pareto hull, and length-only
round-trip assertions that miss silent byte corruption. Under quiet single-core
benchmarking (`taskset -c 4`, 2 MiB raw-DEFLATE Silesia slices across all 9
levels), Safe and Unsafe Rust match-and-DP designs strictly dominate Lean 4
`lean-zip` (`2f7a63f`) along the convex speed-ratio hull (`1.84x` to `7.85x`
faster at matched ratio on levels 8-9), even where deeper Unsafe L7-L8 levels
trade pointwise throughput for tighter compression.

## Applicability

- Head-to-head throughput and compression-ratio benchmarking across C (`zlib
  1.3.2`), Lean 4 (`lean-zip`), and Safe/Unsafe Rust DEFLATE/INFLATE engines.
- Interpreting geometric-mean vs. byte-weighted aggregate ratios over the
  12-file Silesia corpus (`211,938,580` total bytes, pinned by SHA-256).
- Auditing compiled Lean 4 C intermediate code (`lean_is_exclusive`, boxed
  `Nat` ops, and `bv_decide` certificate elimination via LTO/`--gc-sections`).

## Findings

### Benchmark Methodology Traps

1. **Corpus Integrity and Prefix Truncation Sensitivity:** The canonical 12-file
   Silesia corpus totals `211,938,580` bytes (pinned via individual SHA-256
   digests). Measuring 2 MiB prefixes isolates per-file algorithm speed on the
   same working set (`756` raw-DEFLATE measurements across 7 codecs x 12 files x
   9 levels), whereas `>4 MiB` inputs cross adaptive dispatch thresholds in
   `lean-zip` (for example, `Zip/Native/DeflateDynamic.lean` switching Level 5
   from chain `24` / `512`-token splits to chain `22` / `2016`-token splits at
   `>= 4 MiB`).
2. **Aggregate vs. Geometric-Mean Spread (`+4.4` to `+6.3 pp`):** Because
   large poorly compressible files (`mozilla` at `51.2 MB`, `webster` at
   `41.5 MB`) outweigh tiny repetitive files (`xml` at `5.3 MB`), aggregate ratio
   `sum(out_size) / sum(size)` shifts systematically higher than unweighted
   12-file geometric mean across every profile (`+4.96` to `+6.19 pp` on
   `lean-zip`; `+6.23 pp` at Level 9 on Rust `rust_safe_hash4_bt`: `0.397177`
   aggregate vs. `0.334858` geometric mean). Both summaries must appear together
   so weighting shifts do not masquerade as algorithmic wins.
3. **Length-Only Verification Blind Spots (`BenchSilesia.lean`):** In
   `lean-zip`'s `BenchSilesia.lean`, `doDecompress` returns `b.size` and only
   verifies `dec0 != n` against input length rather than checking byte-for-byte
   equality `b == raw`. As `verify_benchmarks_and_pareto.py` confirms, an
   adversarial or corrupted stream decompressing to an identical byte count
   silently passes length-only checks.

### Single-Core Quiet Silesia Pareto Frontier (`taskset -c 4`, 2 MiB Prefix)

All throughput figures use `MiB/s` (`1,048,576 B/s`) on raw RFC 1951 streams:

| Profile | L1 Ratio @ Comp (Decomp) | L6 Ratio @ Comp (Decomp) | L8 Ratio @ Comp (Decomp) | L9 Ratio @ Comp (Decomp) |
| :--- | :--- | :--- | :--- | :--- |
| `zlib_1_3_2` | `0.4050 @ 80.0 (306.5)` | `0.3508 @ 25.0 (328.5)` | `0.3462 @ 14.4 (338.9)` | `0.3457 @ 13.1 (340.1)` |
| `miniz_oxide_0_9_1` | `0.4627 @ 136.8 (269.4)` | `0.3492 @ 24.8 (387.2)` | `0.3470 @ 16.7 (404.5)` | `0.3467 @ 15.2 (393.0)` |
| `lean_zip_2f7a63f` | `0.4190 @ 163.5 (243.5)` | `0.3499 @ 24.1 (237.9)` | `0.3451 @ 18.4 (250.8)` | `0.3414 @ 2.55 (184.0)` |
| `rust_safe_hash4_bt` | `0.4129 @ 219.0 (439.4)` | `0.3460 @ 34.1 (550.6)` | `0.3436 @ 24.3 (538.5)` | `0.3349 @ 7.42 (529.2)` |
| `rust_safe_row_hash_bt` | `0.4132 @ 171.7 (429.5)` | `0.3487 @ 38.0 (538.7)` | `0.3447 @ 25.9 (544.2)` | `0.3377 @ 7.69 (527.3)` |
| `rust_unsafe_bt_dp_simd` | `0.4142 @ 220.2 (519.5)` | `0.3455 @ 37.2 (621.8)` | `0.3365 @ 10.7 (629.0)` | `0.3334 @ 6.68 (616.8)` |
| `rust_unsafe_row_hash_simd` | `0.4179 @ 214.6 (521.0)` | `0.3473 @ 36.4 (602.8)` | `0.3368 @ 11.0 (617.4)` | `0.3321 @ 5.53 (626.8)` |

Key structural observations across the `756`-row matrix:

1. **Pointwise vs. Convex-Hull Dominance:** Comparing Level `k` solely against
   Level `k` hides true Pareto dominance when two codecs calibrate levels
   differently. Both Safe Rust profiles (`rust_safe_hash4_bt` and
   `rust_safe_row_hash_bt`) beat `lean_zip_2f7a63f` pointwise across all 9
   levels (`0` failures), reaching `15.51 MiB/s` (`6.08x` faster than `lean_zip`
   L9 `2.55 MiB/s`) at `lean-zip`'s L9 ratio (`0.341448`) via an `L8/L9`
   time-share (`75.1%` L8, `24.9%` L9). Meanwhile, both Unsafe Rust profiles
   appear slower pointwise at L7-L8 because they invest deeper BT/DP work for
   far tighter ratios (`0.3365` vs. `0.3451` at L8). On the true harmonic
   time-sharing hull (`1/v` convexity), `rust_unsafe_bt_dp_simd` dominates
   `lean_zip` L8 (`18.36 MiB/s`) at `33.84 MiB/s` (`1.84x` faster via `91.0%` L6
   + `9.0%` L7) and beats `lean_zip` L9 at `20.02 MiB/s` (`7.85x` faster via
   `22.8%` L6 + `77.2%` L7).
2. **`lean-zip` vs. Upstream C and `miniz_oxide`:** `zlib_1_3_2` yields strictly
   smaller compressed outputs than `lean_zip_2f7a63f` on `42` of `108`
   `(file, level)` pairs (especially Level 1: `0.4050` vs. `0.4190`), while
   running `5.15x` faster at Level 9 (`13.12` vs. `2.55 MiB/s`) and `33-85%`
   faster in INFLATE (`306-340` vs. `184-251 MiB/s`). Meanwhile, all four
   optimized Rust profiles run `2.2x-3.4x` faster at INFLATE (`429-629 MiB/s`)
   and compress tighter across levels 1-9 than both `zlib_1_3_2` and
   `lean_zip_2f7a63f` (note `zlib` L1 achieves `0.4050` ratio at `80.0 MiB/s`,
   where time-sharing Safe Rust L1/L2 achieves higher speed at matched ratio).
3. **`lean-zip` Compiled C IR and Proof-Artifact Footprint:** Inspecting the
   built `lean-zip` (`v4.35.0-rc2`) intermediate tree reveals `41` generated C
   files totaling `9,323,261` bytes containing `328` `lean_is_exclusive`
   ownership checks and `6,237` boxed `lean_nat_*` operations (including `180`
   in `Zip/Native/DeflateL5.c` and structural proof witnesses such as `else if
   hn :` in `Zip/Native/DeflateL5.lean`). `Zip/Native/Wide.c` spans
   `1,378,091` bytes, `96.3%` of which (`1,326,885` bytes on line 108) is a
   single `bv_decide` LRAT proof certificate string for `ctz` equivalence;
   Clang/LLD LTO (`Wide.c.o.export` LLVM IR bitcode) dead-strips this proof
   object cleanly from `bench_silesia` (`6,319,768` bytes total, longest ELF
   string `707` bytes). See
   [Lean 4 MIR semantics and C codegen](../lean-mir-semantics-scalar-truncation-idempotence-and-fast-step-transfer/REPORT.md)
   for the underlying `LCNF.floatLetIn` and Perceus `@&` mechanisms.

## Boundaries

- Measurements cover the 2 MiB Silesia prefix slices on one pinned Intel Ice
  Lake core (`taskset -c 4`); larger buffers (`>= 4 MiB`) trigger adaptive
  algorithmic switches inside `lean-zip`.
- `lean_zip_ir_stats` checks run dynamically when `/tmp/lean-zip/.lake/build`
  exists locally and return `null` otherwise, while the 756-row Silesia JSON
  matrix and length-only blind-spot counterexample remain completely
  self-contained.

## Evidence

| Check | Verified Outcome | Artifact |
| :--- | :--- | :--- |
| Silesia SHA-256 & 211.94 MB | `12/12` files verified (`211,938,580` B) | [verify_benchmarks_and_pareto.py](support/verify_benchmarks_and_pareto.py) |
| 756-row single-core dataset | 7 codecs x 12 files x L1..L9 on `cpu 4` | [silesia_2mib_single_core.json](support/silesia_2mib_single_core.json) |
| Aggregate vs. geomean bias | `+4.4` to `+6.34 pp` systematic shift | [verify_benchmarks_and_pareto.py](support/verify_benchmarks_and_pareto.py) |
| Hull vs. pointwise dominance | Safe `6.08x`, Unsafe `1.84x`/`7.85x` L8/L9 | [verify_benchmarks_and_pareto.py](support/verify_benchmarks_and_pareto.py) |
| `zlib` vs. `lean-zip` & blind spot | `42/108` smaller; `len(a)==len(b)` bypass | [verify_benchmarks_and_pareto.py](support/verify_benchmarks_and_pareto.py) |
| `lean-zip` C IR & ELF stripping | `41` C files (`9.32 MB`), `707 B` max ELF str | [verify_benchmarks_and_pareto.py](support/verify_benchmarks_and_pareto.py) |

## Revalidation

Run the standalone validator inside `support/` and confirm `exit 0`:

```bash
python3 support/verify_benchmarks_and_pareto.py
```
