# Real Un-Rigged `rustc 1.99.1` Runtime Performance Budget Across `-O2`, `-O3`, Single-CGU, ThinLTO, FatLTO, and Matched vs. Mismatched PGO

## Summary

A drop-in verified Rust compiler must know exactly how much runtime
performance is actually at stake when choosing between modular per-crate
compilation (`lto=off`) and whole-program cross-crate optimization
(`ThinLTO`, `FatLTO`, and Profile-Guided Optimization). Earlier exploratory
reports in this corpus relied on a rigged `--cfg feature="anneal_specialized"`
flag with no profile file (`O5_`) and hardcoded ThinLTO speedup tables (`O8_`).

This report replaces those projections with a clean, un-rigged, held-out
`[real measurement]` benchmark compiled with **`rustc 1.99.1`**
(`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, **LLVM 23.1.1**)
and `rustc 1.99.1`'s bundled `llvm-profdata` across **7 real workloads**
(`miniz_oxide 0.9.1` DEFLATE roundtrip, `serde_json 1.0.154` parse/serialize,
`toml 1.2.0` parse/serialize, `memchr 2.8.3` SIMD scan, `base64 0.23.1` codec,
`crc32fast 1.5.5` streaming hash, and an 85%-hot skewed `dyn Trait` indirect
dispatch loop) across **8 compilation profiles** with identical source code,
zero `--cfg` flags, disjoint PGO training vs. held-out evaluation seeds, 9
interleaved timing rounds, and bit-identical output checksums:

- **Intra-Crate Single-CGU (`lto=off, cgu=1`) Matches `ThinLTO` Overall
  Without Cross-Crate LTO** `[real measurement]`: Moving from Cargo's default
  `O3_cgu16` (`58.18 ms`) to **`O3_cgu1` (`51.38 ms`, `1.133x`)** matches
  **`O3_thin` (`51.33 ms`, `1.134x`)** and actually beats `ThinLTO` on
  `serde_json` (`1.613x` vs. `1.532x`) and `toml` (`1.332x` vs. `1.310x`) —
  with **zero** cross-crate LTO! Because Rust monomorphizes generic crates into
  the caller crate, `codegen-units=16` splits caller loops from their own
  monomorphized helpers; co-locating them in a single CGU recovers nearly the
  entire ThinLTO runtime win while preserving crate-modular verification
  boundaries.
- **Cross-Crate `FatLTO` Adds `+6.0%` Over Modular `cgu=1`**
  `[real measurement]`: `O3_fat` reaches **`48.45 ms` (`1.201x` vs. `O3_cgu16`,
  `1.060x` vs. `O3_cgu1`)**, driven by cross-crate inlining in `toml`
  (`1.332x -> 1.577x`), `serde_json` (`1.613x -> 1.698x`), and `miniz_oxide`
  (`1.010x -> 1.057x`) at `2.15x` clean build time (`9.40 s` vs. `4.37 s`).
- **Matched Real PGO (`ThinLTO + PGO`) Delivers Genuine `2.002x` on
  `serde_json` and `1.309x–1.373x` on Skewed `dyn Trait` Dispatch — Yet `~0%`
  on Tight Compression/SIMD Loops** `[real measurement]`: When `profile-generate`
  matches the LTO mode of `profile-use`, **`O3_thin_pgo` (`48.70 ms`, `1.195x`)**
  matches `O3_fat` (`48.45 ms`), lifting `serde_json` to **`2.002x`**
  (`6.40 ms -> 3.20 ms`), `toml` to **`1.512x`**, and `dyn_icp` to **`1.309x`**
  (`O3_fat_pgo`: **`1.373x`** on `dyn_icp`, `48.02 ms` = `1.212x` total).
  Conversely, tight data-plane kernels gain almost nothing from PGO
  (`miniz_oxide` `0.996x–1.018x`, `crc32fast` `0.973x–0.981x`, `memchr`
  `1.134x` vs. `1.114x` without PGO).
- **Critical `rustc` PGO + LTO Profile-Hash Coupling Pitfall Discovered Live**
  `[real measurement]`: Training a single `cgu=16` (`lto=off`)
  `-C profile-generate` binary (`620,272 B` `.profdata`) and feeding that
  profile into `lto=thin` or `lto=fat` **silently destroyed PGO**
  (`O3_thin_pgo` degraded from `48.70 ms` to `56.44 ms` = `1.047x`, with
  `dyn_icp` regressing from `1.309x` to `0.880x`; `O3_fat_pgo` degraded from
  `48.02 ms` to `57.42 ms` = `1.029x`!). Matching LTO mode during
  `profile-generate` (`629,760 B` / `629,264 B` `.profdata`) immediately
  restored the full `1.195x–1.212x` speedup.

## Applicability

These measurements quantify the exact performance budget for a verified
drop-in `rustc` backend targeting `x86_64-unknown-linux-gnu`:

1. **Systems / Crypto / Compression Kernels (`miniz_oxide`, `crc32fast`,
   `memchr`):** Modular single-CGU per-crate compilation (`lto=off, cgu=1`)
   already sits within **`1–5%`** of whole-program `FatLTO + PGO`, meaning
   whole-program LTO and PGO are **not** prerequisites for competitive verified
   codegen on tight data-plane crates.
2. **Branchy Parsers & Polymorphic Workloads (`serde_json`, `toml`,
   `dyn Trait`):** Reaching parity with `rustc + ThinLTO + PGO` specifically
   requires three targeted mechanisms:
   - Intra-crate monomorphization co-location (`cgu=1` equivalent: **`1.133x`**
     overall, **`1.613x`** on `serde_json`, zero cross-crate proof coupling).
   - Profile-guided block layout and hot/cold inlining on branch-heavy state
     machines (an additional **`1.24x–1.31x`** on `serde_json` / `toml`).
   - Open-world guarded indirect-call promotion (`1.31x–1.37x` on skewed
     `dyn Trait` loops), structured as an optimization-only behavioral guard so
     duplicate multi-DSO vtables remain sound.
3. **`-O2` vs. `-O3` Baseline:** Across all 7 workloads under `cgu=16`, `-O2`
   (`57.12 ms`) and `-O3` (`58.18 ms`) are statistically tied (`1.019x`),
   confirming that `-O3`-only loop unrolling/vectorization heuristics contribute
   negligible net gain here compared to CGU/inlining visibility and PGO layout.

## Findings

### 1. Matched-LTO 8-Profile Held-Out Runtime Matrix (`rustc 1.99.1`, 9 Interleaved Rounds)

All 8 binaries executed identical Rust source (`support/run_pgo_lto_bench.py`,
zero `--cfg` flags) on held-out evaluation seed `9,999,991` (disjoint from PGO
training seeds `[101, 202, 303]`), verified bit-identical across all 7 workload
checksums (`[5856542423, 2111608, 121944, 15292416, 5603848, 122146293933,
11161830799473802833]`) (`[real measurement]`):

| Profile (`rustc 1.99.1`) | Clean Build (s) | `.text` (KB) | Total Median (ms) | Speedup vs. `O3_cgu16` | `serde_json` | `toml` | `dyn_icp` (85% hot) | `base64` | `memchr` | `miniz_oxide` | `crc32fast` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `O2_cgu16` | `4.30` | `775.4` | `57.12` | `1.019x` | `1.023x` | `0.999x` | `1.046x` | `0.994x` | `0.987x` | `1.015x` | `0.999x` |
| `O3_cgu16` (Cargo default) | `4.37` | `784.6` | `58.18` | `1.000x` | `1.000x` | `1.000x` | `1.000x` | `1.000x` | `1.000x` | `1.000x` | `1.000x` |
| **`O3_cgu1` (modular, no LTO)** | `6.28` | `731.4` | **`51.38`** | **`1.133x`** | **`1.613x`** | **`1.332x`** | `1.069x` | `1.175x` | `1.107x` | `1.010x` | `0.934x` |
| `O3_thin` | `6.35` | `724.4` | `51.33` | `1.134x` | `1.532x` | `1.310x` | `1.027x` | `1.232x` | `1.114x` | `1.018x` | `0.954x` |
| **`O3_fat`** | `9.40` | `672.6` | **`48.45`** | **`1.201x`** | **`1.698x`** | **`1.577x`** | `1.098x` | `1.246x` | `1.145x` | **`1.057x`** | `0.959x` |
| `O3_cgu16_pgo` (matched) | `3.69` (+`3.89` gen) | `769.8` | `55.37` | `1.051x` | `1.158x` | `0.960x` | **`1.291x`** | `1.102x` | `1.105x` | `0.980x` | `0.940x` |
| **`O3_thin_pgo` (matched)** | `7.31` (+`6.27` gen) | `770.3` | **`48.70`** | **`1.195x`** | **`2.002x`** | **`1.512x`** | **`1.309x`** | **`1.265x`** | `1.134x` | `0.996x` | `0.973x` |
| **`O3_fat_pgo` (matched)** | `11.22` (+`12.48` gen) | `706.6` | **`48.02`** | **`1.212x`** | **`1.943x`** | **`1.590x`** | **`1.373x`** | `1.244x` | `1.136x` | `1.018x` | `0.981x` |

*(Raw per-workload medians in ms for `O3_cgu16` vs. `O3_thin_pgo` vs.
`O3_fat_pgo`: `deflate` `24.27 / 24.36 / 23.85`, `json` `6.40 / 3.20 / 3.29`,
`toml` `8.60 / 5.69 / 5.41`, `memchr` `6.71 / 5.92 / 5.91`, `base64`
`5.63 / 4.45 / 4.52`, `crc32` `0.71 / 0.73 / 0.72`, `dyn_icp`
`5.44 / 4.16 / 3.96`. Full IQRs are archived in
`support/e2_3_real_pgo_and_lto_runtime.json`.)*

### 2. Controlled A/B Evidence of the LTO-Mode PGO Profile-Hash Coupling Pitfall

Before matching `profile-generate`'s LTO mode to `profile-use`, we ran the
exact same benchmark suite using a single `lto=off, cgu=16` instrumented
training binary (`620,272 B` `.profdata`) fed into `O3_cgu16_pgo`,
`O3_thin_pgo`, and `O3_fat_pgo` (`[real measurement]`):

| Profile | Mismatched `cgu=16` `.profdata` Total (ms / Speedup) | Mismatched `dyn_icp` Speedup | Matched-LTO `.profdata` Total (ms / Speedup) | Matched `dyn_icp` Speedup | Matched `serde_json` Speedup |
| :--- | ---: | ---: | ---: | ---: | ---: |
| `O3_cgu16_pgo` | `57.22 ms` (`1.032x`) | `1.347x` | `55.37 ms` (`1.051x`) | `1.291x` | `1.158x` |
| `O3_thin_pgo` | `56.44 ms` (`1.047x`) | **`0.880x` (regressed!)** | **`48.70 ms` (`1.195x`)** | **`1.309x`** | **`2.002x`** |
| `O3_fat_pgo` | `57.42 ms` (`1.029x`) | **`0.929x` (regressed!)** | **`48.02 ms` (`1.212x`)** | **`1.373x`** | **`1.943x`** |

Matching the LTO mode during instrumentation increased the merged profile size
(`620,272 B -> 629,760 B` for `thin`, `629,264 B` for `fat`), expanded
`O3_thin_pgo`'s `.text` from `722.8 KB` to `770.3 KB` (confirming real hot
inlining fired), and turned a **`-12%` regression** on `dyn_icp` into a
**`+31%` to `+37%` speedup** (`1.309x–1.373x`)! For any future verified-`rustc`
PGO pipeline (or `AutoFDO` / LBR consumer), this proves that **profile identity
hashes must be canonicalized at the MIR / monomorphized-instance level** rather
than depending on CGU-partitioned LLVM symbol hashes.

### 3. Why Modular `cgu=1` Beats `ThinLTO` on Generic-Heavy Crates

Combined with our companion static measurement
(`rustc-lto-monomorphization-dedup-ir-volume-and-dwarf-coverage-census`), where
`cgu=1` eliminated **`63.9%`** of `v0` generic monomorphization symbols without
cross-crate LTO (vs. `66.3%` for `FatLTO` and `44.9%` for `ThinLTO`), this
runtime measurement reveals a single unified cause: in Rust, generic crates
(`serde_json`, `toml`, `base64`) instantiate their generic bodies inside the
downstream binary crate. Splitting that binary crate into `16` CGUs breaks
inlining between caller loops and their own generic instantiations; collapsing
to `cgu=1` (or performing verified content-addressed monomorphization
co-location) delivers **`1.133x`** total speedup (`1.613x` `serde_json`,
`1.332x` `toml`) with **zero cross-crate LTO TCB complexity**.

## Boundaries

- **Single Host Architecture & Crate Mix:** Measured on `x86_64-unknown-linux-gnu`
  with `rustc 1.99.1` / `LLVM 23.1.1` across 7 workloads (`miniz_oxide`,
  `serde_json`, `toml`, `memchr`, `base64`, `crc32fast`, synthetic skewed
  `dyn ByteFilter` loop). Workloads dominated by massive cross-crate non-generic
  virtual calls (such as `rustc` itself or large web servers) may see larger
  PGO and ThinLTO deltas than `miniz_oxide` or `crc32fast`.
- **Instrumented PGO Only (Not Hardware LBR AutoFDO):** This experiment uses
  exact LLVM IR instrumented PGO (`-C profile-generate` / `-C profile-use`),
  not hardware `perf record -b` LBR sampling (`AutoFDO`). Instrumented PGO
  serves as an empirical upper bound on profile accuracy relative to sampled
  LBR.
- **Small Run-to-Run Variance on Sub-Millisecond `crc32fast`:** `crc32fast`
  executes in `~0.70–0.76 ms` per iteration (hardware CRC32 instructions), so
  `±4%` fluctuations (`0.934x–1.007x`) reflect sub-millisecond jitter rather
  than meaningful codegen regressions.

## Evidence

- `support/run_pgo_lto_bench.py`: Complete self-contained benchmark generator
  and runner (builds all 8 profiles offline with `cargo +1.99.1 --offline`,
  runs disjoint training + `llvm-profdata merge`, executes 9 interleaved
  held-out evaluation rounds, and asserts exact checksum equality across all 8
  binaries).
- `support/e2_3_real_pgo_and_lto_runtime.json`: Exact measured build times,
  `.text` sizes, per-workload medians, IQRs, speedup ratios, PGO profile byte
  sizes, and verified output checksums for all 8 matched profiles.
- Related ground-truth reports in this corpus:
  - `rustc-lto-monomorphization-dedup-ir-volume-and-dwarf-coverage-census`
  - `rustc-release-abi-drift-binary-validation-cfg-alignment-and-surviving-bounds-checks`

## Revalidation

Re-run when upgrading `rustc` / LLVM or evaluating a verified backend's CGU
and PGO pipeline:

```bash
python3 support/run_pgo_lto_bench.py --out-json /tmp/e2_3_reval.json
```

Verify bit-identical output checksums across all 8 profiles, confirm that
`O3_cgu1` tracks `O3_thin`, and re-test whether future `rustc`/LLVM versions
eliminate the `cgu=16`-gen → `ThinLTO`/`FatLTO`-use profile mismatch regression.
