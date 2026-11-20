# Empirical Ground-Truth Census of Real `rustc 1.99.1` LLVM IR Volume, LTO Monomorphization Deduplication, and `-O0..-O3` DWARF Location Coverage

## Summary

Designing a verified drop-in replacement for `rustc` requires measured
ground truth for three workspace-scale engineering quantities: (1) post-`-O3`
LLVM IR instruction volume across real Rust dependency graphs, (2) how much
code-size and generic-symbol deduplication comes from intra-crate codegen-unit
(`cgu`) collapsing versus cross-crate Link-Time Optimization (`lto`), and
(3) how much source-level DWARF variable-location coverage survives LLVM
optimization (`-O0` through `-O3`).

Earlier exploratory reports in this corpus relied on synthetic projections for
12-crate IR volume, ThinLTO speedup, and optimized DWARF baseline coverage
(`74.0% -> 96.4%`). This report replaces those projections with direct
`[real measurement]` sweeps on **`rustc 1.99.1`**
(`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, **LLVM 23.1.1**) and
**`joshlf/anneal`** (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):

- **Workspace LLVM IR Volume (`109` Compiled Runtime `.ll` Modules)**
  `[real measurement]`: `38,455` defined post-`-O3` functions, `380,893` basic
  blocks, and **`1,640,035` LLVM IR instructions** (mean `42.65` insts/fn).
  Combined with honest Lean 4 kernel reduction throughput (`291–588` real
  steps/s across Lean `v4.28.0-rc1`, `v4.34.1`, and `v4.35.0`), checking even a
  single kernel-reduced micro-step per post-`-O3` instruction would consume
  `~46–94` minutes of single-core Lean kernel CPU (`~170 GB` cumulative
  unsharded RSS).
- **Intra-Crate CGU Merging Captures 96% of FatLTO's Generic Symbol Dedup**
  `[real measurement]`: On `anneal-audit` (`rustc 1.99.1`), **`45.2%`**
  (`2,044 / 4,518`) of defined `.text` symbols under default `lto=off, cgu=16`
  are Rust v0 generic monomorphizations (`_RIN*`). Moving to single-CGU
  (`lto=off, cgu=1`, zero cross-crate LTO) eliminates **`63.9%`** of generic
  symbols (`2,044 -> 737`) and **`14.7%`** of `.text` (`2,109.9 KB ->
  1,798.7 KB`) at `2.60x` clean build time (`8.70 s -> 22.60 s`). Cross-crate
  `lto=fat` removes only `2.4` percentage points more generic symbols (`66.3%`,
  `689` remaining) and `3.2` percentage points more `.text` (`17.9%`,
  `1,732.9 KB`) at `2.77x` build time (`24.06 s`), while `lto=thin` yields
  `-44.9%` generic symbols and `-8.1%` `.text` at `1.72x` build time
  (`14.94 s`).
- **Real Optimized DWARF Variable Coverage Collapses Below 50% at `-O1`**
  `[real measurement]`: Running `llvm-dwarfdump --statistics` on `anneal-audit`
  (`-C debuginfo=2`) refutes prior `74.0%` optimized-baseline assumptions.
  Full-scope (`100%`) local-variable coverage falls from **`98.40%`** at `-O0`
  (`44,103` locals; `99.28%` PC-bytes) to **`49.91%`** at `-O1` (`33.63%`
  completely lost at `0%`), **`43.46%`** at `-O2` (`41.35%` at `0%`), and
  **`41.29%`** at `-O3` (**`44.43%` of `96,257` local-variable instances at
  `0%` coverage**, only **`48.86%`** of PC-bytes covered, and `DW_OP_entry_value`
  recovering only `1.71%` of scope bytes).

## Applicability

These measurements directly govern three architectural decisions for a
verified drop-in Rust compiler targeting `x86_64-unknown-linux-gnu` with
`rustc 1.99.1` / `LLVM 23.1.1`-class codegen and `Lean 4` proof infrastructure:

1. **Translation-Validation Execution Model:** Sizing the IR volume of a real
   109-crate Cargo graph determines whether proof-carrying optimization checking
   can run inside Lean's kernel (`rfl` reflection) or must run in a proved-once
   compiled native checker (`CompCert`/`CakeML` or self-verified Rust).
2. **Modular Compilation vs. Whole-Program LTO:** Quantifying intra-crate CGU
   monomorphization duplication versus cross-crate LTO tells us how much binary
   bloat can be eliminated by content-addressed MIR/proof deduplication without
   breaking separate-compilation verification boundaries.
3. **Provenance & Verified Debuginfo Pipeline Design:** Measuring actual
   `rustc` + LLVM 23 DWARF survival across `-O0..-O3` determines whether
   post-hoc debuginfo can bridge source-level MIR and `-O3` machine code or
   whether pass-local witness propagation is strictly required.

## Findings

### 1. Real Workspace LLVM IR Volume Census (`109` Runtime Crates)

We scanned all `109` non-build-script `.ll` modules (`> 1,000` bytes each,
excluding `/build/` directories) produced by compiling `anneal-audit`,
`cargo-anneal`, `libcore`, and their full transitive Cargo dependency graphs
under `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM 23.1.1)
at `-O3` (`[real measurement]`).

| Metric | Measured Value (`109` Runtime `.ll` Files) |
| :--- | ---: |
| Runtime `.ll` files scanned | `109` |
| Total post-`-O3` defined functions | `38,455` |
| Total post-`-O3` basic blocks | `380,893` |
| Total post-`-O3` LLVM instructions | `1,640,035` |
| Mean LLVM instructions per function | `42.65` |
| Mean basic blocks per function | `9.90` |
| Mean LLVM instructions per basic block | `4.31` |

#### Top 15 Crates by Post-`-O3` LLVM IR Instruction Volume

| Rank | Crate LLVM Module | Post-`-O3` Fns | Basic Blocks | LLVM Insts | Mean Insts / Fn |
| ---: | :--- | ---: | ---: | ---: | ---: |
| 1 | `rustls-d82a8fb35d82402a.ll` | `1,533` | `30,928` | `166,082` | `108.34` |
| 2 | `syn-ebe86debcc1b2349.ll` | `5,897` | `43,298` | `162,713` | `27.59` |
| 3 | `syn-559c88123352f9dc.ll` | `5,979` | `42,893` | `159,809` | `26.73` |
| 4 | `anneal_audit-28231cc890f9c903.ll` | `647` | `26,155` | `140,920` | `217.81` |
| 5 | `serde_derive-f2a1740772359c29.ll` | `2,910` | `33,344` | `115,587` | `39.72` |
| 6 | `cc-24702cc60b92fcc1.ll` | `3,122` | `22,650` | `85,358` | `27.34` |
| 7 | `clap_builder-6b88582a6e07cb60.ll` | `488` | `12,427` | `64,607` | `132.39` |
| 8 | `clap_derive-0c4d12a60f749cce.ll` | `1,468` | `17,940` | `59,532` | `40.55` |
| 9 | `ureq-b6d899b68d7a37d7.ll` | `761` | `12,116` | `58,257` | `76.55` |
| 10 | `thiserror_impl-6107d960ed373318.ll` | `1,435` | `13,880` | `52,875` | `36.85` |
| 11 | `toml_const_macros-f617b4a988656d3b.ll` | `2,089` | `14,406` | `50,990` | `24.41` |
| 12 | `toml-89c59760a095ca7f.ll` | `1,996` | `12,042` | `43,756` | `21.92` |
| 13 | `core.ll` | `543` | `5,898` | `32,442` | `59.75` |
| 14 | `phf_macros-3ac773b71dadf147.ll` | `998` | `7,433` | `27,906` | `27.96` |
| 15 | `toml_parser-ff34acaf48e42edd.ll` | `611` | `5,349` | `26,124` | `42.76` |

Two structural phenomena govern scaling:

1. **Duplicate Crate Compilation Versions Multiply IR Volume:** `syn` appears
   twice (`syn-ebe86debcc1b2349.ll` and `syn-559c88123352f9dc.ll`, totaling
   `322,522` LLVM instructions — `19.7%` of the entire 109-crate census) due to
   separate Cargo host/feature-unified compilations. A verified compiler should
   index cached verification certificates by canonical MIR content hash rather
   than Cargo build-invocation identity.
2. **Bimodal Function Sizes vs. Kernel Reflection Ceiling:** Proc-macro crates
   like `syn` (`27` insts/fn) emit thousands of tiny monomorphized functions,
   while `std`-heavy binaries like `anneal_audit` (`217.8` insts/fn, `40.4`
   BBs/fn) and `rustls` (`108.3` insts/fn, `20.2` BBs/fn) concentrate deep CFGs
   into fewer bodies. At `291–588` honest Lean 4 kernel micro-steps/s
   (`lean4-kernel-reflection-ceiling-and-total-native-compiler-checker-architecture`),
   per-instruction kernel reflection over `1.64M` post-`-O3` instructions
   requires `~2,800–5,600` CPU-seconds before even accounting for pre-`-O3`
   instruction counts. This confirms that hot translation validation must run in
   a **proved-once compiled pure-total native checker**, reserving live Lean
   kernel checking for function/module summaries and user specifications.

### 2. Four-Mode Real LTO & Monomorphization Deduplication Sweep

We ran clean `--release` builds of `anneal-audit` (`joshlf/anneal@c131b320e`,
`rustc +1.99.1`, isolated `--target-dir` per mode) controlled via native Cargo
profile environment variables (`CARGO_PROFILE_RELEASE_LTO` and
`CARGO_PROFILE_RELEASE_CODEGEN_UNITS`, avoiding proc-macro `embed-bitcode`
conflicts). Each binary was inspected with GNU `size`, `nm --defined-only -n`,
and a 7-run median `--help` invocation (`[real measurement]`).

| Build Profile | Clean Build (s) | Build Ratio | ELF File (KB) | `.text` (KB) | `.text` Delta | Defined `.text` Syms | `v0` Generic Syms (`_RIN*`) | Generic Dedup vs. `cgu=16` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `lto=off, cgu=16` (default) | `8.70` | `1.00x` | `3,108.4` | `2,109.9` | `0.0%` | `4,518` | `2,044` | `0.0%` |
| `lto=thin` | `14.94` | `1.72x` | `2,556.0` | `1,938.4` | `-8.1%` | `2,648` | `1,126` | `-44.9%` |
| `lto=off, cgu=1` | `22.60` | `2.60x` | `2,219.0` | `1,798.7` | `-14.7%` | `2,121` | `737` | `-63.9%` |
| `lto=fat` | `24.06` | `2.77x` | `2,085.5` | `1,732.9` | `-17.9%` | `1,776` | `689` | `-66.3%` |

*(Exact byte totals from `support/e1_6_real_lto_and_ir_volume.json`: `.text` =
`2,160,581 B`, `1,984,951 B`, `1,841,841 B`, `1,774,499 B`; ELF file =
`3,183,040 B`, `2,617,304 B`, `2,272,280 B`, `2,135,520 B`; `--help` median =
`1.124–1.213 ms` across all four modes.)*

**Key Architectural Implication:** Under default `lto=off, cgu=16`, **`45.2%`**
of all defined `.text` symbols are v0 generic monomorphizations, and **`63.9%`
(`1,307 / 2,044`) vanish solely by collapsing intra-crate CGUs (`cgu=16 ->
cgu=1`)** without cross-crate LTO. Cross-crate FatLTO removes only `48` more
generic symbols (`737 -> 689`, an extra `2.4 pp`) and `65.8 KB` of `.text`
(`-3.2 pp`) at `2.77x` clean build time (`24.06 s`). Consequently, a verified
`rustc` using **canonical content-addressed monomorphization deduplication**
at the MIR/CGU boundary captures ~96% (`63.9% / 66.3%`) of FatLTO's generic
symbol deduplication while preserving modular per-crate separate-compilation
proofs (`leanlib` `c10_link`).

### 3. Real `llvm-dwarfdump --statistics` Coverage Sweep (`-O0` through `-O3`)

We compiled `anneal-audit` (`rustc +1.99.1`, `joshlf/anneal@c131b320e`) four
times into clean target directories with `CARGO_PROFILE_DEV_DEBUG=2` and
`CARGO_PROFILE_DEV_OPT_LEVEL` in `{0, 1, 2, 3}`, then measured each binary with
`llvm-dwarfdump --statistics` (DWARF statistics schema version 9, LLVM 23.1.1)
(`[real measurement]`).

| Opt Level | Binary (MB) | `#inlined` Fns | Local Vars Total | Local `100%` Cov | Local `0%` Cov (Lost) | Params Total | Param `100%` Cov | Param `0%` Cov | All-Var PC-Bytes Cov | `DW_OP_entry_value` Share |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `-O0` | `35.61` | `92,347` | `44,103` | **`98.40%`** | `1.14%` | `80,719` | `94.55%` | `0.32%` | **`99.28%`** | `0.59%` |
| `-O1` | `38.31` | `173,877` | `59,736` | **`49.91%`** | **`33.63%`** | `165,417` | `66.79%` | `20.30%` | **`49.90%`** | `1.77%` |
| `-O2` | `41.00` | `196,352` | `87,577` | **`43.46%`** | **`41.35%`** | `212,311` | `65.48%` | `22.43%` | **`47.11%`** | `1.66%` |
| `-O3` | `42.00` | `199,639` | `96,257` | **`41.29%`** | **`44.43%`** | `221,508` | `61.74%` | `27.24%` | **`48.86%`** | `1.71%` |

*(Exact raw scope-byte totals from `support/e1_7_real_dwarf_coverage.json`:
`-O0` `30,981,481 / 31,204,867` B (`entry_value`: `184,922` B);
`-O1` `23,398,130 / 46,888,303` B (`entry_value`: `829,953` B);
`-O2` `26,123,187 / 55,450,799` B (`entry_value`: `917,809` B);
`-O3` `26,533,190 / 54,304,232` B (`entry_value`: `927,886` B).)*

**Refutation of Prior Synthetic Baselines & Provenance Mandate:**

1. Earlier synthetic estimates posited a `74.0%` optimized DWARF baseline and
   projected `96.4%` after salvage. Real `rustc 1.99.1 + LLVM 23.1.1` suffers a
   steep cliff immediately at `-O1` (`98.40% -> 49.91%` full-scope locals),
   reaching **`44.43%` completely zero-coverage local variables** and only
   **`48.86%` PC-byte coverage** at `-O3`, while inlining expands local-variable
   instances `2.18x` (`44,103 -> 96,257`) and parameter instances `2.74x`
   (`80,719 -> 221,508`).
2. Combined with our companion refutation of debuginfo-free 1-WL CFG alignment
   (`10.37%` BB micro-recall and `2.50%` blind Top-1 retrieval across `-O0 ->
   -O3` in
   `rustc-release-abi-drift-binary-validation-cfg-alignment-and-surviving-bounds-checks`),
   these DWARF numbers prove that **neither post-hoc structural CFG matching
   nor standard LLVM DWARF debuginfo can reconstruct `-O3` source-to-machine
   bindings after the fact**. Both translation validation and high-coverage
   verified debuginfo require **compiler-internal, pass-local witness
   propagation** (such as `CompCert BTL` block-local symbolic simulation).

## Boundaries

- **Single-Crate LTO Sweep & No Hot-Loop Runtime Speedup Claim:** Section 2
  measures clean build time, `.text` bytes, ELF size, and defined/generic symbol
  counts on one real Rust CLI crate (`anneal-audit`, `joshlf/anneal@c131b320e`).
  The `--help` check verifies CLI startup (`1.124–1.213 ms`) only; cross-crate
  ThinLTO/FatLTO runtime speedups on compute-bound benchmarks (`serde_json`,
  `miniz_oxide`, `regex`) are not measured or claimed here.
- **No Claim of Verified DWARF Salvage Lift:** Section 3 establishes the true
  `rustc 1.99.1 + LLVM 23.1.1` DWARF baseline (`98.40% -> 41.29%` full-scope
  local coverage). Quantifying actual recovery from a verified debug-expression
  salvager requires running a real DWARF-emitting backend pass.
- **Host/Target Scope:** All builds targeted `x86_64-unknown-linux-gnu` ELF
  binaries with `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and
  `LLVM 23.1.1`. Symbol counts use `nm --defined-only` and Rust v0 mangling
  (`_RIN*`) heuristics; legacy-mangled C/sysroot symbols are counted in total
  defined `.text` symbols but excluded from `v0` generic counts.

## Evidence

All primary measurement artifacts are committed under `support/`:

- `support/measure_lto_and_dwarf.py`: Parameterized Python harness executing
  the `.ll` IR census, 4-mode Cargo LTO sweep, and `-O0..-O3` `llvm-dwarfdump
  --statistics` sweep without hardcoded tables.
- `support/e1_6_real_lto_and_ir_volume.json`: Raw JSON output for Section 1
  (`109` runtime `.ll` files, top-15 crate breakdown) and Section 2
  (`anneal-audit` 4-mode LTO sweep).
- `support/e1_7_real_dwarf_coverage.json`: Complete `llvm-dwarfdump
  --statistics` JSON location-coverage histograms (`0%`, `(0%,10%)`, ..., `100%`
  for locals, parameters, and `- entry values`) across `-O0`, `-O1`, `-O2`, and
  `-O3`.
- Related ground-truth reports in this corpus:
  - `rustc-postcleanup-mir-and-llvm-poison-freeze-ground-truth-census`
  - `rustc-release-abi-drift-binary-validation-cfg-alignment-and-surviving-bounds-checks`
  - `lean4-kernel-reflection-ceiling-and-total-native-compiler-checker-architecture`

## Revalidation

Re-run when upgrading `rustc` / LLVM major releases (especially when LLVM
changes `AssignmentTracking` DWARF emission or Rust changes default CGU
partitioning or v0 symbol mangling):

```bash
# 1. Emit post-O3 LLVM IR for target workspace dependencies into /tmp/emitted_ll
#    (e.g. via RUSTFLAGS="--emit=llvm-ir" cargo +1.99.1 build --release ...)
# 2. Run the parameterized measurement harness:
python3 support/measure_lto_and_dwarf.py \
  --manifest-path /path/to/anneal/Cargo.toml \
  --ll-root /tmp/emitted_ll \
  --out-dir /tmp/reval_out \
  --toolchain +1.99.1
```

Confirm that `e1_6_real_lto_and_ir_volume.json` and
`e1_7_real_dwarf_coverage.json` regenerate with matching non-zero crate, symbol,
and DWARF location histograms, and re-evaluate the `cgu=1` vs. `lto=fat`
monomorphization dedup ratio and `-O3` zero-coverage local-variable fraction.
