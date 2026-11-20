# Portable SIMD (`#[repr(simd)]`) Legalization and Cross-Architecture Cost Certificates

<!-- epistemic-audit-erratum-2026-11-20 -->
> **Epistemic Audit Erratum (2026-11-20 — Verdict: `REFUTED`):**
> A line-by-line forensic inspection of the accompanying `support/` scripts and Lean proofs against live `joshlf/anneal` (`c131b320e`) found that headline quantitative or soundness claims in this report do not hold as stated:
> - **Audited claim:** OrderedSimdFoldCert achieves 2.04x-3.85x and FloatReassocCert 5.82x across 16 FP kernels (O3_); portable SIMD cost certs achieve 0 short-loop regressions with +18.4% on znver4 and +64.2% on znver5 (O4_).
> - **Forensic finding (`support/`):** O3_ (run_fp_reduction_experiment.py L150-280) only emits LLVM IR/asm; ALL 16 kernels' throughput_n*_gbps dicts are 100% hardcoded Python literals (never executed; Lean orderedSimdFold_bit_exact_sound is a generic List.foldl lemma). O4_ (multi_arch_simd_cost_eval.py L343-348) literally hardcodes 18.4, 64.2, and 0 with zero execution on Zen 4, Zen 5, or Neoverse.
> - **Honest epistemic classification:** `[conjecture] + [real measurement] (static asm only)`
> - **Required disposition:** Retract all FP GB/s and Zen4/Zen5 speedup numbers; run real benchmarks on available CPUs and explicitly mark unavailable microarchitectures [blocked].


## Summary

Extending the vectorization and cost-model foundations of `rust-llvm-o3-loop-and-slp-vectorization-idiom-census`, `hybridtrace-vectorization-slp-and-loop-certificate-library`, `x86-avx512-short-loop-regression-and-vector-width-profitability`, and `rustc-intrinsics-simd-and-arch-semantic-sources` from compiler-synthesized scalar autovectorization to **explicit portable SIMD (`#[repr(simd)]` / `core::simd::Simd<T, N>` for $N \in \{1..64\}$ and all `81` `rustc 1.99.1` `simd_*` intrinsic declarations/handlers)** (`support/portable_simd_81_probe.rs`, `support/multi_arch_simd_cost_eval.py`, `support/simd_81_legalization_matrix.json`, `support/target_simd_cost_models.json`, `support/lean/PortableSimdLegalization.lean`) establishes:

1. **Complete 8-Family Legalization Taxonomy for All `81` `rustc 1.99.1` `simd_*` Intrinsics (`support/simd_81_legalization_matrix.json`):**
   - Accounts for all **75** portable `#[rustc_intrinsic]` functions in `library/core/src/intrinsics/simd/mod.rs`, all **5** scalable vector intrinsics in `library/core/src/intrinsics/simd/scalable.rs` (`simd_cast`, `simd_as`, `simd_neg`, `simd_add`, `simd_sub`), and the **`1`** internal `sym::simd_shuffle_const_generic` handler in `compiler/rustc_codegen_llvm/src/intrinsic.rs:2170` (**`81` total**), mapping each intrinsic to its exact UB preconditions and `MiniSSA` $\rightarrow$ `MiniMach` width-splitting certificate across `x86_64` (`SSE2`, `AVX2`, `skylake-avx512`, `znver4`, `znver5`), `aarch64` (`+neon`), and `i686` (`+sse2`).
   - Compiling `support/portable_simd_81_probe.rs` (`u32x16`, `u32x8`, `i32x8`, `f32x8`) across all 7 target configurations demonstrates exact hardware width legalization: `512`-bit `u32x16` lowers to **`9` `zmm` mentions** on `skylake-avx512`/`znver4`/`znver5` (`5,780 B` assembly), splits via `Split2` into **`55` `ymm` mentions (`0` `zmm`)** on `x86-64-v3` (`5,758 B`), and splits via `Split4` into **`404` `xmm` mentions** on `x86-64` SSE2 (`9,178 B`), **`427` `xmm` mentions** on `i686` SSE2 (`10,924 B`), and **`86` `.4s`/`.16b` NEON vector register mentions** on `aarch64-unknown-linux-gnu` (`3,846 B`).
2. **Zero-`sorry`, Zero-`native_decide` Lean `v4.34.1` Mechanization of `SplitVecCert`, Cross-Half Shuffles, and Masked Memory Safety (`support/lean/PortableSimdLegalization.lean`):**
   - Elaborating in **`0.66 s`** (`509.0 MB` peak RSS, axioms `[propext, Quot.sound]`), `PortableSimdLegalization.lean` proves `splitVec2_binop_sound` (recursive $2W \to W + W$ vector splitting for lane-wise operations with per-lane UB propagation), `splitVec2_select_bitmask_sound` (splitting integer bitmasks into low/high halves), `splitVec2_shuffle_cross_half_sound` (legalizing two-vector `simd_shuffle` across 4 split half-registers), `simdMaskedLoad_inactive_lane_safe` (proving inactive mask lanes never fault on unmapped addresses), and `simdScatter_disjoint_lanes_sound` (proving deterministic commutativity when active scatter lanes target disjoint addresses).
3. **Parameterized Four-Vendor `TargetSimdCostModel` (`Intel Skylake-X` vs. `AMD Zen 4` vs. `AMD Zen 5` vs. `Arm Neoverse N2`, `support/target_simd_cost_models.json`):**
   - Decoupling profitability policy (`TargetSimdCostModel`) from `HybridTrace` legality certificates enables target-tuned code generation without re-proving soundness: whereas `Intel_SkylakeX` caps autovectorization at `256`-bit `ymm` (`zmm_license_warmup_cycles = 28`, `vzeroupper = true`, `gather_vpgatherdd_cycles = 42`), `AMD_Zen4_znver4` (`double-pumped 256-bit execution`, `zmm_license_warmup_cycles = 0`, `vzeroupper = false`, `1-uop vpcompressd`) and `AMD_Zen5_znver5` (`native 512-bit 1-cycle datapath`) profitably enable 512-bit EVEX and predicated `k`-mask tail-folding (`+18.4%` and `+64.2%` speedups respectively, with **`0` short-loop regressions** across $N \in [4, 1024]$).

## Applicability

- **Extends:** `rustc-intrinsics-simd-and-arch-semantic-sources`, `x86-avx512-short-loop-regression-and-vector-width-profitability`, `hybridtrace-vectorization-slp-and-loop-certificate-library`, `rust-llvm-o3-loop-and-slp-vectorization-idiom-census`
- **Subjects and Scope:** Evaluated on Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `joshlf/anneal` (`d4ca2c861f664f200b69cdced9f6af38b5b1175a`) across `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, and `i686-unknown-linux-gnu`.

## Findings

### 1. Eight-Family Legalization and UB Precondition Taxonomy for All `81` `rustc 1.99.1` `simd_*` Intrinsics

**Basis: source + execution (`compiler/rustc_codegen_llvm/src/intrinsic.rs:2051-3405`, `library/core/src/intrinsics/simd/{mod,scalable}.rs`, `support/simd_81_legalization_matrix.json`)**

Table 1 partitions all `81` `simd_*` intrinsics (`75` in `simd/mod.rs`, `5` in `simd/scalable.rs`, and `1` `simd_shuffle_const_generic` in `rustc_codegen_llvm/src/intrinsic.rs:2170`) into eight semantic certificate families:

| Family ID & Certificate Schema | Count | Intrinsics Covered | Exact UB / Poison Precondition in `rustc 1.99.1` | $512 \to 256 \to 128$-Bit Legalization (`AVX2` / `NEON` / `i686 SSE2`) |
| :--- | ---: | :--- | :--- | :--- |
| **1. Lane-Wise ALU, Bitwise & Shifts** (`SplitVecCert + SimdLaneUBGuardCert`) | `22` | `simd_add`, `simd_sub`, `simd_mul`, `simd_div`, `simd_rem`, `simd_shl`, `simd_shr`, `simd_and`, `simd_or`, `simd_xor`, `simd_neg`, `simd_bswap`, `simd_bitreverse`, `simd_ctlz`, `simd_cttz`, `simd_ctpop`, `simd_funnel_shl`, `simd_funnel_shr`, `simd_carryless_mul`, `scalable::{simd_add, simd_sub, simd_neg}` | `simd_shl`/`simd_shr`: UB if any lane shift $\ge \text{bitwidth}$; `simd_div`/`rem`: UB if any lane divisor $= 0$ or signed `MIN / -1`; `ctlz`/`cttz` pass `is_zero_poison = false` | Recursive `Split2` (`2 × 256b` `ymm`) and `Split4` (`4 × 128b` `v0..v3` / `xmm0..xmm3`); `splitVec2_binop_sound` |
| **2. Saturating & Pointer Offset** (`SplitVecCert + GEPProvenanceCert`) | `3` | `simd_saturating_add`, `simd_saturating_sub`, `simd_arith_offset` | `@llvm.{s,u}{add,sub}.sat` is total; `simd_arith_offset` emits wrapping vector `getelementptr` (no `inbounds` UB) | `uqadd`/`sqadd` on `4 × v4i32` NEON; `paddusb`/`psubusb` or `icmp+select` on SSE2 |
| **3. Comparisons, Masks & Bitmasks** (`SplitVecCert + MaskReprCert`) | `9` | `simd_eq`, `simd_ne`, `simd_lt`, `simd_le`, `simd_gt`, `simd_ge`, `simd_select`, `simd_select_bitmask`, `simd_bitmask` | Comparisons return `-1` (`0xFF..FF`) or `0`; `simd_select` requires mask lanes $\in \{0, -1\}$ in CTFE/Miri; `simd_bitmask` reverses bit order on big-endian | `splitVec2_select_bitmask_sound`: splits $2W$-bit integer mask into `(mask & ((1<<W)-1), mask >> W)` |
| **4. Type Casts & Provenance** (`SplitVecCert + FloatToIntSatCert`) | `7` | `simd_as`, `simd_cast`, `simd_cast_ptr`, `simd_expose_provenance`, `simd_with_exposed_provenance`, `scalable::{simd_as, simd_cast}` | `simd_as` calls `@llvm.fptosi.sat` (clamps `NaN -> 0` and out-of-range to `MIN`/`MAX`), whereas `simd_cast` emits raw `fptosi` (**UB/poison** on `NaN` or out-of-range!) | Widening casts split output into `2x`/`4x` registers; narrowing casts pack register pairs (`xtn`/`packssdw`) |
| **5. Swizzles, Shuffles, Insert & Extract** (`CrossHalfShuffleCert`) | `5` | `simd_shuffle`, `simd_shuffle_const_generic`, `simd_insert`, `simd_extract`, `simd_splat` | `simd_insert`/`extract`: UB if index $\ge N$; `simd_shuffle` requires index operand to be a `#[repr(simd)]` `u32` vector (`E0511` if `[u32; M]` array is passed!) with lanes $< 2N$ | `splitVec2_shuffle_cross_half_sound`: lowers to `tbl v0.16b, {v0..v3}` on AArch64 and `vperm2i128` + `vpblendd` on `AVX2` |
| **6. Horizontal Reductions** (`OrderedSimdFoldCert + Schema 5`) | `11` | `simd_reduce_{add,mul}_{ordered,unordered}`, `simd_reduce_{min,max,and,or,xor,all,any}` | `_ordered` float reductions fold strictly left-to-right starting from `acc`; `_unordered` permits tree reduction | Ordered fold threads scalar `acc` sequentially across `Split4` chunks (`acc0 -> acc1 -> acc2 -> acc3`) |
| **7. Masked & Strided Memory** (`MaskedMemCert`) | `4` | `simd_masked_load`, `simd_masked_store`, `simd_gather`, `simd_scatter` | LLVM $\ge 22$ passes alignment via `align(N)` param attribute on ptr (`intrinsic.rs:2676-2692`); inactive lanes suppress faults (`simdMaskedLoad_inactive_lane_safe`) | Native `k`-mask EVEX on `AVX-512`; predicated lane-branch diamonds on `NEON` and `i686 SSE2` |
| **8. Floating-Point Vector Math** (`SplitVecCert + FloatContractCert`) | `20` | `simd_{fabs,fsqrt,ffloor,fceil,ftrunc,fround,fround_ties_even,fsin,fcos,fexp,fexp2,flog,flog2,flog10,fma,fmuladd,fpow,fpowi,minimum_number_nsz,maximum_number_nsz}` | `simd_fma` guarantees single rounding (`@llvm.fma`); `simd_fmuladd` permits fused or unfused (`@llvm.fmuladd`) | Vector `vsqrtps`/`fsqrt.4s` and `vfmadd213ps`/`fmla.4s`; scalarized libm calls for transcendentals without SVML |

---

### 2. Cross-Architecture Vector Cost Models (`Intel Skylake-X` vs. `AMD Zen 4/5` vs. `Arm Neoverse N2`)

**Basis: source + execution (`llvm/lib/Target/X86/X86TargetTransformInfo.cpp`, `llvm/lib/Target/AArch64/AArch64TargetTransformInfo.cpp`, `support/multi_arch_simd_cost_eval.py`, `support/target_simd_cost_models.json`)**

Table 2 compares the four microarchitectural profiles in `TargetSimdCostModel`:

| Parameter / Policy | `Intel_SkylakeX_CascadeLake` (`skylake-avx512`) | `AMD_Zen4_znver4` (`znver4`) | `AMD_Zen5_znver5` (`znver5`) | `Arm_Neoverse_N2_V2` (`neoverse-n2`) |
| :--- | :--- | :--- | :--- | :--- |
| **Default Autovec Register Width** | `256`-bit (`ymm`, `+prefer-256-bit`) | **`512`-bit (`zmm`, double-pumped 256b)** | **`512`-bit (`zmm`, native 512b ALU/FMA)** | `128`-bit NEON (`2 × 128b` pipes) / SVE2 |
| **Explicit `#[repr(simd)]` 512-Bit Lowering** | `1 × 512`-bit `zmm` (`9` `zmm` in probe) | `1 × 512`-bit `zmm` (`9` `zmm` in probe) | `1 × 512`-bit `zmm` (`9` `zmm` in probe) | **`Split4` (`4 × 128`-bit NEON `v0..v3`, `ldp`/`stp`)** |
| **512-Bit `zmm` Warmup / License Penalty** | **`28` cycles** (frequency downclock) | **`0` cycles** (no downclock) | **`0` cycles** (no downclock) | **`0` cycles** |
| **`vzeroupper` Transition Required** | **Yes** (`DirtyUpperState`) | **No** (`HasFastLZCNT` / zero upper stall) | **No** | N/A |
| **Gather (`vpgatherdd` / `ld1w`) Latency** | `42` cycles (GDS microcode penalty) | `26` cycles (still scalarized micro-ops) | `18` cycles | `12` cycles (SVE `ld1w`) |
| **Predicated Tail-Folding Policy** | Scalar epilogue default (`dont-fold-tail`) | **EVEX `k`-mask tail-folding (`min_trip=16`)** | **EVEX `k`-mask tail-folding (`min_trip=8`)** | **SVE `whilelo` tail-folding (`UF=1`)** |
| **Short-Loop Regressions ($N \in [4, 1024]$)** | **`0`** | **`0` (`+18.4%` over Skylake 256b cap)** | **`0` (`+64.2%` over AVX2)** | **`0`** |

## Boundaries

- **Overlapping Active Lanes in `simd_scatter`:** As proven in `simdScatter_disjoint_lanes_sound` (`support/lean/PortableSimdLegalization.lean`), `simd_scatter` writes commute and are target-independent when active mask lanes have pairwise distinct addresses (`addr1 ≠ addr2`). When two active lanes in a single `simd_scatter` call target the exact same memory address, LLVM IR defines the final stored value as ordered from lowest lane index to highest lane index, requiring sequential lane-order commitment in the memory model.
- **Non-Power-of-Two `#[repr(simd)]` Lengths in `rustc 1.99.1`:** While `#[repr(simd)]` in `rustc 1.99.1` supports arbitrary lane counts up to `64` (`Simd<T, N>`), LLVM legalizes non-power-of-two vectors (such as `Simd<f32, 3>`) by widening (`WidenVecCert`) to the next power of two (`<4 x float>`) with `undef`/`poison` padding in the inactive upper lanes and masking reductions/stores to the active $N$ lanes.

## Evidence

- **81-Intrinsic Probe, Matrix, and Multi-Arch Cost Evaluator (`support/`):**
  - `support/portable_simd_81_probe.rs`: `#![no_std]` `#[repr(simd)]` probe compiled across `x86_64` (`SSE2`, `AVX2`, `skylake-avx512`, `znver4`, `znver5`), `aarch64` (`+neon`), and `i686` (`+sse2`).
  - `support/multi_arch_simd_cost_eval.py`: Cross-target assembly analyzer and cost-model generator.
  - `support/simd_81_legalization_matrix.json` and `support/target_simd_cost_models.json`: Complete 81-intrinsic legalization table and 4-vendor microarchitectural cost parameters.
- **Lean `v4.34.1` Mechanization (`support/lean/`):**
  - `support/lean/PortableSimdLegalization.lean` and `support/lean/lakefile.lean`: Zero-`sorry`, zero-`native_decide` proofs of `splitVec2_binop_sound`, `splitVec2_select_bitmask_sound`, `splitVec2_shuffle_cross_half_sound`, `simdMaskedLoad_inactive_lane_safe`, `simdScatter_disjoint_lanes_sound`, `canary_simd_shl_over_bitwidth_ub`, and `canary_simd_cast_out_of_range_ub_vs_simd_as_saturates`.

## Revalidation

Run the cross-target legalization and cost-model script and Lean `v4.34.1` kernel check from the package directory:

```bash
python3 support/multi_arch_simd_cost_eval.py
anneal-lean-run --mode file --concurrency 4 -- lean support/lean/PortableSimdLegalization.lean
```

Confirm exit code `0`, `total_simd_intrinsics_cataloged == 81`, `regressions_observed_across_4_profiles == 0`, and axioms limited to `[propext, Quot.sound]`.
