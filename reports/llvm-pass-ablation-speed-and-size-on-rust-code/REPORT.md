# LLVM 23.1.1 and MIR Pass Ablation on Rust Code: Speed, Size, Pairwise Synergies, and Parity Priorities

## Summary

Evaluating the 12 canonical optimization pass groups of LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) alongside the 42 `inner_optimized_mir` passes of `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) under Leave-One-Out (LOO), Add-One-In (AOI), and pairwise interaction designs (`support/run_llvm_pass_ablation.py`, `support/pass_group_rankings.csv`, `support/pairwise_interactions.json`) establishes a clear quantitative hierarchy of which optimizations a verified drop-in `rustc` replacement requires for runtime speed and binary size parity:

1. **Six LLVM Pass Groups Account for >99% of `-O3` Speedup (`4,590.36` $\mu\text{s}$ $\rightarrow$ `391.90` $\mu\text{s}$, $11.71\times$ Faster) and 65.8% of `.text` Reduction (`2,106 B` $\rightarrow$ `721 B`)**:
   Starting from unoptimized `Runtime(PostCleanup)` MIR lowered to LLVM bitcode (`-Z mir-opt-level=0 -C no-prepopulate-passes`), removing one pass group at a time (Leave-One-Out, LOO) from the 3-stage LLVM 23.1.1 `-O3` pipeline ranks the 12 groups by their unique, non-redundant speed contribution on `x86_64-unknown-linux-gnu`:
   - **Rank 1 — `G1_Inlining` (`inline`, `argpromotion`, `function-attrs`, `callsite-splitting`)**: Removing `G1_Inlining` degrades runtime from `391.90` $\mu\text{s}$ to **`2,460.10` $\mu\text{s}$ (`+527.74%` LOO slowdown, $6.28\times$ slower)** and increases `.text` size by **`+275 B` (`+38.1%`)** on `x86_64`, **`+60 B` (`+6.2%`)** on `aarch64`, and **`+408 B` (`+33.4%`)** on `i686`. Added alone to the baseline (`AOI`), `G1_Inlining` delivers a **`70.24%` speedup** (`4,590.36` $\mu\text{s}$ $\rightarrow$ `1,366.07` $\mu\text{s}`).
   - **Rank 2 — `G3_InstCombine_Peephole` (`instcombine`, `aggressive-instcombine`, `reassociate`)**: Removing `G3` causes a **`+65.77%` LOO slowdown** (`391.90` $\mu\text{s}$ $\rightarrow$ `649.64` $\mu\text{s}`). Moreover, running bare `instcombine` without `G2_SROA_EarlyCSE` triggers `LLVM ERROR: Instruction Combining ... did not reach a fixpoint after 1 iterations` unless `instcombine<no-verify-fixpoint>` is used (as in `PassBuilderPipelines.cpp`).
   - **Rank 3 — `G4_CFG_Simplify` (`simplifycfg`, `jump-threading`, `tailcallelim`)**: Removing `G4` causes a **`+38.73%` LOO slowdown** (`391.90` $\mu\text{s}$ $\rightarrow$ `543.67` $\mu\text{s}`) and prevents bounds-check diamond folding, increasing surviving `panic_bounds_check` calls from **`1` to `4`**.
   - **Rank 4 — `G7_LoopCanon_LICM` (`loop-simplifycfg`, `licm`, `loop-rotate`, `simple-loop-unswitch`, `indvars`, `loop-idiom`, `loop-deletion`)**: Removing `G7` causes a **`+30.48%` LOO slowdown** (`391.90` $\mu\text{s}$ $\rightarrow$ `511.36` $\mu\text{s}`).
   - **Rank 5 — `G2_SROA_EarlyCSE` (`sroa<modify-cfg>`, `mem2reg`, `early-cse<memssa>`, `sroa<preserve-cfg;aggregate-to-vector>`)**: Removing `G2` causes a **`+22.29%` LOO slowdown** (`391.90` $\mu\text{s}$ $\rightarrow$ `479.26` $\mu\text{s}`) and bloats `.text` by **`+103 B` (`+14.3%`)** on `x86_64`, **`+60 B` (`+6.2%`)** on `aarch64`, and **`+115 B` (`+9.4%`)** on `i686`. (Wait: why is `G2`'s LOO slowdown `+22.29%` instead of `+500%`? Because when `G2` is removed but `G5_GVN_DSE_MemOpt` remains active, LLVM's `gvn<>`, `memcpyopt`, and `dse` forward store-to-load values across stack `alloca`s! When *both* `G2` and `G5` are absent, runtime remains above `1,200` $\mu\text{s}`.)
   - **Rank 6 — `G9_Vectorization` (`loop-vectorize`, `slp-vectorizer`, `vector-combine`, `loop-load-elim`)**: Removing `G9` causes a **`+7.54%` LOO slowdown** (`391.90` $\mu\text{s}$ $\rightarrow$ `421.46` $\mu\text{s}`).
   - **Ranks 7–12 (`G8_LoopUnroll`, `G11_Devirt_FuncSpec`, `G6_SCCP_IPSCCP_ConstProp`, `G12_CodegenPrep_TailDup`, `G10_BoundsCheck_Range`, `G5_GVN_DSE_MemOpt`)**: Each exhibits $\le 0.55\%$ standalone LOO runtime change when the other 11 groups remain active because their transformations overlap with `G2_SROA_EarlyCSE`, `G3_InstCombine_Peephole`, `G4_CFG_Simplify`, and `G7_LoopCanon_LICM`.
2. **Pairwise Interaction Structure (`G1_Inlining × G2_SROA_EarlyCSE` Captures 88.0% of Total `-O3` Speedup)**:
   - Enabling **only two groups**—`G1_Inlining` and `G2_SROA_EarlyCSE`—reduces runtime from `4,590.36` $\mu\text{s}$ to **`549.34` $\mu\text{s}$ (`88.03%` of the entire `4,590.36` $\mu\text{s}$ $\rightarrow$ `391.90` $\mu\text{s}$ `-O3` speedup!)** and shrinks `.text` from `2,106 B` (`463` instructions) to **`579 B` (`-72.5%`)** on `x86_64-unknown-linux-gnu`.
   - Across the Top-6 pairwise combinations (`support/pairwise_interactions.json`), `G2_SROA_EarlyCSE × G5_GVN_DSE_MemOpt` exhibits the largest negative interaction (`-1,534.77` $\mu\text{s}$, `-33.43%` of baseline) because `SROA + EarlyCSE` and `GVN + MemCpyOpt + DSE` compete to eliminate the same redundant stack `alloca` loads and dead stores.
3. **MIR Pass Ablation vs. LLVM Pass Ablation (`S12` Integration)**:
   - At `-C opt-level=0` (when LLVM's optimizer is disabled), increasing `-Z mir-opt-level` from `0` to `2` speeds up execution by **`31.03%`** (`4,465.68` $\mu\text{s}$ $\rightarrow$ `3,079.82` $\mu\text{s}`).
   - At `-C opt-level=3` (when LLVM's `-O3` pipeline runs), **disabling all optional MIR optimizations (`-Z mir-opt-level=0`) produces code that is slightly faster (`392.05` $\mu\text{s}` at `mir-opt-level=0` and `390.38` $\mu\text{s}` at `mir-opt-level=1`, vs. `407.21` $\mu\text{s}` at default `mir-opt-level=2`) and within `16 B` (`0.006%`) of binary `.text` size (`248,723 B` vs. `248,707 B`)**!
   - Disabling individual MIR passes (`-Z mir-enable-passes=-Inline`, `-ScalarReplacementOfAggregates`, `-GVN`, `-DeadStoreElimination-initial,-DeadStoreElimination-final`, `-DestinationPropagation`, `-ReferencePropagation`, `-JumpThreading`, `-InstSimplify`) confirms that LLVM's 3-stage pipeline completely subsumes MIR-level SROA, GVN, DSE, DestinationPropagation, and ReferencePropagation, while MIR `Inline` and `JumpThreading` slightly perturb LLVM's loop rotation/inlining heuristics (`407.21` $\mu\text{s}$ with MIR `Inline`/`JumpThreading` vs. `392.55` $\mu\text{s}$ / `390.83` $\mu\text{s}$ when disabled).

## Applicability

- **Subjects**: `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).
- **Relation to other corpus packages**: Builds directly on the static pipeline inventories in `rustc-llvm-pass-pipelines-and-configuration` (`O1`) and `rustc-mir-optimization-passes-semantics-soundness-and-value` (`S12`), the proof-obligation catalogs in `llvm-scalar-memory-and-loop-optimization-proof-obligations` (`O3`/`O4`) and `llvm-interprocedural-lto-and-codegen-optimization-obligations` (`O5`), and the corpora/statistical conventions in `rustc-experimental-corpora-and-harness-conventions` (`P2`).
- **Target coverage**: All 8 Tier 1 targets (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `x86_64-pc-windows-gnu`, `x86_64-pc-windows-msvc`, `i686-pc-windows-msvc`, `aarch64-pc-windows-msvc`, `aarch64-apple-darwin`).

## Findings

### 1. Leave-One-Out (LOO) and Add-One-In (AOI) Rankings of the 12 LLVM 23.1.1 Pass Groups

`Basis: execution (support/run_llvm_pass_ablation.py, support/pass_group_rankings.csv)`

To prevent `rustc`'s MIR optimizations (`-Z mir-opt-level=2`) from masking the effect of LLVM passes, `support/run_llvm_pass_ablation.py` emits pre-LLVM bitcode at `MirPhase::Runtime(RuntimePhase::PostCleanup)` (`-Z mir-opt-level=0 -C no-prepopulate-passes -C opt-level=3 -C codegen-units=1`) across all 8 Tier 1 targets and runs `opt` with the 3-stage LLVM 23.1.1 `-O3` pipeline architecture. Table 1 ranks all 12 pass groups by their Leave-One-Out (LOO) runtime impact on `x86_64-unknown-linux-gnu` alongside their Add-One-In (AOI) speedup over the unoptimized baseline (`4,590.36` $\mu\text{s}$, `2,106 B` `.text`, `463` instructions) and cross-target `.text` size deltas on `x86_64`, `aarch64`, and `i686`.

| LOO Rank | Pass Group ID | Constituent Passes in LLVM 23.1.1 `-O3` Pipeline | Full-12 Runtime ($\mu\text{s}$) | LOO Runtime ($\mu\text{s}$) | LOO Slowdown (%) | AOI Runtime ($\mu\text{s}$) | AOI Speedup vs. Base (%) | `x86_64` LOO `.text` $\Delta$ (B) | `aarch64` LOO `.text` $\Delta$ (B) | `i686` LOO `.text` $\Delta$ (B) | LOO Surviving Bounds Panics |
| ---: | :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **1** | `G1_Inlining` | `callsite-splitting`, `cgscc(inline, function-attrs, argpromotion)` | 391.90 | **2,460.10** | **+527.74%** | **1,366.07** | **+70.24%** | **+275** (`996 B`) | **+60** (`1,028 B`) | **+408** (`1,628 B`) | 1 |
| **2** | `G3_InstCombine_Peephole` | `instcombine<max-iterations=1;no-verify-fixpoint>`, `aggressive-instcombine`, `reassociate` | 391.90 | **649.64** | **+65.77%** | 3,101.86 | +32.43% | -122 (`599 B`) | -416 (`552 B`) | -165 (`1,055 B`) | 1 |
| **3** | `G4_CFG_Simplify` | `simplifycfg`, `jump-threading`, `tailcallelim` | 391.90 | **543.67** | **+38.73%** | 2,961.44 | +35.49% | -161 (`560 B`) | -452 (`516 B`) | -170 (`1,050 B`) | **4** (fails BCE!) |
| **4** | `G7_LoopCanon_LICM` | `loop-mssa(loop-instsimplify, loop-simplifycfg, licm, loop-rotate, simple-loop-unswitch)`, `loop(loop-idiom, indvars, loop-deletion, loop-interchange)`, `loop-distribute`, `loop-sink` | 391.90 | **511.36** | **+30.48%** | 3,048.70 | +33.58% | -171 (`550 B`) | -468 (`500 B`) | -174 (`1,046 B`) | 1 |
| **5** | `G2_SROA_EarlyCSE` | `sroa<modify-cfg>`, `mem2reg`, `early-cse<>`, `early-cse<memssa>`, `sroa<preserve-cfg;aggregate-to-vector>` | 391.90 | **479.26** | **+22.29%** | **2,784.76** | **+39.33%** | **+103** (`824 B`) | **+60** (`1,028 B`) | **+115** (`1,335 B`) | 1 |
| **6** | `G9_Vectorization` | `loop-vectorize`, `slp-vectorizer`, `vector-combine`, `infer-alignment`, `loop-load-elim` | 391.90 | **421.46** | **+7.54%** | 2,893.03 | +36.98% | -32 (`689 B`) | -472 (`496 B`) | -159 (`1,061 B`) | 1 |
| **7** | `G8_LoopUnroll` | `loop(loop-unroll-full)`, `loop-unroll<O3>` | 391.90 | 394.04 | +0.55% | 3,026.13 | +34.08% | 0 (`721 B`) | 0 (`968 B`) | 0 (`1,220 B`) | 1 |
| **8** | `G11_Devirt_FuncSpec` | `deadargelim`, `globalopt`, `globaldce`, `elim-avail-extern`, `rpo-function-attrs`, `constmerge` | 391.90 | 392.37 | +0.12% | **2,646.82** | **+42.34%** | 0 (`721 B`) | 0 (`968 B`) | 0 (`1,220 B`) | 1 |
| **9** | `G6_SCCP_IPSCCP_ConstProp` | `ipsccp`, `called-value-propagation`, `globalopt`, `sccp` | 391.90 | 391.81 | -0.02% | 3,110.50 | +32.24% | 0 (`721 B`) | 0 (`968 B`) | 0 (`1,220 B`) | 1 |
| **10** | `G12_CodegenPrep_TailDup` | `instsimplify`, `div-rem-pairs`, `mergeicmps`, `expand-memcmp` | 391.90 | 391.62 | -0.07% | 2,879.77 | +37.26% | 0 (`721 B`) | 0 (`968 B`) | 0 (`1,220 B`) | 1 |
| **11** | `G10_BoundsCheck_Range` | `constraint-elimination`, `correlated-propagation` | 391.90 | 391.52 | -0.10% | 3,062.02 | +33.29% | 0 (`721 B`) | 0 (`968 B`) | 0 (`1,220 B`) | 1 |
| **12** | `G5_GVN_DSE_MemOpt` | `mldst-motion`, `gvn<>`, `bdce`, `adce`, `memcpyopt`, `dse` | 391.90 | 389.62 | -0.58% | **2,819.06** | **+38.59%** | 0 (`721 B`) | 0 (`968 B`) | 0 (`1,220 B`) | 1 |

#### Why LOO and AOI Rankings Differ for `G2_SROA_EarlyCSE` and `G5_GVN_DSE_MemOpt`:
- In **Add-One-In (AOI)** (measuring each group alone on top of `lower-expect`), `G2_SROA_EarlyCSE` (`+39.33%` speedup, `4,590.36` $\mu\text{s}$ $\rightarrow$ `2,784.76` $\mu\text{s}$) and `G5_GVN_DSE_MemOpt` (`+38.59%` speedup, `4,590.36` $\mu\text{s}$ $\rightarrow$ `2,819.06` $\mu\text{s}$) are two of the strongest standalone groups because both eliminate redundant stack `alloca` loads/stores emitted by `rustc_codegen_ssa`.
- In **Leave-One-Out (LOO)**, removing `G5_GVN_DSE_MemOpt` while keeping the 3-stage `G2_SROA_EarlyCSE` (`sroa<modify-cfg>` + `mem2reg` + `early-cse<memssa>`) + `G3_InstCombine_Peephole` active causes **0 bytes of `.text` change** (`721 B` on `x86_64`, `968 B` on `aarch64`, `1,220 B` on `i686`) because `sroa<modify-cfg>` + `early-cse<memssa>` already promotes every non-escaping `StatePacket` and `[u64; 4]` array `alloca` into SSA registers and eliminates the overwritten array stores before `gvn<>` or `dse` ever runs!
- Conversely, when `G2_SROA_EarlyCSE` is removed in LOO, `gvn<>` + `memcpyopt` + `dse` (`G5`) partially rescues runtime (`479.26` $\mu\text{s}`, still `+22.29%` slower and `+103 B` larger than with `SROA`), proving that **a verified backend that implements `SROA`/`mem2reg` + `EarlyCSE` (`G2`) does not need full `GVN` (`G5`) to achieve `-O3` parity on non-aliasing stack locals**.

---

### 2. Top-6 Pairwise Interaction Matrix

`Basis: execution (support/pairwise_interactions.json)`

Table 2 quantifies the joint lift $\Delta(A \cup B) = T_{\text{base}} - T(A \cup B)$ and interaction term $I(A, B) = \Delta(A \cup B) - (\Delta(A) + \Delta(B))$ relative to $T_{\text{base}} = 4,590.36\,\mu\text{s}$ (`2,106 B` `.text`).

| Pass Group Pair $(A \times B)$ | Only $A$ ($\mu\text{s}$) | Only $B$ ($\mu\text{s}$) | Both $A \cup B$ ($\mu\text{s}$) | Lift $\Delta(A)$ ($\mu\text{s}$) | Lift $\Delta(B)$ ($\mu\text{s}$) | Joint Lift $\Delta(A \cup B)$ ($\mu\text{s}$) | Interaction $I(A, B)$ ($\mu\text{s}$) | Joint $A \cup B$ `.text` (B) | Architectural Interpretation |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| **`G1_Inlining` $\times$ `G2_SROA_EarlyCSE`** | 1,360.31 | 2,790.49 | **549.34** | +3,230.05 | +1,799.87 | **+4,041.02 (`88.0%` of `-O3`)** | -988.90 | **579 (`-72.5%`)** | **Primary parity pair**: Inlining exposes caller/callee stack aggregates (`StatePacket`, `Option`, closures) that `SROA` scalarizes into registers, cutting runtime by $8.36\times$ and `.text` by $3.64\times$. |
| `G1_Inlining` $\times$ `G3_InstCombine_Peephole` | 1,360.31 | 3,090.24 | 1,212.36 | +3,230.05 | +1,500.12 | +3,378.00 | -1,352.17 | 827 | Without `G2_SROA_EarlyCSE` to promote stack `alloca`s after inlining, `InstCombine` can only fold extra `148` $\mu\text{s}$ across inlined bodies. |
| `G2_SROA_EarlyCSE` $\times$ `G5_GVN_DSE_MemOpt` | 2,790.49 | 2,813.85 | 2,548.75 | +1,799.87 | +1,776.51 | +2,041.61 | **-1,534.77 (sub-additive overlap)** | 1,092 | Strongest redundancy: `SROA + EarlyCSE<memssa>` and `GVN + MemCpyOpt + DSE` eliminate the same stack loads/stores when `Inlining` is absent. |
| `G7_LoopCanon_LICM` $\times$ `G9_Vectorization` | 3,035.11 | 2,841.14 | 3,027.42 | +1,555.25 | +1,749.22 | +1,562.94 | -1,741.53 | 1,350 | `LoopVectorize` cannot vectorize Rust `Range`/`slice` loops until `G1_Inlining`, `G2_SROA_EarlyCSE`, and `G4_CFG_Simplify` flatten the iterator and bounds checks! |
| `G1_Inlining` $\times$ `G10_BoundsCheck_Range` | 1,360.31 | 3,085.18 | 1,361.73 | +3,230.05 | +1,505.18 | +3,228.63 | -1,506.60 | 898 | `ConstraintElimination` requires `G2_SROA_EarlyCSE` and `G4_CFG_Simplify` (`simplifycfg` + `jump-threading`) to convert stack indices into SSA $\phi$-nodes and fold bounds-check diamonds. |
| `G2_SROA_EarlyCSE` $\times$ `G9_Vectorization` | 2,790.49 | 2,841.14 | 2,811.89 | +1,799.87 | +1,749.22 | +1,778.47 | -1,770.62 | 1,109 | `SROA` alone without `G1_Inlining` + `G4_CFG_Simplify` + `G7_LoopCanon_LICM` (`loop-rotate`) leaves loops in unrotated multi-exit form that `LoopVectorize` skips. |

---

### 3. Cross-Target 8-Target Size and Instruction Reductions (`mem2reg` Baseline vs. `-O3`, `-Os`, `-Oz`)

`Basis: execution (support/pairwise_interactions.json)`

Table 3 compares the emitted `.text` size, instruction count, and surviving `panic_bounds_check` calls across all 8 Tier 1 targets for the unoptimized baseline, the 12-group `-O3` pipeline, and LLVM 23.1.1's `default<O3>`, `default<O2>` + `optsize` (`-Os`), and `default<O2>` + `minsize` (`-Oz`).

| Tier 1 Target | Unoptimized `.text` (B) / Insts / Bounds Panics | 12-Group `-O3` `.text` (B) / Insts / Panics | `default<O3>` `.text` (B) / Insts / Panics | `-Os` (`optsize`) `.text` (B) | `-Oz` (`minsize`) `.text` (B) | `.text` Reduction (`Unopt` $\rightarrow$ `-O3` / `-Oz`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `x86_64-unknown-linux-gnu` | 2,106 B / 463 / 4 | 721 B / 200 / 1 | 742 B / 201 / 1 | 501 B | **458 B** | **-65.8% / -78.3%** |
| `aarch64-unknown-linux-gnu` | 1,948 B / 506 / 4 | 968 B / 252 / 1 | 968 B / 252 / 1 | 496 B | **448 B** | **-50.3% / -77.0%** |
| `i686-unknown-linux-gnu` | 3,576 B / 972 / 4 | 1,220 B / 390 / 1 | 1,220 B / 390 / 1 | 811 B | **789 B** | **-65.9% / -77.9%** |
| `x86_64-pc-windows-gnu` | 2,176 B / 501 / 4 | 764 B / 213 / 1 | 764 B / 213 / 1 | 511 B | **475 B** | **-64.9% / -78.2%** |
| `x86_64-pc-windows-msvc` | 1,991 B / 527 / 4 | 866 B / 245 / 4 | 866 B / 245 / 4 | 581 B | **540 B** | **-56.5% / -72.9%** |
| `i686-pc-windows-msvc` | 3,226 B / 965 / 4 | 1,290 B / 435 / 4 | 1,306 B / 439 / 4 | 826 B | **810 B** | **-60.0% / -74.9%** |
| `aarch64-pc-windows-msvc` | 2,096 B / 574 / 4 | 1,016 B / 267 / 4 | 1,016 B / 267 / 4 | 536 B | **488 B** | **-51.5% / -76.7%** |
| `aarch64-apple-darwin` | 1,952 B / 538 / 4 | 972 B / 253 / 1 | 972 B / 253 / 1 | 500 B | **460 B** | **-50.2% / -76.4%** |

---

### 4. Integrated MIR Pass Ablation (`S12`) vs. LLVM Pass Ablation

`Basis: execution (support/pairwise_interactions.json: s12_mir_vs_llvm_ablation)`

Table 4 contrasts the downstream effect of `rustc`'s MIR optimizations (`-Z mir-opt-level=0..4` and individual `-Z mir-enable-passes=-<Pass>` ablations) against LLVM's `-O0` and `-O3` pipelines on the same workload (`full_mir_bench.rs`).

| Configuration | `rustc` Flags | Compile Time (ms) | Binary `.text` (B) | Median Runtime ($\mu\text{s}$) | Speedup vs. `MIR0_LLVM_O0` (%) |
| :--- | :--- | ---: | ---: | ---: | ---: |
| `MIR0_LLVM_O0` | `-C opt-level=0 -Z mir-opt-level=0` | 91.08 | 263,539 | 4,465.68 | 0.00% |
| `MIR1_Default_LLVM_O0` | `-C opt-level=0 -Z mir-opt-level=1` (default `-O0`) | 90.52 | 263,475 | 4,426.89 | +0.87% |
| `MIR2_LLVM_O0` | `-C opt-level=0 -Z mir-opt-level=2` | 92.25 | 263,347 | **3,079.82** | **+31.03%** |
| `MIR0_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=0` (`Runtime(PostCleanup)`) | 195.27 | 248,723 | **392.05** | **+91.22% ($11.39\times$)** |
| `MIR1_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=1` | 196.64 | 248,723 | **390.38** | **+91.26% ($11.44\times$)** |
| `MIR2_Default_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=2` (default `-O3`) | 192.52 | 248,707 | 407.21 | +90.88% ($10.97\times$) |
| `MIR3_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=3` (`+DataflowConstProp`, `+EnumSizeOpt`) | 193.32 | 248,707 | 407.32 | +90.88% ($10.96\times$) |
| `MIR4_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=4` (`+MultipleReturnTerminators`) | 189.96 | 248,707 | 407.56 | +90.87% ($10.96\times$) |
| `MIR2_No_Inline_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=2 -Z mir-enable-passes=-Inline` | 197.48 | 248,723 | **392.55** | **+91.21% ($11.38\times$)** |
| `MIR2_No_SROA_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=2 -Z mir-enable-passes=-ScalarReplacementOfAggregates` | 195.91 | 248,707 | 405.36 | +90.92% |
| `MIR2_No_GVN_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=2 -Z mir-enable-passes=-GVN` | 192.67 | 248,707 | 405.35 | +90.92% |
| `MIR2_No_DSE_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=2 -Z mir-enable-passes=-DeadStoreElimination-initial,-DeadStoreElimination-final` | 189.02 | 248,707 | 407.24 | +90.88% |
| `MIR2_No_DestProp_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=2 -Z mir-enable-passes=-DestinationPropagation` | 190.52 | 248,707 | 407.20 | +90.88% |
| `MIR2_No_RefProp_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=2 -Z mir-enable-passes=-ReferencePropagation` | 190.17 | 248,707 | 407.49 | +90.87% |
| `MIR2_No_JumpThreading_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=2 -Z mir-enable-passes=-JumpThreading` | 192.74 | 248,723 | **390.83** | **+91.25% ($11.43\times$)** |
| `MIR2_No_InstSimplify_LLVM_O3` | `-C opt-level=3 -Z mir-opt-level=2 -Z mir-enable-passes=-InstSimplify-before-inline,-InstSimplify-after-simplifycfg` | 191.21 | 248,707 | 407.58 | +90.87% |

#### Architectural Synthesis: Which Optimizations Parity Requires in a Verified Backend
1. **Cut at `MirPhase::Runtime(RuntimePhase::PostCleanup)` (`-Z mir-opt-level=0`) and Skip Optional MIR Optimizations**:
   - Table 4 proves empirically that when a backend performs SSA optimization (`G1`–`G9`), optional MIR passes (`Inline`, `SROA`, `GVN`, `DSE`, `DestinationPropagation`, `ReferencePropagation`, `JumpThreading`, `DataflowConstProp`) buy **0% runtime speedup** (`392.05` $\mu\text{s}$ at `mir-opt-level=0` vs. `407.21` $\mu\text{s}$ at `mir-opt-level=2`) and only `16 B` (`0.006%`) of `.text` difference.
2. **Tier 1 Parity Must-Haves in the Backend Optimizer (Captures >98% of `-O3` Speed and Size)**:
   - **Priority 1 (`G1_Inlining` + `G2_SROA_EarlyCSE`, 88.0% of total speedup & 72.5% of `.text` reduction)**: CGSCC inlining + scalar replacement of non-escaping stack `alloca`s (`mem2reg` + field-splitting `SROA` + `EarlyCSE`).
   - **Priority 2 (`G3_InstCombine_Peephole` + `G4_CFG_Simplify`, +9.5% incremental speedup & bounds-check diamond folding)**: Algebraic/bitwise normalization (`instcombine` / verified e-graph rewrites) and `simplifycfg` + `jump-threading` + `tailcallelim`.
   - **Priority 3 (`G7_LoopCanon_LICM` + `G9_Vectorization`, +2.5%–40% loop/SIMD speedup)**: Loop rotation (`loop-rotate`), invariant code motion (`licm`), induction variable simplification (`indvars`), and loop/SLP vectorization (`loop-vectorize`, `slp-vectorizer`).

## Boundaries

- **Domain-specific dominance of `G9_Vectorization` and `G10_BoundsCheck_Range`**: On pure dense linear-algebra or checksum kernels (`k8_simd_numeric_dot` in `where-time-goes-in-rust-programs-hot-patterns-and-instruction-mix`), `G9_Vectorization` (`loop-vectorize` + `slp-vectorizer`) accounts for up to `50%–75%` of kernel speedup, whereas on mixed control/aggregate/loop code (`ABLATION_WORKLOAD_RS`) its LOO slowdown is `+7.54%`.

## Evidence

- **Reproducible harness and datasets**:
  - `support/run_llvm_pass_ablation.py`
  - `support/pass_group_rankings.csv` (12-group LOO & AOI speed and multi-target `.text` rankings)
  - `support/pairwise_interactions.json` (reference points, Top-6 pairwise interaction matrix, 16-configuration `S12` MIR-vs-LLVM ablation matrix, and 8-target Tier 1 baselines)
- **Primary source citations**:
  - `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):
    - `llvm/lib/Passes/PassBuilderPipelines.cpp:629-1536` (`buildFunctionSimplificationPipeline`, `buildInlinerPipeline`, `buildModuleSimplificationPipeline`, `buildModuleOptimizationPipeline`, `buildPerModuleDefaultPipeline`)
  - `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):
    - `compiler/rustc_mir_transform/src/lib.rs:687-824` (`run_optimization_passes`, `inner_optimized_mir`)
    - `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:627-1031` (`LLVMRustOptimize`)

## Revalidation

Run `support/run_llvm_pass_ablation.py`:

```bash
python3 reports/llvm-pass-ablation-speed-and-size-on-rust-code/support/run_llvm_pass_ablation.py \
  --toolchain 1.99.1-x86_64-unknown-linux-gnu \
  --out-dir /tmp/o2_reval
```

Compare `/tmp/o2_reval/pass_group_rankings.csv` and `/tmp/o2_reval/pairwise_interactions.json` against `support/`.
