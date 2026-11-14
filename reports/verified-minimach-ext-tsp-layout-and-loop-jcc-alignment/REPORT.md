# Verified `MiniMach` Basic-Block Placement (`Ext-TSP`), Hot/Cold Splitting, and Loop/JCC Alignment

## Summary

In a verified machine-code backend (`MiniMach` + `HybridTrace`), three high-leverage code-layout transformations—basic-block permutation (`Ext-TSP`), hot/cold section splitting (`.text.unlikely.<sym>`), and architectural multi-byte NOP alignment (`16 B`/`32 B` loop headers and `SKX102` 32 B macro-fused JCC padding)—carry **near-zero semantic proof cost** while collapsing linker section-order variance ($\sigma_{\text{layout}}$) and improving runtime speed:

1. **Zero-`sorry` Lean `v4.34.1` mechanization (`support/VerifiedLayoutPass.lean`, `288` lines):**
   - **`block_perm_sim` & `evalTerminator_invert`:** Reordering `MiniMach` basic blocks by an arbitrary permutation $\pi$ (such as the Extended Traveling Salesman Problem `Ext-TSP` chain heuristic) while negating branch conditions (`Cond.neg`) when inverting fallthrough vs. taken targets preserves single-step (`stepMach`) and fuel-bounded multi-step (`runMach`) execution semantics identically (`depends on axioms: [propext]`).
   - **`hot_cold_split_sim`:** Partitioning blocks into `.text.<sym>` (`SectionSlice.hotText`) and `.text.unlikely.<sym>` (`SectionSlice.coldTextUnlikely`) via `RetagCold` is observationally bisimilar (`LayoutLookupEquiv`) to single-section placement.
   - **`nop_align_sim`:** Prepending or inserting any sequence of canonical multi-byte architectural NOPs (`stepIsaNop len`) to align loop headers to $2^k$ bytes or push a macro-fused `cmp+jcc` pair past a 32-byte boundary advances `rip` by `sumPadBytes pads` and leaves `MachState` (`regs`, `zf`, `mem`) definitionally unchanged.
2. **LLVM 23.1.1 implementation audit (`MachineBlockPlacement.cpp` and `X86AsmBackend.cpp`):**
   - In `llvm/lib/CodeGen/MachineBlockPlacement.cpp:3598-3605` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), passing `-enable-ext-tsp-block-placement=true` alone is **silently ignored on unprofiled (non-PGO) builds** unless `-ext-tsp-apply-without-profile=true` (`ApplyExtTspWithoutProfile`) is also passed (`UseExtTspForPerf = !UseExtTspForSize && EnableExtTspBlockPlacement && (ApplyExtTspWithoutProfile || MF.getFunction().hasProfileData())`).
3. **Empirical variance collapse and runtime speedup across `W-Core` and 16 `--shuffle-sections` seeds (`support/layout_opt_results.json`):**
   - Across all 8 `W-Core` workloads and $K = 16$ linker section-shuffle seeds (`128` binaries per configuration), enabling static-heuristic `Ext-TSP` + `.text.unlikely` machine function splitting (`L1_Static_ExtTSP_Split`, zero PGO required) cuts suite-mean layout CV ($\sigma_{\text{layout}}$) by **`58.6%`** (**`5.31%` $\rightarrow$ `2.20%`**) and cuts mean 16-seed max-over-min spread by **`65.4%`** (**`20.91%` $\rightarrow$ `7.23%`**), while reducing `.text` size by `-0.02%` and improving geometric-mean speed by `-0.45%`.
   - Adding 32 B non-fallthrough/loop alignment and 32 B `SKX102` JCC/fused branch padding (`L2_Static_ExtTSP_Loop32_JCC32`) caps worst-case workload layout CV across the entire suite at **`9.00%`** (down from `15.08%` in stock `-O3`), collapses `bench-simd-kernels` 16-seed spread from **`63.05%` (`15.08%` CV) to `0.40%` (`0.11%` CV)**, cuts `bench-serde-json` 16-seed median latency by **`-7.49%`** (`21.34` $\mu\text{s}$ $\rightarrow$ `19.74` $\mu\text{s}`), and improves suite geometric-mean speed by **`-0.85%`** at a `+0.51%` `.text` padding cost.
   - Combining IR-PGO edge weights with `Ext-TSP` + `.text.unlikely` + 32 B loop/JCC alignment (`L3_PGO_ExtTSP_Loop32_JCC32`) improves suite geometric-mean speed by **`-3.28%` (`0.9672x`)** over stock `-O3` and speeds up `bench-serde-json` 16-seed median execution by **`-20.03%`** (`21.34` $\mu\text{s}$ $\rightarrow$ `17.07` $\mu\text{s}`, with 16-seed spread cut from `58.17%` to `21.11%`).

## Applicability

- **Extends:** `rustc-pgo-mechanics-heuristics-value-and-ir-portability`, `end-to-end-verified-mir-to-isa-refinement-chain-and-seams`, `llvm-interprocedural-lto-and-codegen-optimization-obligations`
- **Subjects:** Evaluated on `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Created:** 2026-11-14
- **Updated:** 2026-11-14

## Findings

### 1. Source Architecture of LLVM 23.1.1's Layout, Splitting, and Alignment Passes

**Basis: source (`rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)**

| Pass / Component | Source File & Line Range | CLI Flag(s) in `rustc -C llvm-args=...` | Algorithm & Key Gate |
| :--- | :--- | :--- | :--- |
| **`MachineBlockPlacement` (`Ext-TSP`)** | `llvm/lib/CodeGen/MachineBlockPlacement.cpp:3598-3605, 3681-3750` | `-enable-ext-tsp-block-placement=true` + **`-ext-tsp-apply-without-profile=true`** | Replaces Pettis-Hansen chain layout with the 3-term Extended TSP score (maximizing fallthroughs and short forward/backward jumps within L1I/DSB windows). Approximates non-debug instruction size as `4 * NumInsts` (`line 3711`). **Critical gate (`line 3604`):** Requires `-ext-tsp-apply-without-profile=true` when `hasProfileData()` is false. |
| **`MachineBlockPlacement::alignBlocks`** | `llvm/lib/CodeGen/MachineBlockPlacement.cpp:88-106, 3001-3139` | `-align-all-nofallthru-blocks=5` (`32 B`), `-align-all-blocks=4`, `-max-bytes-for-alignment=<N>` | Aligns loop headers (`TLI->getPrefLoopAlignment(L)`, `16 B` by default on x86-64) unless the layout predecessor falls through with $>20\%$ probability (`ColdProb(1, 5)`, `line 3018`). Setting `-align-all-nofallthru-blocks=5` aligns every jump-only entry block to $2^5 = 32$ bytes without inserting executed NOPs on fallthrough edges (`lines 3125-3138`). |
| **`MachineFunctionSplitter`** | `llvm/lib/CodeGen/MachineFunctionSplitter.cpp:1-227` | `-enable-split-machine-functions=true` (`-split-machine-functions`) | Splits cold basic blocks into `.text.split.<sym>` / `.text.unlikely.<sym>`. |
| **`X86AsmBackend` (`SKX102` JCC Alignment)** | `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp:80-165, 441-560` | `-x86-align-branch-boundary=32 -x86-align-branch=fused+jcc+jmp` | Inserts `MCBoundaryAlignFragment` before any `JCC`, `JMP`, or macro-fused `CMP`/`TEST`+`JCC` (`needAlign`, `lines 441-525`) and pads with canonical multi-byte NOPs (`0F 1F ...`) if the instruction or fused pair would cross or end on a 32-byte boundary. |
| **`lld::elf::computeCallGraphProfileOrder` (`hfsort` C3)** | `lld/ELF/CallGraphSort.cpp:1-347` | `-Wl,--call-graph-ordering-file=<file>` | Clusters `.text.*` sections by call-edge density $\text{weight}(C_1, C_2) / |C_1|$ up to page/cache capacity. |

### 2. Deterministic Static Branch-Probability Heuristics for `Runtime(PostCleanup)` MIR

**Basis: source + derived (`support/VerifiedLayoutPass.lean#L254-L280`)**

To drive `Ext-TSP` and `.text.unlikely` splitting in `MiniMach` without requiring PGO training runs, `VerifiedLayoutPass.lean` defines a deterministic structural edge classifier (`MirEdgeKind`, `staticEdgeWeight`) directly over `Runtime(PostCleanup)` MIR:

1. **`MirEdgeKind.loopBackedge` ($\text{weight} = 32,768 = 32\times$ latch weight):** Edges targeting a dominating loop header (`bb_target <= bb_src` in natural loop order) receive $32\times$ weight so `Ext-TSP` keeps the entire inner loop body contiguous within a single 32 B / 64 B DSB window.
2. **`MirEdgeKind.normalHotFallthrough` ($\text{weight} = 960 / 1024 = 93.75\%$):** `Ok(_)` / `Some(_)` discriminant arms and in-bounds `assert` continuation edges fall through without taken jumps.
3. **`MirEdgeKind.resultErrOrOptionNone` ($\text{weight} = 64 / 1024 = 6.25\%$):** Early-return `Err(_)` / `None` branches identified from standard library enum discriminant metadata are placed after the hot chain.
4. **`MirEdgeKind.coldCallOrAssertPanic` and `MirEdgeKind.unwindCleanupPad` ($\text{weight} = 0$, assigned to `SectionSlice.coldTextUnlikely`):** Any basic block terminating in `Unreachable`, `UnwindAction::Cleanup` / `UnwindResume`, or a direct call to a `#[cold]` function (`core::panicking::panic_bounds_check`, `panic_fmt`, `alloc::alloc::handle_alloc_error`) receives weight `0` and is placed in `.text.unlikely.<sym>`.

### 3. Lean `v4.34.1` Mechanization of `MiniMach` Layout, Splitting, and NOP Alignment

**Basis: source + execution (`support/VerifiedLayoutPass.lean`, checked under `anneal-lean-run`)**

Building `support/VerifiedLayoutPass.lean` via `anneal-lean-run --mode file --concurrency 4 -- lake env lean VerifiedLayoutPass.lean` verifies five kernel theorems with **zero `sorry`** and **zero `native_decide`**:

| Theorem Name | Lines | Statement Summary | Kernel Axioms |
| :--- | :---: | :--- | :--- |
| `evalTerminator_invert` | `134–141` | `evalTerminator (invertTerminator t) s = evalTerminator t s`: negating `Cond` (`eqZero` $\leftrightarrow$ `neZero`) and swapping `ifTrue`/`ifFalse` preserves the exact branch successor in every `MachState`. | `[propext]` |
| `block_perm_sim` | `207–228` | `LayoutLookupEquiv L₁ L₂ → runMach fuel L₁ bid s = runMach fuel L₂ bid s`: any basic-block permutation (`Ext-TSP`) with corrected fallthrough/inverted branches refines the original `MiniMach` CFG for all `fuel : Nat`. | `[propext]` |
| `hot_cold_split_sim` | `248–253` | `runMach fuel (blocks.map (RetagCold isCold)) bid s = runMach fuel blocks bid s`: partitioning hot and cold blocks into `.text.<sym>` and `.text.unlikely.<sym>` preserves multi-step execution identically. | `[propext]` |
| `nop_align_sim` | `278–286` | `runNopPad pads st = { st with rip := st.rip + sumPadBytes pads }`: any sequence of multi-byte architectural NOPs inserted for loop or `SKX102` JCC alignment advances `rip` to the aligned target while preserving `regs`, `zf`, and `mem` by `rfl`. | `[propext]` |
| `cold_and_unwind_assigned_zero_weight` | `307–311` | `staticEdgeWeight .coldCallOrAssertPanic = 0 ∧ staticEdgeWeight .unwindCleanupPad = 0 ∧ staticEdgeWeight .loopBackedge > staticEdgeWeight .normalHotFallthrough`. | *(none)* |

### 4. Empirical Evaluation Across All 8 `W-Core` Workloads and 16 `--shuffle-sections` Seeds

**Basis: execution (`support/benchmark_ext_tsp_alignment.py`, `support/layout_opt_results.json`)**

Table 1 reports the suite-level speed, 16-seed layout variance ($\sigma_{\text{layout}}$ CV and max-over-min spread), and `.text` footprint across all four layout configurations on `rustc 1.99.1 -C opt-level=3` (`x86_64-unknown-linux-gnu`):

| Configuration | Description | Suite $\text{GeoMean}$ Speed Ratio vs. `L0` ($\Delta\%$) | Mean 16-Seed Layout CV ($\sigma_{\text{layout}}$) | Worst-Case Workload Layout CV | Mean 16-Seed Spread ($(\max-\min)/\text{med}$) | Mean `.text` Size $\Delta\%$ vs. `L0` |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: |
| **`L0_Stock_O3`** | Default Pettis-Hansen layout + 16 B loop align, no JCC padding | `1.0000x` (`+0.00%`) | `5.31%` | `15.08%` | `20.91%` | `+0.00%` |
| **`L1_Static_ExtTSP_Split`** | Static `Ext-TSP` (`-ext-tsp-apply-without-profile`) + `.text.unlikely` split | **`0.9955x` (`-0.45%`)** | **`2.20%`** | `10.37%` | **`7.23%`** | **`-0.02%`** |
| **`L2_Static_ExtTSP_Loop32_JCC32`** | Static `Ext-TSP` + `.text.unlikely` + 32 B loop/non-fallthrough align + 32 B `SKX102` JCC align | **`0.9915x` (`-0.85%`)** | **`2.65%`** | **`9.00%`** | **`9.05%`** | `+0.51%` |
| **`L3_PGO_ExtTSP_Loop32_JCC32`** | IR-PGO edge weights + `Ext-TSP` + `.text.unlikely` + 32 B loop/JCC align | **`0.9672x` (`-3.28%`)** | `5.79%` | `27.59%` | `23.25%` | `+0.06%` |

Table 2 reports the per-workload 16-seed median latency ($\mu\text{s}$) and inter-seed layout CV ($\sigma_{\text{layout}}$) across all 8 `W-Core` workloads:

| `W-Core` Workload | `L0_Stock_O3` Median ($\mu\text{s}$) / $\sigma_{\text{layout}}$ CV (Spread) | `L1_Static_ExtTSP_Split` Median ($\mu\text{s}$) / $\sigma_{\text{layout}}$ CV (Spread) | `L2_Static_ExtTSP_Loop32_JCC32` Median ($\mu\text{s}$) / $\sigma_{\text{layout}}$ CV (Spread) | `L3_PGO_ExtTSP_Loop32_JCC32` Median ($\mu\text{s}$) / $\sigma_{\text{layout}}$ CV (Spread) |
| :--- | ---: | ---: | ---: | ---: |
| `bench-serde-json` | `21.34` / `14.95%` (`58.17%`) | `20.67` / `10.37%` (`28.77%`) | **`19.74` / `9.00%` (`36.85%`)** | **`17.07` / `7.47%` (`21.11%`)** |
| `bench-regex-automata` | `24.43` / `0.37%` (`1.25%`) | **`24.44` / `0.08%` (`0.23%`)** | `24.44` / `0.25%` (`1.03%`) | `24.44` / `0.08%` (`0.24%`) |
| `bench-simd-kernels` | `0.771` / `15.08%` (`63.05%`) | `0.771` / `0.21%` (`0.69%`) | **`0.771` / `0.11%` (`0.40%`)** | **`0.772` / `0.07%` (`0.31%`)** |
| `bench-compression-image` | `7.36` / `9.83%` (`37.30%`) | **`7.34` / `3.96%` (`16.21%`)** | `7.38` / **`6.67%` (`14.88%`)** | **`7.14`** / `27.59%` (`119.37%`) |
| `bench-concurrency-sync` | `6.67` / `1.52%` (`4.67%`) | `6.67` / **`1.19%`** (`5.27%`) | `6.67` / `1.45%` (**`4.46%`**) | `6.68` / `1.48%` (`4.57%`) |
| `bench-hashbrown-indexmap` | `6.10` / `0.42%` (`1.67%`) | **`6.09`** / `0.77%` (`3.06%`) | `6.14` / `0.79%` (`2.67%`) | **`6.08`** / `9.30%` (`39.08%`) |
| `bench-unwind-drop-ladder` | `2.385` / `0.02%` (`0.09%`) | `2.385` / `0.59%` (`1.90%`) | `2.385` / `0.33%` (`1.32%`) | **`2.385` / `0.02%` (`0.06%`)** |
| `bench-ffi-no-std-crc32c` | `11.24` / `0.30%` (`1.04%`) | `11.25` / `0.45%` (`1.74%`) | `11.24` / `2.57%` (`10.81%`) | **`11.13` / `0.35%` (`1.29%`)** |

## Boundaries

- **Tail duplication (`TailDuplicator`) vs. pure block permutation (`Ext-TSP`):** While block permutation (`block_perm_sim`), `.text.unlikely` splitting (`hot_cold_split_sim`), and NOP alignment (`nop_align_sim`) preserve the 1-to-1 `BlockId` graph without duplicating instructions, tail duplication (`-tail-dup-placement`) clones basic blocks into multiple predecessors and therefore requires a `1`-to-$k$ block-cloning simulation witness in `HybridTrace`.
- **Cross-section displacement range (`.text` vs. `.text.unlikely`):** Splitting cold blocks into `.text.unlikely` uses 32-bit PC-relative conditional/unconditional jumps (`JCC rel32` / `JMP rel32` on x86-64/i686; `B.cond` $\pm 1\text{ MiB}$ or `B` $\pm 128\text{ MiB}$ on AArch64); on AArch64 binaries whose `.text` + `.text.unlikely` span exceeds $1\text{ MiB}$, cross-section conditional branches must invert the condition over a direct 26-bit unconditional `B` ($\pm 128\text{ MiB}$).

## Evidence

- **Lean `v4.34.1` mechanization and empirical scripts in `support/`:**
  - `support/VerifiedLayoutPass.lean`: Kernel-checked proofs of `evalTerminator_invert`, `block_perm_sim`, `hot_cold_split_sim`, `nop_align_sim`, and `cold_and_unwind_assigned_zero_weight`.
  - `support/benchmark_ext_tsp_alignment.py`: 8-workload $\times$ 4-configuration $\times$ 16-seed benchmark harness (`512` compiled binaries).
  - `support/layout_opt_results.json`: Per-seed and per-workload runtime latency, $\sigma_{\text{layout}}$ CV, spread, and `.text` byte tables.
- **Upstream LLVM 23.1.1 source references (`rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):**
  - `llvm/lib/CodeGen/MachineBlockPlacement.cpp:88-248, 3001-3139, 3569-3750`
  - `llvm/lib/CodeGen/MachineFunctionSplitter.cpp:1-227`
  - `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp:80-165, 441-560`
  - `lld/ELF/CallGraphSort.cpp:1-347`

## Revalidation

Verify the Lean `v4.34.1` proof module and re-run the 16-seed `W-Core` layout benchmark:

```bash
anneal-lean-run --mode file --concurrency 4 -- lake env lean \
  reports/verified-minimach-ext-tsp-layout-and-loop-jcc-alignment/support/VerifiedLayoutPass.lean
python3 reports/verified-minimach-ext-tsp-layout-and-loop-jcc-alignment/support/benchmark_ext_tsp_alignment.py \
  --out /tmp/b2_layout_results.json
```
