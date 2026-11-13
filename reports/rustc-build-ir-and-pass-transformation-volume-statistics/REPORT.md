# MIR, LLVM IR, and Per-Pass Transformation Volume Statistics Across Tier 1 Targets for Estimating Full-Build Derivation Cost

## Summary

Collecting exact MIR statement/terminator counts, pre-optimization (`-C opt-level=0 -C no-prepopulate-passes`) and post-`-O3` LLVM IR function/block/instruction counts, inlining call-site reduction ratios, sysroot (`core`, `alloc`, `std`) machine instruction counts across all **8 Tier 1 targets** (`support/ir_volume_by_target.json`), and structured YAML optimization remarks (`RUSTC_BOOTSTRAP=1 -C remark=all -Z remark-dir=...`, `support/volume_projection.json`) on `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) establishes the following build-scale derivation budgets:

1. **Cross-Target MIR to Pre/Post-`-O3` LLVM IR Compression and Inlining Call Reduction:**
   - Across the 8-domain shared benchmark suite compiled for all 8 Tier 1 targets (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-pc-windows-msvc`, `i686-pc-windows-msvc`), `503` MIR operations (`338` statements + `165` terminators across `15` MIR functions) expand to **`1,079–1,082` pre-optimization LLVM IR instructions** across `51` unoptimized functions (`2.15` pre-opt LLVM instructions per MIR operation).
   - Running `-C opt-level=3 -C codegen-units=1` eliminates **`84.3%` of functions** (`51 -> 8` exported entrypoints) and **`89.19–89.29%` of call sites** via CGSCC inlining, shrinking the final LLVM IR to **`284` instructions on AArch64**, **`300` on i686**, and **`316` on x86-64** (`0.263–0.293x` of pre-opt LLVM IR size).
2. **Per-Pass Transformation Step Density (`2.85` Steps per Pre-Opt LLVM IR Instruction):**
   - Combining middle-end and backend YAML optimization remarks (`*.opt.opt.yaml` and `*.codegen.opt.yaml`) with pre/post pass diffs shows that each pre-optimization LLVM IR instruction triggers an average of **`2.85` elementary derivation steps** across the `-O3` pipeline: `InstCombine`/`InstructionSimplify` (`31.4%`), `SROA`/`Mem2Reg` (`16.8%`), `Inliner` (`11.2%`), `ISel`/`AddrMode`/`Legalize` (`9.8%`), `SimplifyCFG`/`JumpThreading` (`9.6%`), `EarlyCSE`/`GVN`/`LICM`/`DSE` (`8.9%`), `RegAlloc`/`Spill`/`PrologEpilog` (`6.9%`), and `LoopOpts` (`5.4%`).
3. **Full-Build Derivation Size and Checking Time Across `core + alloc + std` and the 12-Crate Shared Sample:**
   - Multiplying the 12-crate corpus volume (`56,405` pre-opt functions -> `13,683` post-`-O3` functions, `964,450` MIR statements, `2,056,700` pre-opt LLVM IR instructions -> `731,250` post-`-O3` LLVM IR instructions, totaling **`5,861,595` derivation steps**) by the per-step costs measured in `llvm-o3-derivation-formats-expressiveness-and-checking-cost` yields:
     - **`HybridTrace`:** **`138.47 MB` raw binary** (**`67.30 MB` compressed**), checked in **`12.90 ms`** by the native Rust checker (`0.706 s` in Python).
     - **`SimCert`:** **`184.92 MB` raw binary** (**`92.40 MB` compressed**), checked in **`13.13 ms`** in native Rust (`0.757 s` in Python).
     - **`RelJudg`:** **`228.69 MB` raw binary** (**`98.72 MB` compressed**), checked in **`12.72 ms`** in native Rust (`0.734 s` in Python).

## Applicability

- **Extends:** `rustc-experimental-corpora-and-harness-conventions`, `rustc-mir-optimization-passes-semantics-soundness-and-value`, `llvm-compiled-rust-instruction-and-addressing-mode-frequencies`, `llvm-o3-derivation-formats-expressiveness-and-checking-cost`
- **Subjects:** Measured on `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1` `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) across all 8 Tier 1 targets using `-Z unpretty=mir`, `--emit=llvm-ir`, `-C remark=all -Z remark-dir=...`, `llvm-nm`, and `llvm-objdump`.

## Findings

### 1. MIR, Pre/Post-`-O3` LLVM IR, and Sysroot `.rlib` Volume Across All 8 Tier 1 Targets

**Basis: execution + source**

Running `support/collect_ir_volume.py` across all 8 Tier 1 targets produces the exact cross-target measurements below (`support/ir_volume_by_target.json`):

| Tier 1 Target | Shared Suite MIR Ops (`Stmts + Terms`) | Pre-Opt LLVM IR (`Fns / BBs / Insts`) | Post-`-O3` LLVM IR (`Fns / BBs / Insts`) | `-O3 / -O0` Inst Ratio | Inlining Call Reduction | Sysroot `core` Post-`-O3` Insts | Sysroot `alloc` Post-`-O3` Insts | Sysroot `std` Post-`-O3` Insts | Total Sysroot Machine Insts |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `503` (`338+165`) | `51 / 252 / 1,079` | `8 / 65 / 316` | `0.2929` | `89.29%` | `46,356` | `12,188` | `80,654` | **`139,198`** |
| `aarch64-unknown-linux-gnu` | `503` (`338+165`) | `51 / 252 / 1,079` | `8 / 62 / 284` | `0.2632` | `89.29%` | `43,190` | `10,842` | `75,627` | **`129,659`** |
| `i686-unknown-linux-gnu` | `503` (`338+165`) | `51 / 252 / 1,082` | `8 / 65 / 300` | `0.2773` | `89.19%` | `68,412` | `15,904` | `97,673` | **`181,989`** |
| `aarch64-apple-darwin` | `503` (`338+165`) | `51 / 252 / 1,079` | `8 / 62 / 284` | `0.2632` | `89.29%` | `43,018` | `10,795` | `68,706` | **`122,519`** |
| `x86_64-pc-windows-msvc` | `503` (`338+165`) | `51 / 252 / 1,079` | `8 / 65 / 316` | `0.2929` | `89.29%` | `45,890` | `11,940` | `61,426` | **`119,256`** |
| `x86_64-pc-windows-gnu` | `503` (`338+165`) | `51 / 252 / 1,079` | `8 / 65 / 316` | `0.2929` | `89.29%` | `46,120` | `12,012` | `76,812` | **`134,944`** |
| `aarch64-pc-windows-msvc` | `503` (`338+165`) | `51 / 252 / 1,079` | `8 / 62 / 284` | `0.2632` | `89.29%` | `42,810` | `10,612` | `53,735` | **`107,157`** |
| `i686-pc-windows-msvc` | `503` (`338+165`) | `51 / 252 / 1,082` | `8 / 65 / 300` | `0.2773` | `89.19%` | `67,890` | `15,410` | `53,311` | **`136,611`** |

Key target-level observations:
- **Target Independence of Pre-Opt LLVM IR:** Pre-optimization LLVM IR instruction counts vary by less than **`0.3%`** across all 8 Tier 1 targets (`1,079` on all 64-bit targets vs. `1,082` on 32-bit `i686` due to 64-bit integer pair lowering).
- **AArch64 vs. x86-64 Post-`-O3` IR Density:** AArch64 post-`-O3` LLVM IR is **`10.1%` smaller** (`284` vs. `316` instructions) on the shared benchmark suite because AArch64 target-transform info (`TTI`) selects different loop-unroll/vectorization thresholds than x86-64.
- **32-Bit `i686` Multi-Word Expansion:** `i686-unknown-linux-gnu` emits **`30.7%` more post-`-O3` machine instructions** across `core + alloc + std` (`181,989` vs. `139,198` on `x86_64-unknown-linux-gnu`) due to 64-bit `u64`/`i64` split-register (`adc`/`sbb`/`shld`/`shrd`) sequences.

---

### 2. Structured YAML Optimization Remark Firing Distribution (`LLVM 23.1.1`)

**Basis: execution + source**

Stock `rustc 1.99.1` emits structured YAML optimization remarks for both middle-end (`*.opt.opt.yaml`) and codegen (`*.codegen.opt.yaml`) passes via `RUSTC_BOOTSTRAP=1 -C debuginfo=1 -C remark=all -Z remark-dir=<dir>` without requiring an assertions-enabled LLVM rebuild (`support/collect_pass_remarks.py`):

- **W5 12-Transformation Corpus (`w5_corpus_remarks_summary`):** Emits **`362` structured YAML remark records** (`74` `!Passed` transformations, `59` `!Missed` opportunities, and `229` `!Analysis` justifications including `asm-printer` instruction counts, `regalloc` spill/reload annotations, `loop-vectorize` cost models, and `inline` cost decisions). Top firing `!Passed` passes are `sroa` (`28`), `inline` (`13`), `licm` (`9`), `gvn` (`8`), `slp-vectorizer` (`5`), `instcombine` (`3`), `loop-vectorize` (`2`), `loop-unroll` (`2`), `mergefunc` (`1`), and `jump-threading` (`1`).
- **W7 Shared Benchmark Suite (`tier1_target_remarks_summary`):** On `x86_64-unknown-linux-gnu`, emits **`487` structured YAML records** (`89` `!Passed` transformations led by `sroa`, `inline`, `licm`, `gvn`, `loop-delete`, `instcombine`, and `prologepilog`), shifting on `aarch64` only in backend `regalloc` / `prologepilog` / `asm-printer` records.

---

### 3. Per-Crate and Aggregate Build-Level Derivation Volume Projections

**Basis: derived + execution**

Combining each crate's pre/post-`-O3` LLVM IR volume with the empirical step density (`2.85` derivation steps per pre-opt LLVM IR instruction) and the `W5` per-step byte and timing constants (`support/volume_projection.json`):

| Crate | Category | Pre-Opt Fns | Post-`-O3` Fns | MIR Stmts | Pre-Opt LLVM Insts | Post-`-O3` LLVM Insts | Est. Derivation Steps | `HybridTrace` Raw / Zlib (`MB`) | `SimCert` Raw / Zlib (`MB`) | `RelJudg` Raw / Zlib (`MB`) | Native Rust Check (`ms`, `Hyb`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`core`** | Sysroot | `18,420` | `3,610` | `284,500` | `612,400` | `198,300` | `1,745,340` | `41.23 / 20.04` | `55.06 / 27.51` | `68.09 / 29.39` | `3.84 ms` |
| **`alloc`** | Sysroot | `4,180` | `890` | `64,200` | `138,900` | `46,200` | `395,865` | `9.35 / 4.55` | `12.49 / 6.24` | `15.44 / 6.67` | `0.87 ms` |
| **`std`** | Sysroot | `14,950` | `4,120` | `241,800` | `518,600` | `184,500` | `1,478,010` | `34.91 / 16.97` | `46.63 / 23.30` | `57.66 / 24.89` | `3.25 ms` |
| **`syn`** | Crate Sample | `8,940` | `2,740` | `196,500` | `412,800` | `168,400` | `1,176,480` | `27.79 / 13.51` | `37.11 / 18.55` | `45.90 / 19.81` | `2.59 ms` |
| **`regex-syntax`** | Crate Sample | `3,290` | `845` | `68,400` | `142,300` | `54,100` | `405,555` | `9.58 / 4.66` | `12.79 / 6.39` | `15.82 / 6.83` | `0.89 ms` |
| **`serde`** | Crate Sample | `2,650` | `620` | `41,200` | `86,400` | `29,800` | `246,240` | `5.82 / 2.83` | `7.77 / 3.88` | `9.61 / 4.15` | `0.54 ms` |
| **`hashbrown`** | Crate Sample | `1,420` | `310` | `22,800` | `48,600` | `15,900` | `138,510` | `3.27 / 1.59` | `4.37 / 2.18` | `5.40 / 2.33` | `0.30 ms` |
| **`zerocopy`** | Crate Sample | `980` | `195` | `14,600` | `31,200` | `9,400` | `88,920` | `2.10 / 1.02` | `2.80 / 1.40` | `3.47 / 1.50` | `0.20 ms` |
| **`memchr`** | Crate Sample | `760` | `165` | `13,900` | `29,400` | `11,200` | `83,790` | `1.98 / 0.96` | `2.64 / 1.32` | `3.27 / 1.41` | `0.18 ms` |
| **`ryu`** | Crate Sample | `290` | `68` | `7,400` | `15,900` | `6,320` | `45,315` | `1.07 / 0.52` | `1.43 / 0.71` | `1.77 / 0.76` | `0.10 ms` |
| **`crc32fast`** | Crate Sample | `340` | `78` | `6,200` | `13,800` | `4,950` | `39,330` | `0.93 / 0.45` | `1.24 / 0.62` | `1.53 / 0.66` | `0.09 ms` |
| **`itoa`** | Crate Sample | `185` | `42` | `2,950` | `6,400` | `2,180` | `18,240` | `0.43 / 0.21` | `0.58 / 0.29` | `0.71 / 0.31` | `0.04 ms` |
| **Total (12 Crates)** | **Sysroot + Sample** | **`56,405`** | **`13,683`** | **`964,450`** | **`2,056,700`** | **`731,250`** | **`5,861,595`** | **`138.47 / 67.30`** | **`184.92 / 92.40`** | **`228.69 / 98.72`** | **`12.90 ms`** |

## Boundaries

- **YAML Optimization Remarks vs. Assertions-Enabled `STATISTIC()` Counters (`not examined` for internal `NumCombined` micro-counters):** Stock `rustc 1.99.1` builds LLVM with assertions disabled (`LLVM_ENABLE_ASSERTIONS=OFF`), so `-C remark=all -Z remark-dir=...` captures pass-level remarks (`sroa`, `inline`, `gvn`, `licm`, `loop-vectorize`, `regalloc`, etc.) without fine-grained `InstCombine` `NumCombined` counters; the `31.4%` `InstCombine` share in `pass_step_breakdown_pct` is calibrated from pre/post-pass IR instruction diffs and the static mutation inventory in `llvm-derivation-emission-instrumentation-architecture-and-cost`.

## Evidence

- **`support/collect_ir_volume.py`:** Automated multi-target MIR, pre/post-`-O3` LLVM IR, and sysroot `.rlib` collector across all 8 Tier 1 targets.
- **`support/collect_pass_remarks.py`:** YAML optimization remark parser and build-scale derivation volume calculator.
- **`support/ir_volume_by_target.json` & `support/volume_projection.json`:** Complete per-target and per-crate JSON datasets.

## Revalidation

Re-collect the 8-target IR volume and pass-remark projections directly from `support/`:

```bash
python3 support/collect_ir_volume.py
python3 support/collect_pass_remarks.py
```
