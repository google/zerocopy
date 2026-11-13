# Performance Models and Microarchitectural Tuning Data for x86-64 and AArch64 Optimizers

## Summary

A verified compiler with a derivation-checked optimizer separates semantic correctness from heuristic profitability: any schedule, instruction selection, or alignment choice that validates against its semantic certificate is sound, so microarchitectural cost tables sit entirely outside the trusted computing base (TCB). Across `x86_64` and `aarch64`, three primary machine-readable tuning corpora are available under permissive open-source licenses:

1. **LLVM 23.1.1 TableGen `SchedMachineModel` definitions (`Apache-2.0 WITH LLVM-exception`)**: 22 X86 `.td` files (`41,772` lines, `3,632` `InstRW` overrides across 19 CPU models from `SandyBridgeModel` and `Znver1Model` to `SapphireRapidsModel`, `LunarlakePModel`, and `Znver4Model`) and 37 AArch64 `.td` files (`52,561` lines, `10,850` `InstRW` overrides across 28 CPU models including `NeoverseN1Model`–`NeoverseV3Model`, `CortexA53Model`–`CortexA320Model`, `OryonModel`, and `CycloneModel`). Crucially, in upstream LLVM 23.1.1, **every Apple Silicon CPU from `apple-a7` through `apple-m4` is mapped to `CycloneModel`** (`IssueWidth = 6`, `MicroOpBufferSize = 192`, `AArch64SchedCyclone.td`, 881 lines, `148` `InstRW` entries), which predates Firestorm/Avalanche/M1–M4 wide 8–10-issue pipelines.
2. **uops.info XML and uiCA simulator tables (`CC BY 4.0` / `MIT` / `Apache-2.0 WITH LLVM-exception`)**: `andreas-abel/uiCA` (`6ebeeab0f8705cae4b17a9362f9c65ef91f5cc44`) ships pre-generated Python instruction-execution and port-usage tables (`instrData/*.py`, `820,400` lines across 12 Intel microarchitectures from Sandy Bridge `SNB` through Rocket Lake `RKL`) alongside `convertXML.py` (`1,188` lines), which ingests the hardware-measured `instructions.xml` database from `uops.info` (ASPLOS 2019).
3. **BHive basic-block throughput corpus (`MIT`)**: `ithemal/bhive` (`5f1d50077ac0779fd227b261dcf517862c7104bd`) provides hardware PMU cycle-per-iteration ground truth across `330,018` unique `x86_64` basic blocks on Haswell (`HSW`), Ivy Bridge (`IVB`), and Skylake (`SKL`), plus a reproducible 600-block benchmark sample stratified across 6 instruction categories (`Ld`, `St`, `Ld/St`, `Scalar`, `Vec`, `Scalar/Vec`).

Evaluating `llvm-mca` against the 600-block BHive ground-truth sample shows a median absolute percentage error (MedAPE) of `10.66%` on Skylake, `10.42%` on Haswell, and `10.42%` on Ivy Bridge, with strong rank correlation (Kendall's $\tau = 0.8188$, $0.8161$, and $0.8120$). Mean absolute percentage error (MAPE) across all 600 blocks (`36.91%` SKL, `37.10%` HSW, `47.56%` IVB) is dominated by the 39 blocks (`6.5%`) containing statically ambiguous load/store pairs where BHive's harness maps all memory operands to a single scratch page (causing 4K-aliasing/store-forwarding stalls) while `llvm-mca`'s default `-noalias=true` assumes disjoint addresses (`219.23%` MAPE on aliasing blocks vs. `24.24%` MAPE / `10.20%` MedAPE on the 561 non-aliasing blocks on Skylake). In the published literature on BHive, detailed front-end + port + memory-dependency simulation in `uiCA` reaches `~1%` MAPE (Kendall's $\tau = 0.96$), neural predictors (`Ithemal`, `DiffTune`) achieve `~9–14%` MAPE, and `llvm-mca` without front-end micro-op cache or memory-aliasing modeling achieves `~24–27%` MAPE on non-aliasing blocks.

## Applicability

These findings apply to designing, licensing, and validating cost models, instruction schedulers, peephole profitability filters, and code-alignment passes for an optimizing compiler targeting `x86_64` and `aarch64`.

- **Examined subjects:**
  - `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (Rust `1.99.1`), specifically `compiler/rustc_target/src/spec/` and `compiler/rustc_codegen_llvm/` to trace how target CPUs and tuning flags flow into codegen.
  - `rust-lang/llvm-project` at `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (LLVM `23.1.1`), specifically `llvm/lib/Target/X86/X86Schedule*.td`, `llvm/lib/Target/AArch64/AArch64Sched*.td`, `llvm/lib/MC/MCAssembler.cpp`, `llvm/lib/Target/X86/MCTargetDesc/X86MCAsmInfo.cpp`, and `llvm/tools/llvm-mca/`.
  - `andreas-abel/uiCA` at `6ebeeab0f8705cae4b17a9362f9c65ef91f5cc44` and the `uops.info` paper (Abel & Reineke, ASPLOS 2019, DOI `10.1145/3297858.3304062`) and `uiCA` paper (Abel & Reineke, ACM TOCS 2022, DOI `10.1145/3524059`).
  - `ithemal/bhive` at `5f1d50077ac0779fd227b261dcf517862c7104bd` (Chen et al., IISWC 2019, DOI `10.1109/IISWC47752.2019.9041950`), `Ithemal` (Mendis et al., ICML 2019, arXiv `1808.07412`), and `DiffTune` (Renda et al., MICRO 2020, DOI `10.1109/MICRO50266.2020.00059`).
  - Agner Fog's *Instruction tables* and microarchitecture optimization manuals (`https://www.agner.org/optimize/instruction_tables.pdf`).
- **Scope:** Static basic-block and loop-kernel throughput/latency cost models, register-zeroing and dependency-breaking idioms, macro-fusion pairs, and code/branch alignment padding (`JCC` erratum and loop alignment). Cache-hierarchy capacity misses, DRAM bandwidth saturation, and OS page-fault effects are outside the scope of static pipeline scheduling models.

## Findings

### 1. LLVM 23.1.1 TableGen Scheduling Models for x86-64 and AArch64

Basis: source + execution

In LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), machine scheduling and `llvm-mca` cost estimation share the declarative TableGen `SchedMachineModel` hierarchy defined in `llvm/include/llvm/Target/TargetSchedule.td`. Each CPU subtarget binds architectural `SchedReadWrite` classes (or opcode-regex `InstRW` overrides) to processor resource groups (`ProcResource`, `ProcResGroup`), issue widths (`IssueWidth`), reorder buffer sizes (`MicroOpBufferSize`), loop stream detector capacities (`LoopMicroOpBufferSize`), load latencies (`LoadLatency`), and branch misprediction penalties (`MispredictPenalty`).

#### 1.1 x86-64 Scheduling Models Inventory

Across `llvm/lib/Target/X86/X86Sched*.td`, LLVM 23.1.1 contains 22 scheduling files totaling `41,772` lines and `3,632` `InstRW` overrides across 19 distinct `SchedMachineModel` definitions:

| TableGen File | Model Name | Lines | `ProcResource` Defs | `SchedWriteRes` | `InstRW` Overrides | `IssueWidth` | `MicroOpBufferSize` (ROB / Loop) | `LoadLatency` | `MispredictPenalty` | `CompleteModel` |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :--- | ---: | ---: | :---: |
| `X86SchedSandyBridge.td` | `SandyBridgeModel` | 1,292 | 7 | 74 | 84 | 4 | 168 / 28 | 5 | 16 | `0` |
| `X86SchedHaswell.td` | `HaswellModel` | 1,955 | 10 | 150 | 167 | 4 | 192 / 50 | 5 | 16 | `0` |
| `X86SchedBroadwell.td` | `BroadwellModel` | 1,691 | 10 | 121 | 135 | 4 | 192 / 50 | 5 | 16 | `0` |
| `X86SchedSkylakeClient.td` | `SkylakeClientModel` | 1,762 | 10 | 124 | 143 | 6 | 224 / 50 | 5 | 14 | `0` |
| `X86SchedSkylakeServer.td` | `SkylakeServerModel` | 2,567 | 10 | 180 | 205 | 6 | 224 / 50 | 5 | 14 | `0` |
| `X86SchedIceLake.td` | `IceLakeModel` | 2,591 | 12 | 181 | 204 | 6 | 352 / 50 | 5 | 14 | `0` |
| `X86SchedAlderlakeP.td` | `AlderlakePModel` | 2,474 | 13 | 288 | 351 | 6 | 512 / 72 | 5 | 14 | `0` |
| `X86SchedSapphireRapids.td` | `SapphireRapidsModel` | 5,208 | 13 | 577 | 766 | 6 | 512 / 72 | 5 | 14 | `0` |
| `X86SchedLunarlakeP.td` | `LunarlakePModel` | 2,410 | 19 | 246 | 305 | 8 | 792 / 200 | 4 | 14 | `0` |
| `X86ScheduleZnver1.td` | `Znver1Model` | 1,399 | 12 | 84 | 106 | 4 | 192 / — | 4 | 17 | `0` |
| `X86ScheduleZnver2.td` | `Znver2Model` | 1,403 | 13 | 86 | 109 | 4 | 224 / — | 4 | 17 | `0` |
| `X86ScheduleZnver3.td` | `Znver3Model` | 1,628 | 17 | 68 | 77 | 6 | 256 / 96 | 4 (vec 7) | 13 | `1` |
| `X86ScheduleZnver4.td` | `Znver4Model` | 2,059 | 17 | 102 | 111 | 6 | 320 / 108 | 4 (vec 7) | 13 | `1` |
| `X86ScheduleAtom.td` / `SLM.td` / `BtVer2.td` / `BdVer2.td` / `C864GM*.td` | 6 models | 10,837 | 2–19 | 4–313 | 5–324 | 2–6 | 0–256 | 3–7 | 10–20 | `0`/`1` |

In `llvm/lib/Target/X86/X86.td:1780-1980`, newer Intel P-core and E-core subtargets without standalone `.td` files alias existing models: `graniterapids` and `emeraldrapids` use `SapphireRapidsModel`, `raptorlake` and `meteorlake` use `AlderlakePModel`, `arrowlake-s` / `pantherlake` use `LunarlakePModel`, and `znver5` aliases `Znver4Model` where dedicated overrides are absent.


#### 1.2 AArch64 Scheduling Models Inventory and the Apple Silicon `CycloneModel` Gap

Across `llvm/lib/Target/AArch64/AArch64Sched*.td`, LLVM 23.1.1 contains 37 scheduling files totaling `52,561` lines and `10,850` `InstRW` overrides across 28 distinct `SchedMachineModel` definitions:

| TableGen File | Model Name | Lines | `ProcResource` Defs | `SchedWriteRes` | `InstRW` Overrides | `IssueWidth` | `MicroOpBufferSize` (ROB / Loop) | `LoadLatency` | `MispredictPenalty` | `CompleteModel` |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| `AArch64SchedA53.td` | `CortexA53Model` | 300 | 7 | 13 | 73 | 2 | 0 | 3 | 9 | `1` |
| `AArch64SchedA55.td` | `CortexA55Model` | 483 | 9 | 29 | 141 | 2 | 0 | 4 | 8 | `0` |
| `AArch64SchedA510.td` | `CortexA510Model` | 1,396 | 12 | 33 | 406 | 3 | 0 | 3 | — | `0` |
| `AArch64SchedA57.td` (+ `WriteRes`) | `CortexA57Model` | 1,258 | 7 | 112 | 334 | 3 | 128 / 16 | 4 | 14 | `1` |
| `AArch64SchedCyclone.td` | `CycloneModel` | 881 | 13 | 23 | 148 | 6 | 192 | 4 | 16 | `1` |
| `AArch64SchedNeoverseN1.td` | `NeoverseN1Model` | 1,116 | 7 | 89 | 171 | 3 | 128 / 16 | 4 | 11 | `1` |
| `AArch64SchedNeoverseN2.td` | `NeoverseN2Model` | 2,535 | 10 | 165 | 449 | 5 | 160 / 16 | 4 | 10 | `1` |
| `AArch64SchedNeoverseN3.td` | `NeoverseN3Model` | 2,488 | 9 | 140 | 445 | 5 | 160 / 16 | 4 | 10 | `1` |
| `AArch64SchedNeoverseV1.td` | `NeoverseV1Model` | 2,013 | 12 | 168 | 298 | 8 | 256 / 16 | 4 | 11 | `1` |
| `AArch64SchedNeoverseV2.td` | `NeoverseV2Model` | 2,847 | 15 | 217 | 448 | 6 | 320 / 16 | 4 | 10 | `1` |
| `AArch64SchedNeoverseV3.td` | `NeoverseV3Model` | 2,780 | 18 | 197 | 450 | 10 | 320 / 16 | 4 | 10 | `1` |
| `AArch64SchedOlympus.td` | `OlympusModel` | 3,382 | 13 | 205 | 1,031 | 10 | 320 / 16 | 4 | 10 | `1` |
| `AArch64SchedOryon.td` | `OryonModel` | 1,660 | 22 | 81 | 331 | 14 | 376 / 16 | 4 | 13 | `1` |
| `AArch64SchedAmpere1B.td` | `Ampere1BModel` | 1,151 | 8 | 82 | 236 | 12 | 208 / 32 | 3 | 10 | `1` |
| `AArch64SchedC1Ultra.td` | `C1UltraModel` | 3,136 | 35 | 162 | 519 | 10 | 320 / 16 | 4 | 10 | `1` |
| `AArch64SchedA64FX.td` | `A64FXModel` | 2,613 | 8 | 182 | 606 | 6 | 180 / 128 | 5 | 12 | `1` |

In `llvm/lib/Target/AArch64/AArch64Processors.td:1380-1560`, every Apple processor definition (`apple-a7` through `apple-a17`, `apple-m1`, `apple-m2`, `apple-m3`, `apple-m4`, and `apple-s4`/`apple-s5`) binds `SchedMachineModel` to `CycloneModel` (originally authored for the 2013 Apple A7 Cyclone core with `IssueWidth = 6`, `MicroOpBufferSize = 192`, 4 integer ALUs, and 2 128-bit NEON pipes). While ISA feature flags (`FeatureLSE`, `FeatureDotProd`, `FeatureBF16`, `FeatureSME`) and subtarget tuning predicates (`TuneAppleM1`, `FeatureZCRegMove`, `FeatureZCMov`, `FeatureFuseAES`, `FeatureFuseArithmeticLogic`, `FeatureFuseLiterals`) differ across generations, `llvm-mca -mtriple=aarch64-unknown-linux-gnu -mcpu=apple-{a7,m1,m2,m3,m4}` produces identical cycle counts (`[103, 403, 104, 807, 1303]` cycles for 100 iterations of our 5-kernel probe in `support/evaluate_tuning_models.py`). A modern optimizer targeting Apple Silicon (`aarch64-apple-darwin`) therefore cannot rely solely on `AArch64SchedCyclone.td` for issue width (8–10 wide on M1 Firestorm through M4) or execution-port pressure without supplementing it with wider port counts (such as `NeoverseV3Model` / `OlympusModel` or empirical Firestorm/M-series measurements).

#### 1.3 Zero-Latency Register Zeroing, Dependency-Breaking Idioms, and Macro-Fusion

Both X86 and AArch64 TableGen models encode special-case register renamer and decoder behaviors required for accurate scheduling and register allocation:

- **Zero-latency register-zeroing and move elimination:** On X86 (`llvm/lib/Target/X86/X86SchedPredicates.td:35-140`), `IsZeroIdiomPred` matches `XOR32rr`/`XOR64rr`/`PXORrr`/`VPXORDZrr`/`SUB32rr` when `MI.getOperand(1).getReg() == MI.getOperand(2).getReg()`, routing them to `WriteZero` (`0` execution cycles, `0` execution ports). By contrast, `movl $0, %eax` (`MOV32ri`) consumes an ALU execution port and 1 cycle latency (`k3_zero_idiom_xor` = `103` cycles vs. `k4_false_dep_mov0` = `104` cycles under `llvm-mca` when paired with a dependent `addq`). On AArch64 (`llvm/lib/Target/AArch64/AArch64SchedPredicates.td`), `IsZeroFPIdiomPred` and `FeatureZCRegMove`/`FeatureZCMov` model renamer-handled `mov xd, #0` and `movi v0.2d, #0`.
- **Macro-fusion pairs:** In `llvm/lib/Target/X86/X86MacroFusion.cpp` and `llvm/lib/Target/AArch64/AArch64MacroFusion.cpp`, the post-RA scheduler (`createMacroFusionDAGMutation`) fuses adjacent flag-setting (`CMP`, `TEST`, `ADD`, `SUB`, `AND`, `INC`, `DEC`) and conditional-branch (`JCC` / `B.cond`) instructions into a single decoder micro-op when scheduled contiguously, plus AES (`AESE`+`AESMC`) and ADRP+ADD literal pairs on AArch64.

---

### 2. Empirical Tuning Databases and Throughput Predictors (`uops.info`, `uiCA`, `BHive`, Agner Fog)

Basis: source + execution + documentation

| Source / Predictor | Architecture Coverage | Representation & Size | Reported / Measured Accuracy on BHive | License & Redistribution Terms |
| :--- | :--- | :--- | :--- | :--- |
| **`uops.info` XML** (Abel & Reineke, ASPLOS 2019) | Intel `CON` through `ICL`/`RKL` + AMD `ZEN+`..`ZEN4` | Single XML file (`instructions.xml`) with per-uarch latency (per operand edge), throughput, port masks, and uops count | Hardware PMU ground truth for single instructions | **`CC BY 4.0`** (attribution required; unrestricted commercial and open-source compiler embedding) |
| **`uiCA`** (`andreas-abel/uiCA`, `6ebeeab0f8705cae4b17a9362f9c65ef91f5cc44`, ACM TOCS 2022) | 12 Intel uarchs (`SNB`, `IVB`, `HSW`, `BDW`, `SKL`, `SKX`, `KBL`, `CFL`, `CLX`, `CNL`, `ICL`, `RKL`) | `820,400` lines in `instrData/*.py` + `microArchConfigs.py` (`287` lines) + `uiCA.py` (`2,429` lines) + `convertXML.py` (`1,188` lines) | **MAPE `~0.9%–1.4%`**, Kendall's $\tau \approx 0.96$ on BHive (models front-end 16B fetch windows, DSB uop cache, macro-fusion, port assignment, and memory dependencies) | **`MIT`** (`uiCA.py`, `convertXML.py`, `microArchConfigs.py`), **`Apache-2.0 WITH LLVM-exception`** (`x86_instructions.py`), **`CC BY 4.0`** (`instrData/*.py` derived from `uops.info`) |
| **LLVM TableGen + `llvm-mca`** (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) | 19 X86 models + 28 AArch64 models | `94,333` lines across 59 `.td` files | **MedAPE `10.4%–10.7%`**, non-aliasing **MAPE `24.2%–31.2%`**, overall **MAPE `36.9%–47.6%`**, Kendall's $\tau = 0.812–0.819$ on BHive 600-block sample | **`Apache-2.0 WITH LLVM-exception`** |
| **`BHive`** (`ithemal/bhive`, `5f1d50077ac0779fd227b261dcf517862c7104bd`, IISWC 2019) | Intel `IVB`, `HSW`, `SKL` | `330,018` unique hex-encoded `x86_64` basic blocks in `benchmark/throughput/{haswell,ivybridge,skylake}.csv` + 600-block stratified sample + C PMU timing harness (`timing-harness/`) | Ground-truth PMU cycle counts (unrolled inside a single-page scratch memory mapping) | **`MIT`** (`LICENSE`, Copyright 2019 Massachusetts Institute of Technology) |
| **`Ithemal` & `DiffTune`** (ICML 2019 / MICRO 2020) | Intel `IVB`, `HSW`, `SKL` | Hierarchical LSTM (`Ithemal`) or differentiable surrogate tuning of LLVM `SchedReadWrite` tables (`DiffTune`) | `Ithemal`: **MAPE `~8.9%`** (on BHive test split); `DiffTune`-learned LLVM tables: **MAPE `~13.8%`** (vs. `~25%` default `llvm-mca`) | Open-source research code (`MIT`), but neural weights lack interpretability for deterministic cross-target table maintenance |
| **Agner Fog's *Instruction tables*** (`agner.org/optimize`) | Intel, AMD, VIA `x86_64` | PDF / spreadsheet tables of instruction latency, reciprocal throughput, and uop breakdown | Reference manual used to cross-check TableGen and `uops.info` | Prose/PDF copyright Agner Fog (free to read and cite; for automated table generation, `uops.info`'s `CC BY 4.0` XML and LLVM's `Apache-2.0` `.td` files provide explicit machine-redistribution licenses) |
| **Vendor Optimization Manuals** (Intel SDM/Optimization Reference Manual; AMD SOG; Arm Software Optimization Guides) | Intel, AMD, Arm Cortex/Neoverse | Vendor PDFs and Arm machine-readable JSON/TableGen contributions upstreamed directly to `llvm/lib/Target/AArch64/AArch64Sched*.td` | Authoritative architectural latency/throughput specs (Arm engineers directly author `AArch64SchedNeoverse*.td` in LLVM) | Vendor PDFs are proprietary documentation; Arm, Intel, and AMD engineers upstream the corresponding machine-readable `.td` models into LLVM under **`Apache-2.0 WITH LLVM-exception`** |

#### 2.1 Quantitative Evaluation of `llvm-mca` Against BHive Hardware Ground Truth

Using `support/evaluate_tuning_models.py` and the 600-block stratified BHive benchmark (`benchmark/Preprocess/categories/{Ld,St,Ld_St,Scalar,Vec,Scalar_Vec}_500.csv`, 100 blocks per category matched against `benchmark/throughput/{skylake,haswell,ivybridge}.csv`), we disassembled each hex basic block with `llvm-mc -triple=x86_64-unknown-linux-gnu -disassemble` and ran `llvm-mca -mtriple=x86_64-unknown-linux-gnu -mcpu={skylake,haswell,ivybridge} -iterations=100`:

| Microarchitecture | All 600 Blocks MAPE / MedAPE | Non-Aliasing Blocks ($N=561$) MAPE / MedAPE | May-Alias Ld+St Blocks ($N=39$) MAPE / MedAPE | Kendall's $\tau$ | `Scalar` ($N=100$) MAPE / MedAPE | `Vec` ($N=100$) MAPE / MedAPE | `Scalar/Vec` ($N=100$) MAPE / MedAPE | `St` ($N=100$) MAPE / MedAPE | `Ld` ($N=100$) MAPE / MedAPE | `Ld/St` ($N=100$) MAPE / MedAPE |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **Skylake (`-mcpu=skylake`)** | `36.91%` / `10.66%` | **`24.24%` / `10.20%`** | `219.23%` / `83.89%` | **`0.8188`** | `17.97%` / `13.60%` | `15.35%` / `9.09%` | `28.16%` / `12.77%` | `34.75%` / `5.10%` | `67.61%` / `10.20%` | `57.63%` / `14.77%` |
| **Haswell (`-mcpu=haswell`)** | `37.10%` / `10.42%` | **`24.98%` / `10.17%`** | `211.41%` / `77.90%` | **`0.8161`** | `15.87%` / `11.67%` | `25.28%` / `10.62%` | `30.44%` / `11.67%` | `33.49%` / `5.58%` | `63.12%` / `10.74%` | `54.41%` / `11.34%` |
| **Ivy Bridge (`-mcpu=ivybridge`)** | `47.56%` / `10.42%` | **`31.21%` / `9.52%`** | `282.81%` / `252.33%` | **`0.8120`** | `16.60%` / `11.96%` | `23.98%` / `10.75%` | `16.82%` / `10.42%` | `109.25%` / `6.19%` | `61.27%` / `9.52%` | `57.45%` / `10.38%` |

Three actionable conclusions emerge for compiler optimizer design:

1. **Rank correlation is high ($\tau > 0.81$, MedAPE $\approx 10\%$):** For choosing between candidate instruction sequences or list-scheduling permutations within a basic block, simple port + latency TableGen models rank candidates accurately on pure scalar (`15.9%–18.0%` MAPE) and vector (`15.4%–25.3%` MAPE) kernels.
2. **Memory-aliasing assumptions dominate outlier errors:** In `ithemal/bhive/timing-harness/harness.c`, all general-purpose registers holding base addresses are initialized to point to the same mapped scratch page, so blocks with both stores and loads (or repeated stores to the same address) suffer store-to-load forwarding latencies (`~5–6` cycles) or 4K-aliasing penalties in hardware. Because `llvm-mca` defaults to `-noalias=true` (`llvm/tools/llvm-mca/llvm-mca.cpp`), it predicts parallel L1AGU execution (`~0.5–1.0` cycles/iter), creating `>200%` relative under-prediction on the 39 may-alias blocks. When an optimizer knows aliasing facts from MIR/type-based alias analysis, feeding must-alias edges into the scheduler eliminates this error class.
3. **`uiCA` closes the remaining gap (`24%` $\rightarrow$ `~1%` MAPE) via three microarchitectural features missing from `llvm-mca`:** Inspecting `andreas-abel/uiCA/uiCA.py` and `microArchConfigs.py` shows that `uiCA` models (a) 16-byte/32-byte pre-decode fetch windows and MITE/DSB (decoded uop cache) switches, (b) asymmetric port bindings from `uops.info` XML (where an instruction's 2 uops bind to different port masks rather than a uniform `ProcResGroup`), and (c) partial-register/flags stalls (`partialFlags`, `calleeSaved`).

---

### 3. Code Alignment, Loop Padding, and the Intel Skylake `JCC` Erratum

Basis: source

Code alignment affects front-end fetch bandwidth and decoded micro-op cache (DSB) line packing without changing architectural semantics:

1. **Default function and loop alignment in LLVM 23.1.1:**
   - On `x86_64` (`llvm/lib/Target/X86/X86Subtarget.cpp` and `X86TargetMachine.cpp`), functions and hot loop headers default to 16-byte alignment (`Align(16)`), with up to 15 bytes of multi-byte `NOP` padding emitted via `X86MCAsmInfo.cpp` (`nop`, `66 nop`, `0f 1f 00`, `0f 1f 40 00`, `0f 1f 44 00 00`, `66 0f 1f 44 00 00`, `0f 1f 80 00 00 00 00`, `0f 1f 84 00 00 00 00 00`).
   - On `aarch64` (`llvm/lib/Target/AArch64/AArch64Subtarget.cpp`), functions default to 4-byte or 16-byte alignment and loop headers on wide cores (`NeoverseV1`/`V2`/`V3`, `CortexA57`, `Oryon`) configure `PrefLoopAlignment = Align(16)` or `Align(32)` with `MaxBytesForLoopAlignment = 8` or `16`.
2. **Intel Skylake Jump Conditional Code (`JCC`) 32-Byte Boundary Erratum (`SKX102`):**
   - On Skylake, Cascade Lake, Coffee Lake, and Cooper Lake microarchitectures, Intel's microcode mitigation for the Jump Conditional Code (`JCC`) erratum prevents any conditional branch, macro-fused compare-and-branch pair, unconditional jump, `CALL`, or `RET` that crosses or ends on a 32-byte address boundary (`addr % 32 == 0` for the byte immediately following the branch) from being cached in the Decoded ICache (DSB), forcing a switch to the legacy MITE decoder (`~2–15%` throughput loss in tight loops).
   - In `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp` and `llvm/lib/MC/MCAssembler.cpp` (`layoutBundle` / `BoundaryAlignFragment`), `-x86-branches-within-32B-boundaries` (`-mbranches-within-32B-boundaries`) inserts variable-length `NOP`s (or CS/DS segment prefixes) before the branch (or before the `CMP`/`TEST`/`ADD`/`SUB`/`AND` instruction when macro-fused) so that the branch neither crosses nor ends on a 32-byte boundary.
   - Because `NOP` insertion in an assembler or post-link layout pass preserves exact instruction-stream semantics (advancing `RIP` without mutating registers, flags, or memory), a verified compiler can either (a) verify the `NOP` instruction semantics once in the ISA model and allow untrusted alignment heuristics to insert `NOP`s freely before offset resolution, or (b) run alignment before branch-displacement relaxation and validate the final binary's branch displacements.

---

### 4. Licensing and Redistribution Summary for a Verified Optimizer

Basis: source + documentation

For a permissively licensed (`Apache-2.0 OR MIT OR BSD`) verified Rust compiler:

- **Directly embeddable with zero license friction:**
  1. **LLVM TableGen `.td` scheduling models (`llvm/lib/Target/{X86,AArch64}/*Sched*.td`):** Licensed under `Apache-2.0 WITH LLVM-exception`. Can be parsed directly or compiled into Rust/Lean lookup tables.
  2. **`uops.info` `instructions.xml` and `uiCA` `instrData/*.py` (`CC BY 4.0`):** Can be ingested at build time (via `uiCA`'s `MIT`-licensed `convertXML.py`) to generate static Rust/Lean latency, throughput, and port-mask tables for Intel and AMD `x86_64` cores, provided attribution to `uops.info` (Abel & Reineke, ASPLOS 2019) is retained in documentation and source headers.
  3. **`BHive` throughput corpus (`MIT`):** Can be checked into or referenced by the compiler's benchmark/CI suite to regression-test cost-model changes against hardware PMU measurements.

## Boundaries

- **Apple Silicon M1–M4 TableGen fidelity:** Upstream LLVM 23.1.1 maps `apple-m1` through `apple-m4` to `CycloneModel` (`AArch64SchedCyclone.td`). While Arm Cortex and Neoverse (`N1`–`N3`, `V1`–`V3`) have detailed vendor-maintained `.td` models in LLVM, fine-grained port masks for Apple M1–M4 Firestorm/Avalanche/M3/M4 cores are not separated into distinct `SchedMachineModel` definitions in upstream LLVM 23.1.1.
- **Static basic-block scope:** All evaluated predictors (`llvm-mca`, `uiCA`, `Ithemal`, `DiffTune`) assume L1 instruction and data cache hits (`LoadLatency = 4–5` cycles) and steady-state loop execution. L2/L3/DRAM cache-miss latency, TLB walks, and dynamic branch predictor state require runtime profiling (PGO/BOLT) rather than static instruction tables.

## Evidence

- **LLVM 23.1.1 TableGen scheduling models & `llvm-mca`:**
  - Repository: `rust-lang/llvm-project` at commit `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`.
  - X86 models (`22` files, `41,772` lines): `llvm/lib/Target/X86/X86Sched*.td` and `llvm/lib/Target/X86/X86Schedule*.td`; subtarget mapping in `llvm/lib/Target/X86/X86.td:1780-1980`; zero-idiom predicates in `llvm/lib/Target/X86/X86SchedPredicates.td:35-140`.
  - AArch64 models (`37` files, `52,561` lines): `llvm/lib/Target/AArch64/AArch64Sched*.td`; Apple CPU mappings (`apple-a7`..`apple-m4` $\rightarrow$ `CycloneModel`) in `llvm/lib/Target/AArch64/AArch64Processors.td:1380-1560`.
  - Code & branch alignment (`BoundaryAlignFragment`, 32B `JCC` erratum): `llvm/lib/MC/MCAssembler.cpp` and `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp`.
- **`uiCA` and `uops.info`:**
  - Repository: `andreas-abel/uiCA` at commit `6ebeeab0f8705cae4b17a9362f9c65ef91f5cc44` (`uiCA.py`, `convertXML.py`, `microArchConfigs.py`, `instrData/*_instructions.py`, `LICENSE`).
  - Publications: Andreas Abel and Jan Reineke, *"uops.info: Characterizing Latency, Throughput, and Port Usage of Instructions on Intel Microarchitectures"*, ASPLOS 2019 (`10.1145/3297858.3304062`); *"uiCA: Accurate Throughput Prediction of Basic Blocks on Recent Intel Microarchitectures"*, ACM TOCS 40(1), 2022 (`10.1145/3524059`).
- **`BHive`, `Ithemal`, and `DiffTune`:**
  - Repository: `ithemal/bhive` at commit `5f1d50077ac0779fd227b261dcf517862c7104bd` (`benchmark/throughput/{skylake,haswell,ivybridge}.csv`, `benchmark/Preprocess/categories/*_500.csv`, `timing-harness/harness.c`, `LICENSE`).
  - Publications: Yishen Chen et al., *"BHive: A Benchmark Suite and Measurement Framework for Validating x86-64 Basic Block Performance Models"*, IISWC 2019 (`10.1109/IISWC47752.2019.9041950`); Charith Mendis et al., *"Ithemal: Accurate, Portable and Fast Basic Block Throughput Estimation using Deep Neural Networks"*, ICML 2019 (`arXiv:1808.07412`); Alex Renda et al., *"DiffTune: Optimizing CPU Simulator Parameters with Learned Differentiable Surrogates"*, MICRO 2020 (`10.1109/MICRO50266.2020.00059`).
- **Support artifacts in this package:**
  - `support/tuning_models_summary.json` — full extracted inventory of all 22 X86 and 37 AArch64 LLVM 23.1.1 `.td` files plus the 600-block `llvm-mca` vs. BHive evaluation metrics across Skylake, Haswell, and Ivy Bridge.
  - `support/evaluate_tuning_models.py` — reproducible verification script checking the TableGen counts, BHive accuracy metrics, and `llvm-mca` Apple Silicon `CycloneModel` equivalence.

## Revalidation

Run the bundled verification script to validate the TableGen inventory, BHive evaluation metrics, and `llvm-mca` microkernel checks:

```bash
python3 reports/performance-models-and-microarchitectural-tuning-data/support/evaluate_tuning_models.py
```

To re-extract TableGen counts against a newer LLVM checkout or re-run the 600-block BHive comparison against `llvm-mca`:

1. Inspect `llvm/lib/Target/X86/X86Sched*.td` and `llvm/lib/Target/AArch64/AArch64Sched*.td` for `SchedMachineModel`, `ProcResource`, `SchedWriteRes`, and `InstRW` definitions, and check `llvm/lib/Target/AArch64/AArch64Processors.td` to see whether `apple-m1`..`apple-m4` have been migrated off `CycloneModel`.
2. Disassemble the 600 stratified hex basic blocks in `ithemal/bhive/benchmark/Preprocess/categories/{Ld,St,Ld_St,Scalar,Vec,Scalar_Vec}_500.csv` via `llvm-mc -triple=x86_64-unknown-linux-gnu -disassemble` and compare `llvm-mca -mcpu={skylake,haswell,ivybridge} -iterations=100` `TotalCycles / 100.0` against `benchmark/throughput/{skylake,haswell,ivybridge}.csv`.
