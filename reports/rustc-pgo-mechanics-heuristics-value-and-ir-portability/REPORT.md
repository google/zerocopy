# Profile-Guided Optimization (PGO) in `rustc` 1.99.1 and LLVM 23.1.1: Binary Formats, CFG Hashing, Heuristic Attribution, and IR Portability

## Summary

`rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and bundled LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) implement three profile-guided and coverage instrumentation pipelines—IR-level PGO (`-C profile-generate` / `-C profile-use`), sample-based AutoFDO (`-Z profile-sample-use`), and MIR-level source coverage (`-C instrument-coverage`)—with the following concrete mechanics and measured performance properties:

1. **Binary Format Versions and Section Layouts (`InstrProfData.inc`)**:
   - In LLVM 23.1.1 (`llvm/include/llvm/ProfileData/InstrProfData.inc:776-806`), raw profiles (`.profraw`) use **`INSTR_PROF_RAW_VERSION = 11`** (64-bit little-endian magic `0xff6c70726f667281` on 64-bit targets; 32-bit magic `0xff6c70726f665281` on `i686`), with upper version-word bitflags encoding `VARIANT_MASK_IR_PROF` (`1ULL << 56`, producing raw version `0x010000000000000b` for `-C profile-generate`), `VARIANT_MASK_CSIR_PROF` (`1ULL << 57` for context-sensitive PGO), `VARIANT_MASK_BYTE_COVERAGE` (`1ULL << 60`), and `VARIANT_MASK_FUNCTION_ENTRY_ONLY` (`1ULL << 61`).
   - Indexed merged profiles (`.profdata`, produced by `llvm-profdata merge`) use **`INSTR_PROF_INDEX_VERSION = 14`** (`InstrProfData.inc:778`).
   - LLVM 23.1.1 defines **three** value-profiling kinds (`InstrProfData.inc:259-281`): `IPVK_IndirectCallTarget = 0` (`indirect call target`), `IPVK_MemOPSize = 1` (`memory intrinsic functions size`), and `IPVK_VTableTarget = 2` (`profiled address point of the vtable`).
   - On ELF targets (`aarch64-unknown-linux-gnu`, `x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`), `-C profile-generate` emits five dedicated sections into each object file: `__llvm_prf_cnts` (8-byte edge counters), `__llvm_prf_data` (per-function metadata records), `__llvm_prf_names` (compressed function symbol names), `__llvm_prf_vals` (value-profile site pointers), and `__llvm_prf_vnds` (preallocated value-profiling runtime nodes), and automatically links `libclang_rt.profile.a` from the target `rustlib` directory (`compiler/rustc_codegen_ssa/src/back/link.rs:1412-1445`).
2. **PGO Pre-Inliner and Minimum-Spanning-Tree CFG Hash (`PGOInstrumentation.cpp`)**:
   - When `-C profile-generate` or `-C profile-use` is active, `PassBuilder::buildModuleSimplificationPipeline` (`llvm/lib/Passes/PassBuilderPipelines.cpp:1087-1155`) runs a dedicated **PGO Pre-Inliner** CGSCC pass (`inline<only-mandatory>, inline<threshold=75>`) followed by `FunctionSimplificationPipeline` *before* `pgo-instr-gen` or `pgo-instr-use`, reducing counter overhead and ensuring that small Rust wrappers/iterators are inlined identically before CFG hashing.
   - `FuncPGOInstrumentation::computeCFGHash` (`llvm/lib/Transforms/Instrumentation/PGOInstrumentation.cpp:698-745`) constructs a Minimum Spanning Tree (`CFGMST`) of the function's basic-block edges (instrumenting only non-MST chord edges) and computes a 60-bit `FunctionHash` (`FUNC_HASH_MASK = 0x0fffffffffffffffULL`, reserving bit 60 for `CSFlagInHash`):
     - **Lower 32 bits (`JC.getCRC()`)**: `JamCRC` (CRC-32C) over the little-endian `uint32_t` BB indices of every successor edge `(BB -> Succ)` in the CFG.
     - **Upper 28 bits (`(JCH.getCRC() << 28) & FUNC_HASH_MASK`)**: `JamCRC` over four 64-bit little-endian counts: `NumOfSelectInsts`, `ValueSites[IPVK_IndirectCallTarget].size()`, `ValueSites[IPVK_MemOPSize].size()`, and `MST.numEdges()`.
3. **Empirical PGO Value and Heuristic Decomposition (`x86_64` and `i686`)**:
   - On the multi-stage dispatch, branch, and slice-copy benchmark (`support/run_pgo_experiments.py`, `support/pgo_heuristic_attribution.csv`), 2-stage PGO (`PGO_Full_O3`) reduces median runtime from `2,494.39` $\mu\text{s}$ to **`967.61` $\mu\text{s}$ (`61.21%` speedup)** on `x86_64-unknown-linux-gnu` and from `2,873.16` $\mu\text{s}$ to **`2,409.48` $\mu\text{s}$ (`16.14%` speedup)** on `i686-unknown-linux-gnu`, while also shrinking `.text` by `592 B` (`251,379 B` $\rightarrow$ `250,787 B`) on `x86_64` and `256 B` (`266,115 B` $\rightarrow$ `265,859 B`) on `i686` via cold-callsite inlining suppression (`226` $\rightarrow$ `219` inlined callsites).
   - **Heuristic attribution**: On `x86_64`, value-profiled `MemOpSize` specialization (`IPVK_MemOPSize` specializing the 99%-frequent 16-byte `copy_from_slice` `memcpy` call into inline SSE loads/stores) accounts for **52.07 percentage points** of the `61.21%` speedup (disabling `-disable-memop-opt=true` drops the speedup to `9.14%`), while Indirect Call Promotion (`IPVK_IndirectCallTarget` promoting the 96.8%-frequent `&dyn StageOp` vtable call to a direct conditional branch) and PGO inlining account for the remaining `9.14%`. On `i686`, Indirect Call Promotion accounts for **9.24 percentage points** (`16.14%` $\rightarrow$ `6.90%` when `-disable-icp=true` is passed) and `MemOpSize` specialization accounts for **6.49 percentage points** (`16.14%` $\rightarrow$ `9.65%`).
4. **Stale-Profile Sensitivity and `rustc` Symbol-Mangling Pitfall**:
   - Because `rustc` encodes the crate name and `-C metadata` disambiguator hash (`StableCrateId`) into every mangled Rust symbol (`_RNvCs<crate_hash>_...`), changing the crate name or `-C metadata` between `-C profile-generate` and `-C profile-use` causes **100% (`18 / 18`) of internal Rust functions to miss** in `.profdata` (`llvm_missing_function_warnings = 18`, collapsing the PGO speedup from `61.21%` to `0.75%`).
   - When `--crate-name` and `-C metadata` are held constant across four source mutations (`support/stale_profile_sensitivity.json`):
     - `M1_RenameInternalHelper` (renaming a helper that the PGO pre-inliner inlines before `pgo-instr-gen`), `M3_RefactorLoopConstruct` (`while` $\rightarrow$ `for i in 0..iters` producing an isomorphic LLVM CFG after pre-inlining), and `M4_ReorderBranchArms` (`if cond { A } else { B }` $\rightarrow$ `if !cond { B } else { A }`, which has the same BB successor edge count and `Select`/`ICall`/`MemOp` counts) retain **99.8% to 99.9%** of the PGO speedup (`0` hash mismatch warnings; note that `M4` silently inverts branch probabilities without changing `computeCFGHash()` unless `-pgo-warn-misexpect` is used!).
     - By contrast, `M2_InsertColdLoggingBranchInHotLoop` adds two basic blocks and three CFG edges to `<OpFastAdd as StageOp>::execute`, changing `computeCFGHash()` (`llvm_cfg_hash_mismatch_warnings = 1`: `function control flow change detected (hash mismatch)`), discarding the function's entire counter and `MemOpSize` profile, and collapsing the retained PGO gain from **`99.6%` to `9.4%`** (`959.12` $\mu\text{s}$ $\rightarrow$ `2,302.44` $\mu\text{s}$).

## Applicability

- **Subjects**: `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).
- **Relation to other corpus packages**: Extends `rustc-llvm-pass-pipelines-and-configuration` (`O1`), uses the statistical methodology in `rustc-experimental-corpora-and-harness-conventions` (`P2`), and informs the design of an LLVM-independent profile format for a verified `rustc` backend.

## Findings

### 1. `.profraw` v11 and `.profdata` v14 Binary Layouts and Value Profiling

`Basis: source + execution (llvm/include/llvm/ProfileData/InstrProfData.inc:200-285, 776-806; support/stale_profile_sensitivity.json)`

In LLVM 23.1.1, `-C profile-generate` emits raw profiles with a 136-byte (`17 × uint64_t`) header (`__llvm_profile_header` defined by `INSTR_PROF_RAW_HEADER` in `InstrProfData.inc:202-222`):

| Offset (Bytes) | Field Name (`InstrProfData.inc`) | Type | Observed Value on `x86_64` (`support/stale_profile_sensitivity.json`) | Semantic Role |
| ---: | :--- | :--- | :--- | :--- |
| `0` | `Magic` | `uint64_t` | `0xff6c70726f667281` (`\x81rforpl\xff`; `0xff6c70726f665281` on 32-bit `i686`) | Identifies raw instrprof endianness and pointer width |
| `8` | `Version` | `uint64_t` | `0x010000000000000b` (`BaseVersion = 11` \| `VARIANT_MASK_IR_PROF`) | Format version `11` + high-32-bit variant mask (`IR_PROF = 1<<56`, `CSIR_PROF = 1<<57`, `BYTE_COVERAGE = 1<<60`, `FUNCTION_ENTRY_ONLY = 1<<61`) |
| `16` | `BinaryIdsSize` | `uint64_t` | `32` | Byte length of embedded ELF `.note.gnu.build-id` section |
| `24` | `NumData` | `uint64_t` | `19` | Number of `__llvm_profile_data` function records |
| `32` | `PaddingBytesBeforeCounters` | `uint64_t` | `0` | Alignment padding before counter array |
| `40` | `NumCounters` | `uint64_t` | `143` | Total 64-bit edge/block counters in `__llvm_prf_cnts` |
| `48` | `PaddingBytesAfterCounters` | `uint64_t` | `0` | Alignment padding after counter array |
| `56` | `NumBitmapBytes` | `uint64_t` | `0` | Modified Condition/Decision Coverage (MC/DC) bitmap bytes |
| `64` | `PaddingBytesAfterBitmapBytes` | `uint64_t` | `0` | Alignment padding after MC/DC bitmaps |
| `72` | `NumTemporalProfTraces` / `NumUniformCounters` | `uint64_t` | `0` | Temporal / uniform counter count |
| `80` | `PaddingBytesAfterUniformCounters` | `uint64_t` | `0` | Alignment padding |
| `88` | `NamesSize` | `uint64_t` | `449` (in object `__llvm_prf_names`) | Size of zlib-compressed or raw function name table |
| `96` | `CountersDelta` | `uint64_t` | Relative pointer delta `CountersBegin - DataBegin` | Relocates per-function counter pointers without dynamic relocations |
| `104` | `BitmapDelta` | `uint64_t` | `BitmapBegin - DataBegin` | Relocates MC/DC bitmap pointers |
| `112` | `NamesDelta` | `uint64_t` | `NamesBegin` | Base address of `__llvm_prf_names` |
| `120` | `NumVTables` | `uint64_t` | `0` (unless `-enable-vtable-value-profiling`) | VTable profile data entries (`IPVK_VTableTarget`) |
| `128` | `ValueKindLast` | `uint64_t` | `2` (`IPVK_Last = IPVK_VTableTarget`) | Highest `InstrProfValueKind` enum value |

Each function's `__llvm_profile_data` record (`72` bytes on 64-bit targets) stores:
1. `NameRef` (`uint64_t`): Lower 64 bits of the MD5 hash of the function's PGO symbol name (`IndexedInstrProf::ComputeHash`, `llvm/include/llvm/ProfileData/InstrProf.h:1069-1075`). For internal (`local` linkage) functions, `getIRPGOFuncName` prepends `<source_filename>;` before hashing.
2. `FuncHash` (`uint64_t`): The 60-bit `FunctionHash` computed by `FuncPGOInstrumentation::computeCFGHash` (`PGOInstrumentation.cpp:698-745`).
3. `CounterPtr` (`intptr_t`), `BitmapPtr` (`intptr_t`), `FunctionPointer` (`intptr_t`), `Values` (`void*`), `NumCounters` (`uint32_t`), and `NumValueSites[3]` (`uint16_t[3]` for `IPVK_IndirectCallTarget`, `IPVK_MemOPSize`, and `IPVK_VTableTarget`).

---

### 2. Which LLVM Passes Consume Profiles and How Much Each Buys on Rust Code

`Basis: source + execution (support/run_pgo_experiments.py, support/pgo_heuristic_attribution.csv)`

In `rustc` 1.99.1 / LLVM 23.1.1 (`support/newpm_O2_pgo_use.txt` in `rustc-llvm-pass-pipelines-and-configuration`), profile weights attached by `pgo-instr-use` (`!prof !{"branch_weights", ...}` and `!VP` metadata) are consumed by seven downstream passes:

| Profile Consumer Pass | LLVM Flag / Threshold Controlled | Empirical Effect When Disabled in `support/pgo_heuristic_attribution.csv` |
| :--- | :--- | :--- |
| **`MemOpOpt` (`PGOMemOPSizeOpt.cpp`)** | `-disable-memop-opt` (`-memop-max-annotations=4`) | Specializes variable-length `llvm.memcpy`/`llvm.memmove`/`llvm.memset` calls for the hottest observed byte sizes (`16 B` in `OpFastAdd::execute`). Disabling it drops the `x86_64` PGO speedup from **`61.21%` (`967.61` $\mu\text{s}$) to `9.14%` (`2,266.28` $\mu\text{s}`)** and the `i686` speedup from **`16.14%` to `9.65%`**. |
| **`PGOIndirectCallPromotion` (`IndirectCallPromotion.cpp`)** | `-disable-icp` (`-icp-max-annotations=3`, `-icp-remaining-percent-threshold=30`) | Reads `!VP` (`IPVK_IndirectCallTarget`) metadata on vtable / `fn` pointer calls and emits `if (callee_ptr == &HotTarget) HotTarget(...) else (*callee_ptr)(...)`, enabling downstream CGSCC inlining of the promoted direct call. Disabling it on `i686` drops the PGO speedup from **`16.14%` (`2,409.48` $\mu\text{s}$) to `6.90%` (`2,674.86` $\mu\text{s}`)**. |
| **CGSCC Inliner (`InlineCost.cpp`)** | `-hot-callsite-threshold=3000` (vs. `225`/`250`), `-inline-cold-callsite-threshold=45` | Boosts hot-callsite inline budget by $12\times$ (`3000` vs `250`) while shrinking cold-callsite inline budget to `45`, reducing total inlined callsites in our benchmark from `226` (`NoPGO`) to `219` (`PGO_Full_O3`) and shrinking `.text` by `592 B` on `x86_64`. |
| **`MachineBlockPlacement` & Tail Duplication (`MachineBlockPlacement.cpp`)** | `-disable-block-placement`, `-tail-dup-placement` | Applies Pettis–Hansen chain layout so high-probability branches fall through without taken jumps and cold blocks move to the end of the function. |
| **Hot/Cold Splitting & Machine Function Splitting** | `-hot-cold-split`, `-split-machine-functions` | Extracts zero-count cold basic blocks into `.text.split.<fn>` / `.text.unlikely.<fn>` sections to reduce instruction-cache footprint on large functions. |
| **Register Allocation Spill Weight Scaling (`CalcSpillWeights.cpp`)** | `MBFI.getBlockFreq(MBB)` | Scales virtual-register live-interval spill weights by profile-derived `MachineBlockFrequencyInfo`, keeping hot-loop variables in GPRs across calls in cold branches. |

---

### 3. Stale-Profile Sensitivity and Designing an IR-Portable Profile Format for a Verified Backend

`Basis: source + execution (compiler/rustc_mir_transform/src/coverage/, support/stale_profile_sensitivity.json)`

Table 2 compares how LLVM's `PGOInstrumentation` (MD5 symbol name + 60-bit `CFGMST` hash) behaves across four source mutations on `x86_64-unknown-linux-gnu` versus MIR-level coverage counter mapping (`compiler/rustc_mir_transform/src/coverage/graph.rs`):

| Source Mutation | `x86_64` Runtime ($\mu\text{s}$) | Speedup vs. No-PGO (`2,494.39` $\mu\text{s}$) | Retained PGO Gain (%) | LLVM Missing-Fn Warnings | LLVM CFG Hash Mismatch Warnings | Failure / Survival Mechanism |
| :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| `Unpinned_CrateName` (filename changed without `--crate-name`) | 2,475.64 | +0.75% | **1.2%** | **18** | 0 | Changing crate name or `-C metadata` alters v0 mangled symbol names (`_RNvCs...`), missing 100% of Rust functions! |
| `M0_Unmodified` (same `--crate-name` & `-C metadata`) | 959.12 | +60.73% | **99.6%** | 0 | 0 | Exact `NameRef` MD5 and 60-bit `FunctionHash` match. |
| `M1_RenameInternalHelper` (`hot_helper_transform` $\rightarrow$ `_v2`) | 954.38 | +60.92% | **99.9%** | 0 | 0 | Helper is inlined into `OpFastAdd::execute` by the PGO Pre-Inliner *before* `pgo-instr-gen`/`use`, so caller `FunctionHash` is unchanged. |
| `M2_InsertColdLoggingBranchInHotLoop` (+1 cold `if` in `OpFastAdd::execute`) | **2,302.44** | **+5.73%** | **9.4%** | 0 | **1** | Adding 1 `if` adds 2 BBs and 3 CFG edges, altering `JC.getCRC()` and `MST.numEdges()`. LLVM drops the entire function's counters and `MemOpSize` profile! |
| `M3_RefactorLoopConstruct` (`while i < iters` $\rightarrow$ `for i in 0..iters`) | 956.34 | +60.84% | **99.8%** | 0 | 0 | The PGO Pre-Inliner (`threshold=75`) + `sroa` + `simplifycfg` canonicalizes `Range::next` to the exact same 2-BB loop CFG before `computeCFGHash()`. |
| `M4_ReorderBranchArms` (`if (x & 0x7f) == 0` $\rightarrow$ `!= 0` with swapped arms) | 955.62 | +60.87% | **99.8%** | 0 | 0 | **Silent mis-association hazard**: Swapping `then`/`else` arms keeps identical BB successor indices and `MST.numEdges()`, so `FunctionHash` does not change (`0` hash mismatch warnings!), applying the old `then` counter to the new `then` arm unless `-pgo-warn-misexpect` or condition hashing is used. |

#### Architectural Recommendations for an Independent Verified Backend's Profile Pipeline:
1. **Key Function Profiles by Un-Disambiguated DefPath + HIR/THIR Structural Hash (NotCrate-Hash-Mangled Symbol Name)**:
   - Stripping the `-C metadata` crate disambiguator hash from the profile key prevents `cargo` feature/metadata rebuilds from invalidating 100% of function profiles.
2. **Anchor Counters to MIR `BasicCoverageBlock` (`BCB`) Source Spans and `SwitchInt` Values Rather Than Unlabeled CFG Edge Indices**:
   - In `compiler/rustc_mir_transform/src/coverage/`, `rustc` already builds a `CoverageGraph` of `BasicCoverageBlock`s at `MirPhase::Analysis(Initial)` (before MIR or LLVM optimizations) and maps each `BCB` to stable HIR `Span`s and `SwitchInt` discriminant values.
   - Keying branch weights by `(DefPathHash, TerminatorKind, ArmDiscriminantOrSourceSpanHash)` rather than a whole-function `JamCRC` over all BB indices fixes both of LLVM's failure modes observed above:
     - Adding a cold logging `if` (`M2`) only introduces one new unprofiled branch (defaulting to static heuristics) while preserving the existing branch weights and `MemOpSize` annotations in the rest of the function; and
     - Swapping `if`/`else` or `match` arms (`M4`) preserves the association between each arm's condition/discriminant and its profile weight instead of silently inverting hot and cold arms.

## Boundaries

- **BOLT (`llvm-bolt`) and Hardware LBR Sample PGO (`-Z profile-sample-use`)**: Hardware Last Branch Record (`perf record -b` $\rightarrow$ `llvm-profgen` $\rightarrow$ `-Z profile-sample-use`) and post-link binary optimization (`llvm-bolt`) depend on physical CPU PMU LBR sampling registers (`perf_event_open` with `PERF_SAMPLE_BRANCH_STACK`), which are virtualized away inside containerized/cloudtop guest environments. Their static pipeline integration in `rustc` (`get_pgo_sample_use_path` in `write.rs:520-525` and `PassWrapper.cpp:741-754`) is fully audited in Section 1.

## Evidence

- **Reproducible harness and datasets**:
  - `support/run_pgo_experiments.py`
  - `support/pgo_heuristic_attribution.csv` (14 rows across `x86_64` and `i686` heuristic ablations)
  - `support/stale_profile_sensitivity.json` (`.profraw` v11 header decoding, `.profdata` value-site histograms, AArch64 `__llvm_prf_*` section sizes, and `M0`–`M4` stale-profile mutation results)
- **Primary source citations**:
  - `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):
    - `compiler/rustc_codegen_llvm/src/back/write.rs:498-532, 611-614, 799-805` (`get_pgo_gen_path`, `get_pgo_use_path`, `get_pgo_sample_use_path`)
    - `compiler/rustc_codegen_ssa/src/back/link.rs:1412-1445` (profiler runtime archive `libclang_rt.profile.a` linking)
    - `compiler/rustc_mir_transform/src/coverage/mod.rs` and `graph.rs` (MIR-level `InstrumentCoverage` and `BasicCoverageBlock` graph)
  - `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):
    - `llvm/include/llvm/ProfileData/InstrProfData.inc:202-285, 776-806` (`INSTR_PROF_RAW_VERSION = 11`, `INSTR_PROF_INDEX_VERSION = 14`, `IPVK_*` value kinds, `VARIANT_MASK_*`)
    - `llvm/lib/Transforms/Instrumentation/PGOInstrumentation.cpp:178-209, 598-745` (`FuncPGOInstrumentation`, `computeCFGHash`)

## Revalidation

Run `support/run_pgo_experiments.py`:

```bash
python3 reports/rustc-pgo-mechanics-heuristics-value-and-ir-portability/support/run_pgo_experiments.py \
  --toolchain 1.99.1-x86_64-unknown-linux-gnu \
  --out-dir /tmp/v7_reval
```

Compare `/tmp/v7_reval/pgo_heuristic_attribution.csv` and `/tmp/v7_reval/stale_profile_sensitivity.json` against `support/`.
