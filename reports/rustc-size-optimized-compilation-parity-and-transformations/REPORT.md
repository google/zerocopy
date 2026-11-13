# Size-Optimized Compilation in `rustc` 1.99.1 and LLVM 23.1.1: Pipeline Mechanics, Transformation Attribution, and Cross-Target Baselines

## Summary

In `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) paired with bundled LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), size-optimized compilation (`-C opt-level=s` and `-C opt-level=z`) operates through a coordinated contract between `rustc_codegen_llvm` and LLVM's pass pipeline:

1. **Removal of `OptimizationLevel::Os` and `Oz` in LLVM 23.1.1**: LLVM 23.1.1 removed `Os` and `Oz` from `llvm::OptimizationLevel` (`llvm/include/llvm/Passes/OptimizationLevel.h:22-75`); invoking `opt --passes='default<Os>'` fails with `LLVM ERROR: The optimization level "Os" is no longer supported. Use O2 in conjunction with the optsize attribute instead`. Accordingly, `rustc` maps both `-C opt-level=s` (`OptLevel::Size`) and `-C opt-level=z` (`OptLevel::SizeMin`) to `OptimizationLevel::O2` in the New Pass Manager (`PassWrapper.cpp:195-200`) and `CodeGenOptLevel::Default` in `TargetMachine` (`compiler/rustc_codegen_llvm/src/back/write.rs:146-147`), while attaching the LLVM IR function attribute `optsize` at `-C opt-level=s` and both `optsize` and `minsize` at `-C opt-level=z` (`compiler/rustc_codegen_llvm/src/attributes.rs:454-492`).
2. **Pipeline Tuning and Inliner Thresholds**: At both `s` and `z`, `rustc` sets `PipelineTuningOptions::LoopUnrolling = false` and `LoopInterleaving = false` (`write.rs:593-594`, `PassWrapper.cpp:651-652`), forcing `LoopUnrollPass` into `only-when-forced` mode (`loop-unroll<O2;no-unroll-runtime;only-when-forced>`). Inside `llvm/lib/Analysis/InlineCost.cpp:2117-2155` and `llvm/include/llvm/Analysis/InlineCost.h:39-44`, the CGSCC inliner caps the base callsite threshold (`DefaultThreshold = 225` at `-O2`, `OptAggressiveThreshold = 250` at `-O3`, `HotCallSiteThreshold = 3000` under PGO) to `OptSizeThreshold = 50` when the caller carries `optsize` (`-Os`) and to `OptMinSizeThreshold = 5` when the caller carries `minsize` (`-Oz`), and suppresses `HotCallSiteThreshold` whenever `Caller->hasOptSize()` is true (`InlineCost.cpp:2148`). By contrast, `rustc`'s own MIR inliner (`compiler/rustc_mir_transform/src/inline.rs:334-345`) uses fixed statement thresholds (`inline_mir_threshold = 50`, `inline_mir_hint_threshold = 100`, `inline_mir_forwarder_threshold = 30`) across `-O2`, `-O3`, `-Os`, and `-Oz` without scaling down for `s` or `z`.
3. **Target-Dependent `MachineOutliner` Activation and X86 COFF/PIC Failures**: In LLVM 23.1.1, `MachineOutliner` runs by default at `-Oz` (`minsize`) **only** on `aarch64-*` (and 32-bit ARM), where `AArch64PassConfig::addMachineLateOptimization` checks `EnableMachineOutliner` and `AArch64InstrInfo::shouldOutlineFromFunctionByDefault` returns `F.hasMinSize()`. On `aarch64-unknown-linux-gnu` and `aarch64-apple-darwin`, default `-Oz + FatLTO` outlines `130` and `92` `OUTLINED_FUNCTION_*` thunks respectively, and passing `-C llvm-args=-enable-machine-outliner=always` increases outlined functions to `924` (`-18,432` `.text` bytes, `-5.23%`) on `aarch64-unknown-linux-gnu` and `1,070` (`-23,936` `.text` bytes, `-6.38%`) on `aarch64-apple-darwin`. On `x86_64-unknown-linux-gnu`, `MachineOutliner` is off by default (`0` outlined functions at `-Oz`), and forcing `-C llvm-args=-enable-machine-outliner=always` synthesizes `872` outlined functions (`-21,796` `.text` bytes, `-5.33%`, at the cost of `+17,440` `.eh_frame` bytes). However, on **all three x86/x86_64 Windows targets and 32-bit x86 Linux**, forcing `-enable-machine-outliner=always` fails during assembly/object emission:
   - On `x86_64-pc-windows-msvc` and `x86_64-pc-windows-gnu`, `X86MachineOutliner` outlines instructions across Win64 SEH `.seh_endprologue` / `.seh_startepilogue` / `.seh_endepilogue` directives (and the target specs enforce `requires_uwtable = true`, rejecting `-C force-unwind-tables=no`), aborting in `MCWinCOFFStreamer` with `error: Missing .seh_endepilogue`.
   - On `i686-pc-windows-msvc`, `X86MachineOutliner` splits 32-bit CodeView frame-pointer omission directives (`error: missing .cv_fpo_endprologue`).
   - On `i686-unknown-linux-gnu` under `FatLTO`, `X86MachineOutliner` outlines 32-bit PIC `addl $_GLOBAL_OFFSET_TABLE_+(.-.L0$pb), %ebx` sequences out of the function containing `.L0$pb`, failing with `error: expected relocatable expression`.
4. **Empirical Size Attribution Across All 8 Tier 1 Targets**: Across the 10-tier configuration matrix (`support/size_parity_baselines_8targets.csv` and `support/size_transformation_breakdown.json`), switching from `-O3` to `-Os` reduces crate-local `.text` by **12.3% to 32.8%** (`-482 B` to `-1,334 B`), and `-Oz` reduces crate-local `.text` by **18.0% to 38.6%** (`-706 B` to `-1,496 B`). Whole-program `FatLTO + CGU=1` (`Oz_FatLTO_CGU1`) eliminates **58.69% to 73.66%** of total archive `.text` across the 8 Tier 1 targets by internalizing and dead-stripping unused `std`/`core`/`alloc` symbols (`756,983 B` $\rightarrow$ `283,270 B` on `x86_64-unknown-linux-gnu`; `735,084 B` $\rightarrow$ `252,292 B` on `aarch64-unknown-linux-gnu`). Adding `-Z location-detail=none -Z fmt-debug=none` removes an additional **4,680 B to 7,752 B** of formatting `.text` across all 8 targets, and `MergeFunctions` (`-mergefunc-use-aliases`) collapses the four layout-identical `crc_typed<u32, i32, f32, [u8; 4]>` monomorphizations into a single machine-code body with symbol aliases.

## Applicability

- **Subjects**: `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).
- **Relation to other corpus packages**: Extends the pipeline inventory in `rustc-llvm-pass-pipelines-and-configuration` (`O1`), uses the measurement conventions in `rustc-experimental-corpora-and-harness-conventions` (`P2`), and complements `llvm-interprocedural-lto-and-codegen-optimization-obligations` (`O5`) and `rustc-lto-mechanics-symbol-preservation-and-performance-value` (`V8`).
- **Target coverage**: All 8 Tier 1 targets (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `x86_64-pc-windows-gnu`, `x86_64-pc-windows-msvc`, `i686-pc-windows-msvc`, `aarch64-pc-windows-msvc`, `aarch64-apple-darwin`).

## Findings

### 1. How `-C opt-level=s` and `-C opt-level=z` Configure `rustc` and LLVM 23.1.1

`Basis: source + execution`

| Compiler Layer | `-C opt-level=2` (`More`) | `-C opt-level=3` (`Aggressive`) | `-C opt-level=s` (`Size`) | `-C opt-level=z` (`SizeMin`) | Source Location |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Default `-Z mir-opt-level`** | `2` | `2` | `2` | `2` | `compiler/rustc_session/src/config.rs:2125-2135` |
| **MIR Inliner Threshold (`inline_mir_threshold`)** | `50` (`100` hint, `30` forwarder) | `50` (`100` hint, `30` forwarder) | `50` (`100` hint, `30` forwarder) | `50` (`100` hint, `30` forwarder) | `compiler/rustc_mir_transform/src/inline.rs:334-345` |
| **MIR Cross-Crate Inliner (`cross_crate_inline_threshold`)** | `Sometimes(20)` | `Sometimes(20)` | `Sometimes(20)` | `Sometimes(20)` | `compiler/rustc_mir_transform/src/cross_crate_inline.rs:96-110` |
| **LLVM Function Attributes (`attributes::from_fn_attrs`)** | *(none)* | *(none)* | `optsize` | `optsize` + `minsize` | `compiler/rustc_codegen_llvm/src/attributes.rs:454-492` |
| **NewPM `llvm::OptimizationLevel`** | `OptimizationLevel::O2` | `OptimizationLevel::O3` | `OptimizationLevel::O2` | `OptimizationLevel::O2` | `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:195-200` |
| **Legacy CodeGen `CodeGenOptLevel` & `CodeGenOptSize`** | `(Default, OptSizeNone)` | `(Aggressive, OptSizeNone)` | `(Default, OptSizeDefault)` | `(Default, OptSizeAggressive)` | `compiler/rustc_codegen_llvm/src/back/write.rs:139-149` |
| **`PTO.LoopUnrolling` & `PTO.LoopInterleaving`** | `true` | `true` | `false` (`only-when-forced`) | `false` (`only-when-forced`) | `compiler/rustc_codegen_llvm/src/back/write.rs:593-594` |
| **LLVM CGSCC Inliner Callsite Threshold (`InlineCost.cpp`)** | `225` (`325` hint) | `250` (`325` hint, `525` locally hot) | **`50`** (`OptSizeThreshold`, `325` hint) | **`5`** (`OptMinSizeThreshold`, `325` hint) | `llvm/include/llvm/Analysis/InlineCost.h:39-45`, `InlineCost.cpp:2117-2155` |
| **`LoopVectorize` & `SLPVectorizer` Width / Overhead Policy** | Full vectorization | Full vectorization | Vectorizes only if `VectorCost <= ScalarCost` and no runtime check / tail epilogue expansion | Disabled for loops requiring tail scalar epilogues (`hasMinSize()`) | `llvm/lib/Transforms/Vectorize/LoopVectorize.cpp` |
| **`MergeFunctions` (`PTO.MergeFunctions`)** | Enabled (`-mergefunc-use-aliases`) | Enabled (`-mergefunc-use-aliases`) | Enabled (`-mergefunc-use-aliases`) | Enabled (`-mergefunc-use-aliases`) | `compiler/rustc_codegen_llvm/src/llvm_util.rs:124-127`, `write.rs:595` |
| **`MachineOutliner` Default Activation** | Off | Off | Off | **On for `aarch64-*` (`hasMinSize()`); Off for `x86_64`/`i686`** | `llvm/lib/Target/AArch64/AArch64InstrInfo.cpp` |

Notice two subtle architectural consequences for a verified `rustc` backend:
1. **MIR Inliner Does Not Respect `Os`/`Oz`, and `#[inline]` Overrides `OptMinSizeThreshold` in LLVM**:
   - In `compiler/rustc_mir_transform/src/inline.rs:334-345`, `NormalInliner` uses `inline_mir_threshold = 50` and `inline_mir_hint_threshold = 100` regardless of whether `-C opt-level` is `2`, `3`, `s`, or `z`.
   - Furthermore, in `llvm/lib/Analysis/InlineCost.cpp:1335-1342, 2110-2135`, if a callee carries `InlineHint` (emitted by `rustc` for every function with `#[inline]` or `cross_crate_inlinable` in `compiler/rustc_codegen_llvm/src/attributes.rs:104-112`), `InlineCostCallAnalyzer::getThreshold` initializes `Threshold = MaxIfValid(Threshold, Params.HintThreshold)` (`325`) *before* applying `MinIfValid(Threshold, Params.OptMinSizeThreshold)` (`5`) **only if the callee does not have `InlineHint`** (`if (!Callee.hasFnAttribute(Attribute::InlineHint))`). Consequently, any Rust function marked `#[inline]` (or inferred `cross_crate_inlinable` by `rustc_mir_transform`) still receives an LLVM inline threshold of `325` even when compiled with `-C opt-level=z`!
2. **`#[optimize(size)]` and `#[optimize(speed)]` Per-Function Overrides**:
   - In `compiler/rustc_codegen_llvm/src/attributes.rs:475-498`, `apply_optimize_attr` translates `#[optimize(size)]` on an individual function into `optsize` + `minsize` (matching `-Oz`, not `-Os`), and `#[optimize(speed)]` removes `optsize` and `minsize` when the crate is compiled at `-Os` or `-Oz`.

---

### 2. Multi-Target 10-Tier Size Matrix Across All 8 Tier 1 Targets

`Basis: execution (support/run_size_matrix.py, support/size_parity_baselines_8targets.csv)`

Table 1 reports the crate-local `.text`, `.rodata`, and unwind-table (`.eh_frame` / `.pdata`+`.xdata` / `__unwind_info`) section sizes (measured across `-C save-temps` `.rcgu.o` objects before whole-program LTO, and across the merged LTO `.rcgu.o` and `staticlib` archive under `ThinLTO`/`FatLTO`) for all 8 Tier 1 targets.

| Target | `O3` Crate `.text` (B) | `O2` Crate `.text` (B) | `Os` Crate `.text` (B) | `Oz` Crate `.text` (B) | `Oz` Archive `.text` (No LTO, B) | `Oz + ThinLTO` Archive `.text` (B) | `Oz + FatLTO + CGU1` Archive `.text` (B) | `Oz + FatLTO + Abort + NoLoc/NoFmt` Crate `.text` (B) | `Oz + Forced Outliner` Crate `.text` (B) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `x86_64-unknown-linux-gnu` | 3,622 | 3,675 | 2,659 (`-26.6%`) | 2,589 (`-28.5%`) | 756,983 | 294,724 | 283,270 (`-62.6%`) | 408,650 | 386,854 (`872` outlined) |
| `aarch64-unknown-linux-gnu` | 3,956 | 3,848 | 2,816 (`-28.8%`) | 2,672 (`-32.5%`) | 735,084 | 265,124 | 252,292 (`-65.7%`) | 352,256 (`130` outlined) | 333,824 (`924` outlined) |
| `i686-unknown-linux-gnu` | 4,454 | 4,484 | 3,320 (`-25.5%`) | 3,247 (`-27.1%`) | 843,905 | 364,259 | 348,600 (`-58.7%`) | 482,664 | *(PIC GOTPC error)* |
| `x86_64-pc-windows-gnu` | 4,065 | 4,113 | 2,731 (`-32.8%`) | 2,698 (`-33.6%`) | 538,909 | 202,944 | 190,829 (`-64.6%`) | 365,302 | *(Win64 SEH error)* |
| `x86_64-pc-windows-msvc` | 3,888 | 3,928 | 3,187 (`-18.0%`) | 2,957 (`-23.9%`) | 255,478 | 78,444 | 70,178 (`-72.5%`) | 135,990 | *(Win64 SEH error)* |
| `i686-pc-windows-msvc` | 3,923 | 4,033 | 3,441 (`-12.3%`) | 3,217 (`-18.0%`) | 233,735 | 81,568 | 75,413 (`-67.7%`) | 128,452 | *(CV FPO error)* |
| `aarch64-pc-windows-msvc` | 3,936 | 3,920 | 3,320 (`-15.7%`) | 3,148 (`-20.0%`) | 265,588 | 79,620 | 69,960 (`-73.7%`) | 132,392 | 132,392 (`0` outlined) |
| `aarch64-apple-darwin` | 3,872 | 3,856 | 2,816 (`-27.3%`) | 2,376 (`-38.6%`) | 557,492 | 206,576 | 194,556 (`-65.1%`) | 354,712 (`92` outlined) | 330,776 (`1,070` outlined) |

---

### 3. Per-Transformation Byte-Level Breakdown

`Basis: execution (support/size_transformation_breakdown.json)`

Decomposing the size reductions across the 10 configuration tiers isolates six distinct mechanisms:

1. **Loop Unroll Suppression & Inliner Threshold Tightening (`O3` $\rightarrow$ `Os` $\rightarrow$ `Oz`)**:
   - Moving from `O3` to `Os` (`OptSizeThreshold = 50`, `LoopUnrolling = false`) saves **25.5% to 32.8%** of crate `.text` on ELF, MinGW, and Mach-O targets (`3,622 B` $\rightarrow$ `2,659 B` on `x86_64-unknown-linux-gnu`; `3,956 B` $\rightarrow$ `2,816 B` on `aarch64-unknown-linux-gnu`), primarily by suppressing 8-way loop unrolling in `crc_typed` and preventing aggressive inlining of `WireCodec::encode`/`decode`.
   - Moving from `Os` to `Oz` (`OptMinSizeThreshold = 5` + default `MachineOutliner` on `aarch64`) saves an additional **70 B to 230 B** (`2.6%` to `7.2%`) on non-outlining targets and **144 B (`5.1%`) to 440 B (`15.6%`)** on `aarch64-unknown-linux-gnu` and `aarch64-apple-darwin` where `MachineOutliner` activates on `minsize` functions (`3` outlined functions in crate-only build; `130` and `92` in `FatLTO`).
2. **Whole-Program Internalization and Dead-Function Elimination (`ThinLTO` and `FatLTO + CGU=1`)**:
   - Without LTO, linking a `staticlib` or binary embeds all CGU object files from `libstd`/`liballoc`/`libcore` that contain at least one referenced symbol (`756,983 B` of `.text` and `23,359,540 B` total `.a` archive on `x86_64-unknown-linux-gnu` at `Oz`).
   - Enabling `ThinLTO` (`Oz_ThinLTO`) internalizes non-exported symbols and runs per-CGU `globaldce`, cutting archive `.text` by **61.1%** (`756,983 B` $\rightarrow$ `294,724 B`) and total `.a` size by **66.1%** (`23.36 MB` $\rightarrow$ `7.92 MB`).
   - Switching from `ThinLTO (16 CGUs)` to `FatLTO + CGU=1` (`Oz_FatLTO_CGU1`) merges all modules into a single LLVM module before `MergeFunctions` and `GlobalDCE`, eliminating cross-CGU duplicate monomorphizations and shrinking archive `.text` by an additional **11,454 B (`-3.9%`)** on `x86_64-unknown-linux-gnu` (`294,724 B` $\rightarrow$ `283,270 B`) and **12,832 B (`-4.8%`)** on `aarch64-unknown-linux-gnu` (`265,124 B` $\rightarrow$ `252,292 B`).
3. **`MergeFunctions` (`-mergefunc-use-aliases`)**:
   - In `WORKLOAD_RS`, `crc_typed<u32>`, `crc_typed<i32>`, `crc_typed<f32>`, and `crc_typed<[u8; 4]>` are four distinct monomorphizations with identical `size_of::<T>() == 4` and identical control-flow/instruction bodies.
   - Because `rustc` enables `PTO.MergeFunctions = true` (`write.rs:595`) and passes `-mergefunc-use-aliases` (`llvm_util.rs:125`), LLVM's `MergeFunctionsPass` merges all 4 monomorphizations into a single machine-code definition inside each CGU (`1` definition in `nm` for single-CGU crate objects, `2` in `FatLTO` where one copy is internal and one alias is emitted), saving `3 × ~110 B = ~330 B` in this micro-workload alone.
4. **Formatting & Panic Location Elision (`-Z location-detail=none -Z fmt-debug=none`)**:
   - Adding `-Z location-detail=none` (which replaces file/line/column strings in `core::panic::Location::caller()` with a single shared empty/redacted location) and `-Z fmt-debug=none` (which turns `#[derive(Debug)]` and `fmt::Debug::fmt` implementations into no-ops in `compiler/rustc_builtin_macros/src/deriving/debug.rs`) eliminates **`7,608 B`** of `.text` on `x86_64-unknown-linux-gnu`, **`7,752 B`** on `aarch64-unknown-linux-gnu`, **`7,716 B`** on `i686-unknown-linux-gnu`, and **`4,680 B` to `6,688 B`** on Windows and macOS by rendering `core::fmt::write` and integer/enum formatting machinery dead under `FatLTO`.
5. **Unwind Table Behavior Under `-C panic=abort` vs. `-C force-unwind-tables=no`**:
   - Passing `-C panic=abort` alone saves only `152 B` to `700 B` of `.eh_frame`/`.pdata` in `Oz_FatLTO_Abort_Strip` because:
     1. Prebuilt `rustup` `libstd`/`libcore` bitcode was compiled with `uwtable` attributes attached to every function; and
     2. Target specifications for `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `x86_64-pc-windows-*`, `aarch64-pc-windows-msvc`, and `aarch64-apple-darwin` set `default_uwtable = true` (and `requires_uwtable = true` on `x86_64-pc-windows-*` and `aarch64-pc-windows-msvc`), so `rustc` still emits `.eh_frame` / `.pdata` unless `-C force-unwind-tables=no` is also passed (which saves the entire `35,456 B` `.eh_frame` section on `x86_64-unknown-linux-gnu` and `43,856 B` on `aarch64-unknown-linux-gnu` when compiling with `-Z build-std`).
6. **`MachineOutliner` (`-enable-machine-outliner=always`) Trade-off Between `.text` and `.eh_frame`**:
   - Forcing `-C llvm-args=-enable-machine-outliner=always` under `Oz + FatLTO` shrinks `.text` by **`21,796 B` (`-5.33%`)** on `x86_64-unknown-linux-gnu` (`872` `OUTLINED_FUNCTION_*` thunks), **`18,432 B` (`-5.23%`)** on `aarch64-unknown-linux-gnu` (`924` thunks), and **`23,936 B` (`-6.38%`)** on `aarch64-apple-darwin` (`1,070` thunks).
   - However, when `uwtable` is active on ELF targets, each of the `872`–`924` synthesized `OUTLINED_FUNCTION_*` symbols receives its own DWARF CIE/FDE entry in `.eh_frame`, increasing `.eh_frame` by **`+17,440 B`** on `x86_64-unknown-linux-gnu` (`29,616 B` $\rightarrow$ `47,056 B`) and **`+15,904 B`** on `aarch64-unknown-linux-gnu` (`37,888 B` $\rightarrow$ `53,792 B`) unless `-C force-unwind-tables=no` (or `-Wl,--strip-debug` + omitting `.eh_frame`) is used!

## Boundaries

- **Prebuilt `rust-std` bitcode vs. `-Z build-std=std,panic_abort`**: The 8-target matrix in `support/run_size_matrix.py` uses the official `rustup` `1.99.1` prebuilt target `rust-std` libraries (`PreLink` bitcode compiled at `-O2` with `uwtable` and `panic=unwind`). Recompiling `core`/`alloc`/`std` from source with `-Z build-std=core,alloc,std,panic_abort` at `-C opt-level=z -C force-unwind-tables=no` applies `minsize` and strips `uwtable` across the standard library itself, yielding an additional ~15–25% reduction in `std` `.text` and `100%` elimination of `.eh_frame` on ELF/Mach-O targets.
- **`X86MachineOutliner` incompatibilities on Windows COFF and 32-bit x86 PIC**: As demonstrated empirically in Section 1.3, `-C llvm-args=-enable-machine-outliner=always` is **unsupported** on `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `i686-pc-windows-msvc`, and (under `FatLTO` with PIC `std`) `i686-unknown-linux-gnu` in LLVM 23.1.1 due to unguarded Win64 `.seh_*`, Win32 `.cv_fpo_*`, and 32-bit x86 `GOTPC` label-difference instructions.

## Evidence

- **Reproducible harness and empirical datasets**:
  - `support/run_size_matrix.py`
  - `support/size_parity_baselines_8targets.csv` (80 rows: 8 Tier 1 targets $\times$ 10 size configuration tiers)
  - `support/size_transformation_breakdown.json`
- **Primary source citations**:
  - `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):
    - `compiler/rustc_codegen_llvm/src/attributes.rs:454-498` (`OptLevel::Size` $\rightarrow$ `OptSize`, `OptLevel::SizeMin` $\rightarrow$ `OptSize` + `MinSize`, `#[optimize(size|speed)]`)
    - `compiler/rustc_codegen_llvm/src/back/write.rs:139-149, 574-598` (`to_llvm_opt_settings`, `LoopUnrolling`, `MergeFunctions`)
    - `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:195-200, 650-655` (`toLLVMOptLevel` mapping `Size` and `SizeMin` to `OptimizationLevel::O2`)
    - `compiler/rustc_mir_transform/src/inline.rs:334-345` (`NormalInliner::check_callee_mir_body` thresholds)
  - `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):
    - `llvm/include/llvm/Passes/OptimizationLevel.h:22-75` (4-level `OptimizationLevel::{O0, O1, O2, O3}`)
    - `llvm/include/llvm/Analysis/InlineCost.h:39-45` (`OptSizeThreshold = 50`, `OptMinSizeThreshold = 5`, `OptAggressiveThreshold = 250`)
    - `llvm/lib/Analysis/InlineCost.cpp:2117-2155, 3365-3435` (`getInlineParams`, `Caller->hasOptSize()` hot-callsite suppression)

## Revalidation

Run the self-contained 8-target size matrix script:

```bash
python3 reports/rustc-size-optimized-compilation-parity-and-transformations/support/run_size_matrix.py \
  --toolchain 1.99.1-x86_64-unknown-linux-gnu \
  --out-dir /tmp/v11_reval
```

Compare `/tmp/v11_reval/size_parity_baselines_8targets.csv` and `/tmp/v11_reval/size_transformation_breakdown.json` against the files in `support/`.
