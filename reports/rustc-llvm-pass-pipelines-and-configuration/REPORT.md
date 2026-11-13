# rustc 1.99.1 LLVM 23.1.1 Pass Pipelines, Target Machine Configuration, and Component Inventory

## Summary

`rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) drives its bundled LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) backend through a two-tier pass architecture split across `compiler/rustc_codegen_llvm/src/back/write.rs` and `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp`:

1. **Middle-end IR optimization (`LLVMRustOptimize`) uses the LLVM New Pass Manager (`llvm::PassBuilder`)**:
   - **Removal of `OptimizationLevel::Os` and `Oz` in LLVM 23**: LLVM 23.1.1 removed `Os` and `Oz` from `llvm::OptimizationLevel` (`llvm/include/llvm/Passes/OptimizationLevel.h:22-75`), leaving only `{O0, O1, O2, O3}`. In `PassWrapper.cpp:195-200`, `rustc` maps both `-C opt-level=s` and `-C opt-level=z` to `OptimizationLevel::O2`, disables loop unrolling and loop interleaving in `PipelineTuningOptions` (`write.rs:593-594`, `PassWrapper.cpp:651-652`), and relies on per-function `optsize` (`-Os`) and `minsize` (`-Oz`) IR attributes (`compiler/rustc_codegen_llvm/src/attributes.rs:47-55`) to govern size-sensitive pass thresholds (`InlineCost`, `LoopVectorize`, `SLPVectorizer`).
   - **Split Pre-Link + Module Pipeline for Bitcode-Embedding Builds (`rlib`)**: When `OptStage == PreLinkNoLTO` and bitcode embedding is active (`ThinLTOBufferRef != nullptr`, the default for `rlib` crates), `LLVMRustOptimize` (`PassWrapper.cpp:904-920`) does **not** run `PassBuilder::buildPerModuleDefaultPipeline`. Instead, it concatenates `buildThinLTOPreLinkDefaultPipeline(OptLevel)`, `ThinLTOBitcodeWriterPass` (snapshotting pre-link bitcode and summary buffers mid-pipeline), `buildModuleOptimizationPipeline(OptLevel, ThinOrFullLTOPhase::None)`, and `AnnotationRemarksPass`. Only when bitcode embedding is disabled (`-C embed-bitcode=no` or single-CGU `ThinLocal`) does `rustc` invoke `buildPerModuleDefaultPipeline(OptLevel)` (`PassWrapper.cpp:921`).
   - **LTO and ThinLocal Orchestration**: `PreLinkThinLTO` and `PreLinkFatLTO` both execute `buildThinLTOPreLinkDefaultPipeline(OptLevel)` (`PassWrapper.cpp:924-928`); `PreLinkFatLTO` then attaches the module flag `"ThinLTO" = 0` (`forceFullLTOSummary`, lines 612-625) and runs `BitcodeWriterPass` (`EmitSummaryIndex=true`), whereas `PreLinkThinLTO` runs `ThinLTOBitcodeWriterPass`. Post-link `ThinLTO` runs `buildThinLTODefaultPipeline(OptLevel, nullptr)` (`PassWrapper.cpp:932`, `4,448` chars at `-O2`), and post-link `FatLTO` runs `buildLTODefaultPipeline(OptLevel, nullptr)` (`PassWrapper.cpp:936`, `2,285` chars at `-O2`).
   - **Mandatory Suffix Passes**: Unless `OptStage` is `PreLinkThinLTO`, `PreLinkFatLTO`, or `FatLTO`, `LLVMRustOptimize` unconditionally appends `CanonicalizeAliasesPass`, `NameAnonGlobalPass`, and (new in LLVM 23) `AssignGUIDPass` (`PassWrapper.cpp:958-964`).

2. **Machine code generation (`LLVMRustWriteOutputFile`) uses the LLVM Legacy `PassManager` (`TargetMachine::addPassesToEmitFile`)**:
   - Invoked via `write_output_file` (`write.rs:53-101`) and `PassWrapper.cpp:478-517`, `addPassesToEmitFile` schedules IR-level pre-ISel lowering passes (`PreISelIntrinsicLowering`, `ExpandIRInsts`, `AtomicExpand`, `LoopStrengthReduce`, `CodeGenPrepare`, `DwarfEHPrepare`, `SafeStack`, `StackProtector`) followed by `MachineFunction` instruction selection, register allocation, scheduling, frame lowering, and `AsmPrinter` emission.
   - At `-O0`, `aarch64-unknown-linux-gnu` and `aarch64-apple-darwin` default to **GlobalISel** (`irtranslator -> aarch64-O0-prelegalizer-combiner -> localizer -> legalizer -> aarch64-postlegalizer-lowering -> regbankselect -> instruction-select`) paired with `regallocfast`, with `aarch64-isel` (`SelectionDAGISel`) retained as a fallback. At `-O1`/`-O2`/`-O3` on AArch64, and at **all** optimization levels (`-O0` through `-O3`) on `x86_64` and `i686`, LLVM uses `SelectionDAGISel` (`FastISel` + `SelectionDAG` fallback at `-O0`; full `SelectionDAG` + `RAGreedy` at `-O1`/`-O2`/`-O3`).

3. **Target Machine and Global Option Defaults**:
   - `rustc` sets two non-default global `cl::opt` flags on every invocation (`llvm_util.rs:136-139`): `-preserve-alignment-assumptions-during-inlining=false` and `-import-cold-multiplier=0.1` (plus `-generate-arange-section` and `-mergefunc-use-aliases` on targets where `MergeFunctions::Aliases` is default).
   - `LLVMRustCreateTargetMachine` (`PassWrapper.cpp:390-410`) enables `Options.TrapUnreachable = true` by default and sets `Options.NoTrapAfterNoreturn = true` on all targets **except** WebAssembly and Windows (`!Trip.isWasm() && !Trip.isOSWindows()`), preserving return-address ranges inside `.pdata` unwind tables on Windows SEH (`rust-lang/rust#140489`).

4. **Linked LLVM Components and Footprint**:
   - `compiler/rustc_llvm/build.rs:11-35` links 8 required components (`ipo`, `bitreader`, `bitwriter`, `linker`, `asmparser`, `lto`, `coverage`, `instrumentation`) and up to 19 optional target components (`x86`, `arm`, `aarch64`, `amdgpu`, `avr`, `loongarch`, `m68k`, `csky`, `mips`, `powerpc`, `systemz`, `webassembly`, `msp430`, `sparc`, `nvptx`, `hexagon`, `riscv`, `xtensa`, `bpf`), pulling in 19 core `llvm/lib/*` subdirectories totaling `2,261,841` LOC (`894,388` LOC in `lib/Target`, `445,509` LOC in `lib/Transforms`, `388,377` LOC in `lib/CodeGen`, `110,582` LOC in `lib/Analysis`, `96,384` LOC in `lib/Support`, `81,734` LOC in `lib/IR`). In the official `1.99.1-x86_64-unknown-linux-gnu` toolchain, the BOLT-optimized shared library `libLLVM.so.23.1-rust-1.99.1-stable` is `208,167,760` bytes (`198.5` MiB).

## Applicability

These findings apply to `rustc` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) paired with `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`). Pipeline dumps were captured directly from `rustc 1.99.1` using `RUSTC_BOOTSTRAP=1 -Z autodiff=PrintPasses` (which invokes `ModulePassManager::printPipeline` at `PassWrapper.cpp:1013-1023`), `-Z print-llvm-passes` (which passes `-debug-pass=Structure` to the legacy `TargetMachine::addPassesToEmitFile` pipeline), and `opt` / `llc` built from the exact `23.1.1` commit. Any drop-in verified replacement for `rustc`, translation validator, or certifying LLVM backend must account for the exact sequence of IR and `MachineFunction` passes documented here across `-O0`..`-Oz`, LTO modes (`no`, `thinlocal`, `thin`, `fat`), PGO (`-C profile-generate`, `-C profile-use`), sanitizers, and target architectures.

## Findings

### 1. Global LLVM Command-Line Options and Per-Target `llvm_args`

**Basis: source + execution**

During compiler initialization, `rustc_codegen_llvm::llvm_util::configure_llvm` (`compiler/rustc_codegen_llvm/src/llvm_util.rs:46-169`) constructs an `argv` array and calls `LLVMRustSetLLVMOptions` (`PassWrapper.cpp:449-459`), which invokes `llvm::cl::ParseCommandLineOptions` exactly once per process.

1. **Ordering and Override Precedence (`llvm_util.rs:89-108`)**:
   - Target specification `sess.target.llvm_args` are appended **before** user-supplied `-C llvm-args=...` so user flags win under `cl::opt`'s last-wins semantics.
   - Built-in defaults added via `add(arg, /*force=*/false)` check `user_specified_args` by flag name prefix (splitting on `=` or whitespace) so `-C llvm-args` can override any built-in default.

2. **Built-in Global Flags (`llvm_util.rs:111-160`)**:

| Condition in `configure_llvm` | LLVM `cl::opt` Flag Passed | Purpose and Semantic Effect |
| :--- | :--- | :--- |
| Unconditional (`line 136`) | `-preserve-alignment-assumptions-during-inlining=false` | Prevents `InlineFunction` (`llvm/lib/Transforms/Utils/InlineFunction.cpp`) from synthesizing `@llvm.assume() ["align"(ptr, N)]` operand bundles when inlining parameters with `align N` attributes, because extra `@llvm.assume` calls block downstream scalar/loop optimizations. |
| Unconditional (`line 139`) | `-import-cold-multiplier=0.1` | Overrides LLVM's default `0.0` multiplier in `FunctionImport.cpp` so ThinLTO still imports small functions at cold call sites (with instruction threshold scaled by $0.1\times$). |
| `sess.target.generate_arange_section && !no_generate_arange_section` (`line 117`) | `-generate-arange-section` | Instructs `DwarfDebug` to emit `.debug_aranges` address range tables when DWARF debuginfo is enabled. |
| `merge_functions == MergeFunctions::Aliases` (`line 125`, default on most targets) | `-mergefunc-use-aliases` | Instructs `MergeFunctionsPass` (`llvm/lib/Transforms/IPO/MergeFunctions.cpp`) to emit `GlobalAlias` thunks instead of wrapper call thunks when merging identical unnamed_addr functions. |
| `wants_wasm_eh(sess)` (`line 130`) | `-wasm-enable-eh` | Enables WebAssembly exception-handling instructions in the Wasm backend. |
| `-Z time-llvm-passes` (`line 111`) | `-time-passes` | Enables LLVM pass timing reports. |
| `-Z print-llvm-passes` (`line 114`) | `-debug-pass=Structure` | Prints the legacy `PassManager` structure during `LLVMRustWriteOutputFile` codegen. |
| `small_data_threshold` set (`line 156`) | `--<arg>=<threshold>` | Sets target small-data section threshold where supported via LLVM flag. |

3. **Per-Target `llvm_args` Across All Target Specs (`compiler/rustc_target/src/spec/`)**:
   A complete scan of `compiler/rustc_target/src/spec/**/*.rs` (preserved in `support/target_spec_llvm_args.json`) shows that only **three** distinct target families set non-empty `llvm_args`:
   - `compiler/rustc_target/src/spec/base/wasm.rs`: `["-wasm-use-legacy-eh=false"]` (applies to `wasm32`/`wasm64` targets other than `wasm32_unknown_emscripten`, which overrides `llvm_args` to `[]`).
   - All 21 `mips*` / `mips64*` target specs (`mips_unknown_linux_gnu.rs`, `mips64_unknown_linux_gnuabi64.rs`, etc.): `["-mno-check-zero-division"]` (disables hardware/trap zero-division emission inside the MIPS backend because Rust checks integer division by zero in MIR before lowering).
   - `compiler/rustc_target/src/spec/targets/x86_64_fortanix_unknown_sgx.rs`: `["--x86-experimental-lvi-inline-asm-hardening"]` (enables Load Value Injection mitigation on inline assembly for Intel SGX enclaves).

---

### 2. TargetMachine Configuration (`target_machine_factory` and `LLVMRustCreateTargetMachine`)

**Basis: source**

`target_machine_factory` (`write.rs:195-307`) and `LLVMRustCreateTargetMachine` (`PassWrapper.cpp:342-429`) translate `rustc` session and target options into `llvm::TargetOptions` and `llvm::TargetMachine`:

- **CodeGen Optimization Level Mapping (`write.rs:139-149`)**:
  - `-C opt-level=0` (`No`) $\rightarrow$ `CodeGenOptLevel::None`
  - `-C opt-level=1` (`Less`) $\rightarrow$ `CodeGenOptLevel::Less`
  - `-C opt-level=2` (`More`), `-C opt-level=s` (`Size`), and `-C opt-level=z` (`SizeMin`) $\rightarrow$ `CodeGenOptLevel::Default`
  - `-C opt-level=3` (`Aggressive`) $\rightarrow$ `CodeGenOptLevel::Aggressive`
- **Section Layout**: `Options.FunctionSections` and `Options.DataSections` default to `sess.target.function_sections` (`true` on Linux/Windows/macOS targets), and `Options.UniqueSectionNames` defaults to `true` (`!sess.opts.unstable_opts.no_unique_section_names`).
- **`TrapUnreachable` and `NoTrapAfterNoreturn` (`PassWrapper.cpp:390-410`)**:
  - `sess.target.trap_unreachable` defaults to `true` on almost all targets (`compiler/rustc_target/src/spec/mod.rs`).
  - When `TrapUnreachable` is `true`, `PassWrapper.cpp:395` sets `Options.TrapUnreachable = true` so `llvm.unreachable` lowers to an architectural trap (`ud2` on x86, `brk #0x1` on AArch64) instead of falling through into adjacent bytes.
  - Furthermore, if `!Trip.isWasm() && !Trip.isOSWindows()`, `PassWrapper.cpp:407-409` sets `Options.NoTrapAfterNoreturn = true` to suppress redundant trap instructions immediately following `noreturn` calls. Windows is explicitly excluded (`rust-lang/rust#140489`) because omitting a trailing instruction after a `noreturn` call at the end of a function allows the return address (`RIP`) to point to the first byte of the *next* function, causing `RtlLookupFunctionEntry` to resolve the wrong `.pdata` unwind entry during SEH stack walking.

---

### 3. `llvm_optimize` Options and New Pass Manager (`PassBuilder`) Pipeline Architecture

**Basis: source + execution**

`llvm_optimize` (`write.rs:541-894`) invokes `LLVMRustOptimize` (`PassWrapper.cpp:627-1031`), which configures `PipelineTuningOptions` (`PTO`) and `PassBuilder`:

| `PipelineTuningOptions` Field | Value Set by `rustc` (`write.rs:587-598`, `PassWrapper.cpp:650-655`) | LLVM Default (`PassBuilderPipelines.cpp:339-355`) |
| :--- | :--- | :--- |
| `PTO.LoopUnrolling` | `opt_level != Size && opt_level != SizeMin` (`true` for `O0..O3`, `false` for `Os`/`Oz`) | `true` |
| `PTO.LoopInterleaving` | Same as `UnrollLoops` (`true` for `O0..O3`, `false` for `Os`/`Oz`) | `true` |
| `PTO.LoopVectorization` | `config.vectorize_loop` (`true` at `O2`/`O3`/`Os`/`Oz` unless `-C no-vectorize-loops` or `Oz` disables it) | `true` |
| `PTO.SLPVectorization` | `config.vectorize_slp` (`true` at `O2`/`O3`/`Os`/`Oz` unless `-C no-vectorize-slp`) | `false` (note: `PassBuilder` default is `false`, `rustc` explicitly enables it!) |
| `PTO.MergeFunctions` | `config.merge_functions` (`true` at `O2`/`O3`/`Os`/`Oz` on targets with `MergeFunctions::Aliases` or `Trampolines`) | `false` (`EnableMergeFunctions`) |
| `PTO.LoopInterchange` | `true` (inherited from `EnableLoopInterchange` default in LLVM 23.1.1) | `true` |

#### 3.1 How `rustc` Selects `PassBuilder` Pipelines by `OptStage` and Bitcode Embedding

In `write.rs:920-943` and `PassWrapper.cpp:897-983`, the NewPM pipeline depends on **both** `OptStage` and whether `ThinLTOBufferRef` is non-null (`emit_obj == EmitObj::ObjectCode(BitcodeSection::Full) || config.emit_thin_lto_summary`):

1. **`OptLevel == O0 && !IsLTO` (`PassWrapper.cpp:897-900`, `support/newpm_O0_no_lto_embed_bc.txt`)**:
   Runs `PB.buildO0DefaultPipeline(O0)` followed by the suffix passes and (if embedding bitcode) `ThinLTOBitcodeWriterPass` (or `forceFullLTOSummary` + `BitcodeWriterPass` for `PreLinkFatLTO`):
   ```text
   function(ee-instrument<>),always-inline,
   coro-cond(coro-early,cgscc(coro-split),coro-cleanup,globaldce),
   alloc-token,lower-ifunc,function(annotation-remarks),
   canonicalize-aliases,name-anon-globals,assign-guid,ThinLTOBitcodeWriterPass
   ```

2. **`OptStage == PreLinkNoLTO` WITH Bitcode Embedding (`ThinLTOBufferRef != nullptr`, default for `rlib` at `O1`/`O2`/`O3`/`Os`/`Oz`, `PassWrapper.cpp:904-920`, `support/newpm_O2_no_lto_embed_bc.txt`)**:
   Instead of `buildPerModuleDefaultPipeline`, `rustc` splits optimization into two halves separated by `ThinLTOBitcodeWriterPass`:
   - **Half 1**: `PB.buildThinLTOPreLinkDefaultPipeline(OptLevel)` (`3,313` chars at `-O2`)
   - **Midpoint snapshot**: `ThinLTOBitcodeWriterPass(ThinLTODataOS, &ThinLinkDataOS)` — serializes the module after early simplification and CGSCC inlining/SROA/EarlyCSE/GVN/LICM/DSE, *before* loop vectorization, SLP vectorization, loop unrolling, and `MergeFunctions`!
   - **Half 2**: `PB.buildModuleOptimizationPipeline(OptLevel, ThinOrFullLTOPhase::None)` (`1,490` chars at `-O2`)
   - **Suffix**: `function(annotation-remarks),canonicalize-aliases,name-anon-globals,assign-guid`

3. **`OptStage == PreLinkNoLTO` WITHOUT Bitcode Embedding (`-C embed-bitcode=no` or single-CGU `ThinLocal`, `PassWrapper.cpp:921`, `support/newpm_O2_no_lto_no_bc.txt`)**:
   Runs `PB.buildPerModuleDefaultPipeline(OptLevel)` followed by `canonicalize-aliases,name-anon-globals,assign-guid`. Unlike the split `ThinLTOPreLink + ModuleOptimization` pipeline above, `buildPerModuleDefaultPipeline` starts with `memprof-remove-attributes`, passes `ThinOrFullLTOPhase::None` to `LoopRotatePass` inside the CGSCC loop pipeline (`loop-rotate<header-duplication;no-prepare-for-lto>` instead of `prepare-for-lto`), and does not insert `lower-comment-string` before the module optimization phase.

4. **`OptStage == PreLinkThinLTO` and `PreLinkFatLTO` (`PassWrapper.cpp:924-928, 966-983`)**:
   Both run `PB.buildThinLTOPreLinkDefaultPipeline(OptLevel)` (`support/newpm_O2_linker_plugin_lto.txt`), followed by `canonicalize-aliases,name-anon-globals,assign-guid` (which `buildThinLTOPreLinkDefaultPipeline` itself appends at `PassBuilderPipelines.cpp:1927-1929`), and then either `ThinLTOBitcodeWriterPass` (`PreLinkThinLTO`) or `forceFullLTOSummary` + `BitcodeWriterPass` (`PreLinkFatLTO`).

5. **`OptStage == ThinLTO` (Post-Link ThinLTO and Multi-CGU `ThinLocal`, `PassWrapper.cpp:929-933`, `support/newpm_O2_lto_thin.txt`)**:
   After `rustc_codegen_llvm::back::lto::run_pass_manager` (`lto.rs:515-580`) internalizes non-exported symbols and runs `FunctionImport` across the ThinLTO index, `LLVMRustOptimize` runs `PB.buildThinLTODefaultPipeline(OptLevel, nullptr)` followed by `canonicalize-aliases,name-anon-globals,assign-guid`.
   - At `-O0` (`support/newpm_O0_lto_thin.txt`), `buildThinLTODefaultPipeline(O0)` runs:
     ```text
     memprof-remove-attributes,drop-type-tests<assume>,
     coro-cond(coro-early,cgscc(coro-split),coro-cleanup,globaldce),
     alloc-token,elim-avail-extern,globaldce,
     canonicalize-aliases,name-anon-globals,assign-guid
     ```

6. **`OptStage == FatLTO` (Post-Link Fat LTO, `PassWrapper.cpp:934-937`, `support/newpm_O2_lto_fat.txt`)**:
   After linking all crate bitcode modules into a single `llvm::Module` and running `LLVMRustRunRestrictionPass` (`internalizeModule`, `PassWrapper.cpp:1144-1157`), `LLVMRustOptimize` runs `PB.buildLTODefaultPipeline(OptLevel, nullptr)` (`2,285` chars at `-O2`, `2,300` chars at `-O3`, `201` chars at `-O0`).

---

### 4. Complete Ordered NewPM Pass Inventory Across `-O1`, `-O2`, `-O3`, `-Os`, `-Oz`, LTO, PGO, and Sanitizers

**Basis: source + execution**

The table below decomposes `buildPerModuleDefaultPipeline` (`PassBuilderPipelines.cpp:1505-1536`), `buildModuleSimplificationPipeline` (`lines 1043-1269`), `buildInlinerPipeline` (`lines 919-1039`), `buildFunctionSimplificationPipeline` (`lines 629-862`), and `buildModuleOptimizationPipeline` (`lines 1272-1502`), showing the exact pass sequence and where `-O1`, `-O2`, `-O3`, `-Os`, `-Oz`, LTO, PGO, and Sanitizers diverge:

| Phase | Ordered Pass Sequence in NewPM (`rustc` 1.99.1 / LLVM 23.1.1) | Differences by OptLevel (`O1`/`O2`/`O3`/`Os`/`Oz`), LTO, PGO, and Sanitizers |
| :--- | :--- | :--- |
| **1. Pipeline Start & Early Module** | `memprof-remove-attributes` (omitted in `ThinLTOPreLink`), `annotation2metadata`, `forceattrs`, *[EP: PipelineStart: `lowertypetests` if CFI, `verify` if `-Zverify-llvm-ir`, `function(lint)` if `-Zlint-llvm-ir`, `instrprof` if `-Cinstrument-coverage`]*, `inferattrs`, `coro-early` | Identical across `O1`..`Oz`. |
| **2. Early Function Simplification** | `function<eager-inv>(ee-instrument<>, lower-expect, simplifycfg<bonus-inst-threshold=1;...;no-speculate-unpredictables>, sroa<modify-cfg>, early-cse<>, callsite-splitting)` (`callsite-splitting` only at `O2`/`O3`/`Os`/`Oz`; omitted at `O1` and under PGO) | At **`O3`** only, `callsite-splitting` runs here; at **`O1`** it is omitted; under **`PGO Gen/Use`**, `callsite-splitting` is deferred until after PGO instrumentation/annotation. |
| **3. PGO Pre-Inliner & Instrumentation / Profile Annotation** | *(Only when `-Cprofile-generate` or `-Cprofile-use` is active)*: `PGO Pre-Inliner CGSCC (inline<only-mandatory>, inline<threshold=75>, FunctionSimplification)` $\rightarrow$ `pgo-instr-gen` (or `pgo-instr-use`) $\rightarrow$ `function(sroa<modify-cfg>, early-cse<>, simplifycfg, instcombine, libcalls-shrinkwrap, simplifycfg, pgo-icall-prom)` | Added only when `PGOOpt` is `IRInstr` (`support/newpm_O2_pgo_generate.txt`, `+568` chars) or `IRUse` (`support/newpm_O2_pgo_use.txt`, `+524` chars). |
| **4. Early Global IPO** | `openmp-opt`, `ipsccp`, `called-value-propagation`, `globalopt`, `function<eager-inv>(mem2reg, instcombine<max-iterations=1;no-verify-fixpoint>, simplifycfg<...>)` | In **`ThinLTOPostLink`**, `pgo-icall-prom` and `drop-type-tests<assume>` precede `ipsccp`. |
| **5. CGSCC Inliner & Function Simplification Pipeline** | `always-inline`, `function<eager-inv>(alloc-token<hot-cold-new>)`, `require<globals-aa>`, `function(invalidate<aa>)`, `require<profile-summary>`, `cgscc(devirt<4>(...))` containing: `inline` (`only-mandatory` then full `inline`), `function-attrs<skip-non-recursive-function-attrs>`, `argpromotion` (**`O3` only!**), `openmp-opt-cgscc`, **`FunctionSimplificationPipeline`** (see below), `function-attrs`, `coro-split`, `coro-annotation-elide`, `function(should-not-run-function-passes)` | **`O3` vs `O2`**: `O3` adds `argpromotion` inside CGSCC and sets `simplifycfg<speculate-unpredictables>` (vs `no-speculate-unpredictables` at `O1`/`O2`/`Os`/`Oz`). **`O1` vs `O2`**: `O1` omits `argpromotion`. |
| **5a. `FunctionSimplificationPipeline` (inside CGSCC)** | `sroa<modify-cfg>`, `early-cse<memssa>`, `speculative-execution<only-if-divergent-target>` (**`O2`/`O3`/`Os`/`Oz` only**), `jump-threading`, `correlated-propagation`, `simplifycfg`, `instcombine`, `aggressive-instcombine` (**`O3` only** in LLVM 23!), `libcalls-shrinkwrap`, `tailcallelim`, `simplifycfg`, `reassociate`, `constraint-elimination`, **`LoopPipeline1 (MemorySSA)`**: `loop-mssa(loop-instsimplify, loop-simplifycfg, licm<no-allow-speculation>, loop-rotate<header-duplication>, licm<allow-speculation>, simple-loop-unswitch<nontrivial;trivial> [nontrivial disabled at O1/Os/Oz])`, `simplifycfg`, `instcombine`, **`LoopPipeline2`**: `loop(loop-idiom, indvars, simple-loop-unswitch<nontrivial> [when ExtraSimpleLoopUnswitch], loop-interchange, loop-deletion, loop-unroll-full [only-when-forced at Os/Oz])`, `sroa<modify-cfg>`, `vector-combine` (**`O2`/`O3`/`Os`/`Oz`**), `mldst-motion<no-split-footer-bb>` (**`O2`/`O3`**, omitted at `O1`), `gvn<>` (**`O2`/`O3`/`Os`/`Oz`**; **`O1` omits `gvn`!**), `sccp`, `bdce`, `instcombine`, `jump-threading`, `correlated-propagation`, `adce`, `memcpyopt`, `dse`, `move-auto-init`, `loop-mssa(licm<allow-speculation>)`, `coro-elide`, `simplifycfg<hoist-common-insts;sink-common-insts>`, `instcombine` | **`O1` vs `O2`**: `O1` runs `buildO1FunctionSimplificationPipeline` (`PassBuilderPipelines.cpp:492-624`), which **omits** `speculative-execution`, `jump-threading`, `correlated-propagation`, `constraint-elimination`, `vector-combine`, `mldst-motion`, `gvn`, and `move-auto-init`, and sets `simple-loop-unswitch<no-nontrivial;trivial>`. **`Os`/`Oz` vs `O2`**: `Os`/`Oz` sets `loop-unroll-full<O2;only-when-forced>` (because `PTO.LoopUnrolling = false`). |
| **6. Post-CGSCC Module Cleanup** | `deadargelim`, `coro-cleanup`, `globalopt`, `globaldce`, `elim-avail-extern` (in `PerModule` and `ThinLTOPostLink`), `rpo-function-attrs`, `recompute-globals-aa` | In **`ThinLTOPreLink`**, `elim-avail-extern`, `rpo-function-attrs`, and `recompute-globals-aa` are omitted; instead `ThinLTOPreLink` ends here with `lower-comment-string, canonicalize-aliases, name-anon-globals, assign-guid`. |
| **7. Module Optimization & Vectorization Pipeline (`buildModuleOptimizationPipeline`)** | `function<eager-inv>(float2int, lower-constant-intrinsics, chr [if PGO/profile], loop(loop-rotate<no-header-duplication>, loop-deletion), loop-distribute, inject-tli-mappings, loop-vectorize<no-interleave-forced-only;no-vectorize-forced-only> [interleave-forced-only at Os/Oz], drop-unnecessary-assumes, infer-alignment, loop-load-elim, instcombine, simplifycfg<forward-switch-cond;switch-range-to-icmp;switch-to-arithmetic;switch-to-lookup>, slp-vectorizer, vector-combine, instcombine, loop-unroll<O1/O2/O3;only-when-forced at Os/Oz>, transform-warning, sroa<preserve-cfg>, infer-alignment, instcombine, loop-mssa(licm<allow-speculation>), alignment-from-assumptions, loop-sink, instsimplify, div-rem-pairs, tailcallelim, simplifycfg)` | **`Os`/`Oz`**: `loop-vectorize<interleave-forced-only;no-vectorize-forced-only>` and `loop-unroll<O2;only-when-forced>`. **`O1`**: `loop-vectorize<interleave-forced-only;vectorize-forced-only>` and omits `slp-vectorizer`. |
| **8. Late Module IPO & Sanitizers** | `globaldce`, `constmerge`, `cg-profile`, `rel-lookup-table-converter`, `function(annotation-remarks)`, *[EP: OptimizerLast: `asan`/`msan`/`tsan`/`dfsan`/`hwasan`/`rtsan`]*, `mergefunc` (when `PTO.MergeFunctions == true`), `canonicalize-aliases`, `name-anon-globals`, `assign-guid` | Sanitizers run at `OptimizerLastEPCallback` (`PassWrapper.cpp:793-870`), immediately before `mergefunc`. |
| **9. Full/Fat LTO Post-Link Pipeline (`buildLTODefaultPipeline`)** | `memprof-remove-attributes, cross-dso-cfi, openmp-opt, globaldce<vfe-linkage-unit-visibility>, inferattrs, function(callsite-splitting), ipsccp, called-value-propagation, globalopt, globaldce, elim-avail-extern, rpo-function-attrs, recompute-globals-aa, cgscc(inline, function-attrs, openmp-opt-cgscc), wholeprogramdevirt, globalopt, function(instcombine, aggressive-instcombine [O3], jump-threading, sroa, tailcallelim), rpo-function-attrs, globalopt, function(loop(loop-rotate, loop-deletion), loop-distribute, inject-tli-mappings, loop-vectorize, drop-unnecessary-assumes, loop-load-elim, instcombine, simplifycfg, slp-vectorizer, vector-combine, instcombine, loop-unroll, transform-warning, instcombine, loop-mssa(licm), alignment-from-assumptions, instsimplify, div-rem-pairs, simplifycfg), sccp, instcombine, bdce, dse, loop-mssa(licm), adce, simplifycfg, instcombine, lowertypetests, lowertypetests, elim-avail-extern, globaldce, constmerge, rel-lookup-table-converter, cg-profile, coro-cleanup, alloc-token, function(annotation-remarks)` | Runs only in `LLVMRustOptStage::FatLTO` (`support/newpm_O2_lto_fat.txt`, `support/newpm_O3_lto_fat.txt`). |

---

### 5. Code-Generation Pipeline (`LLVMRustWriteOutputFile` / `TargetPassConfig`) Across Targets

**Basis: source + execution**

After `LLVMRustOptimize` completes on a codegen unit, `write_output_file` (`write.rs:53-101`) creates a legacy `llvm::legacy::PassManager`, attaches `TargetTransformInfo` (`LLVMAddAnalysisPasses`), `TargetLibraryInfoWrapperPass`, and `RuntimeLibraryInfoWrapper` (`LLVMRustAddLibraryInfo`, `PassWrapper.cpp:433-447`), and calls `TargetMachine::addPassesToEmitFile` (`PassWrapper.cpp:505-510`).

The table below compares the exact codegen pipelines dumped via `-Z print-llvm-passes` (`support/codegen_*_O*.txt`) across `x86_64-unknown-linux-gnu` (`i686` is identical), `x86_64-pc-windows-msvc`, `aarch64-unknown-linux-gnu`, and `aarch64-apple-darwin`:

| CodeGen Stage | `x86_64` / `i686` (`-O0`) | `x86_64` / `i686` (`-O2` / `-O3`) | `aarch64` (`-O0`) | `aarch64` (`-O2` / `-O3`) |
| :--- | :--- | :--- | :--- | :--- |
| **1. Pre-ISel IR Lowering** | `pre-isel-intrinsic-lowering`, `expand-ir-insts<O0>`, `atomic-expand`, `x86-lower-amx-intrinsics`, `x86-lower-amx-type`, `gc-lowering`, `shadow-stack-gc-lowering`, `unreachableblockelim`, `post-inline-ee-instrument`, `scalarize-masked-mem-intrin`, `expand-reductions`, `indirectbr-expand`, `dwarf-eh-prepare` (`winehprepare` on MSVC), `inline-asm-prepare`, `safe-stack`, `stack-protector` | Adds `objc-arc-contract`, `loop-simplify`, `canon-freeze`, `loop-reduce` (`LoopStrengthReduce`), `consthoist`, `replace-with-veclib`, `partially-inline-libcalls`, `interleaved-access`, `x86-partial-reduction`, `codegenprepare` | `pre-isel-intrinsic-lowering`, `expand-ir-insts<O0>`, `atomic-expand`, `gc-lowering`, `shadow-stack-gc-lowering`, `unreachableblockelim`, `post-inline-ee-instrument`, `scalarize-masked-mem-intrin`, `expand-reductions`, `aarch64-stack-tagging`, `dwarf-eh-prepare`, `inline-asm-prepare`, `safe-stack`, `stack-protector` | Adds `objc-arc-contract`, `aarch64-sve-intrinsic-opts`, `simplifycfg`, `loop-data-prefetch`, `aarch64-falkor-hwpf-fix`, `canon-freeze`, `loop-reduce`, `consthoist`, `replace-with-veclib`, `partially-inline-libcalls`, `stack-safety`, `interleaved-load-combine`, `interleaved-access`, `type-promotion`, `codegenprepare`, `aarch64-promote-const`, `global-merge` (plus `SeparateConstOffsetFromGEP` + `SLSR` + `EarlyCSE` at **`-O3` only!**) |
| **2. Instruction Selection** | `x86-isel` (`FastISel` + `SelectionDAGISel` fallback), `x86-argument-stack-slot`, `finalize-isel` | `x86-isel` (`SelectionDAGISel`), `x86-argument-stack-slot`, `finalize-isel`, `x86-domain-reassignment` | **GlobalISel**: `irtranslator`, `aarch64-O0-prelegalizer-combiner`, `localizer`, `legalizer`, `aarch64-postlegalizer-lowering`, `regbankselect`, `instruction-select`, `aarch64-isel` (fallback), `finalize-isel` | **GlobalISel (O0 fallback pipeline registered) + `aarch64-isel` (`SelectionDAGISel`)**, `aarch64-local-dynamic-tls-cleanup`, `finalize-isel` |
| **3. Pre-RA Machine Optimizations** | *(Skipped at `-O0`)* | `early-tailduplication`, `opt-phis`, `stack-coloring`, `localstackalloc`, `dead-mi-elimination`, `early-ifcvt`, `machine-combiner`, `x86-cmov-conversion`, `early-machinelicm`, `machine-cse`, `machine-sink`, `peephole-opt`, `dead-mi-elimination`, `lrshrink`, `x86-fixup-setcc`, `x86-optimize-leas`, `x86-cf-opt`, `x86-avoid-sfb`, `x86-suppress-apx-for-relocation`, `x86-slh`, `x86-flags-copy-lowering`, `x86-dyn-alloca-expander` | `localstackalloc`, `aarch64-machine-sme-abi` | `aarch64-machine-sme-abi`, `aarch64-sme-peephole-opt`, `early-tailduplication`, `opt-phis`, `stack-coloring`, `localstackalloc`, `dead-mi-elimination`, `aarch64-condopt`, `aarch64-ccmp`, `machine-combiner`, `aarch64-cond-br-tuning`, `early-ifcvt`, `aarch64-stp-suppress`, `aarch64-simd-instr-opt`, `aarch64-stack-tagging-pre-ra`, `early-machinelicm`, `machine-cse`, `machine-sink`, `peephole-opt`, `dead-mi-elimination`, `aarch64-mi-peephole-opt`, `aarch64-dead-defs`, `aarch64-sls-hardening` |
| **4. SSA Deconstruction & Register Allocation** | `phi-node-elimination`, `twoaddressinstruction`, `regallocfast`, `x86-lower-tile-copy`, `x86-fp-stackifier`, `x86-lvi-load`, `removeredundantdebugvalues`, `fixup-statepoint-caller-saved` | `tilepreconfig`, `detect-dead-lanes`, `init-undef`, `processimpdefs`, `unreachable-mbb-elimination`, `livevars`, `phi-node-elimination`, `twoaddressinstruction`, `slotindexes`, `liveintervals`, `register-coalescer`, `rename-independent-subregs`, `machine-scheduler`, `virtregmap`, `liveregmatrix`, `spill-code-placement`, **`greedy` (`RAGreedy`)**, `x86-tile-config`, **`greedy`**, `virtregrewriter`, `stack-slot-coloring`, `machine-cp`, `machinelicm`, `x86-lower-tile-copy`, `x86-fp-stackifier`, `x86-lvi-load` | `phi-node-elimination`, `twoaddressinstruction`, `regallocfast`, `removeredundantdebugvalues`, `fixup-statepoint-caller-saved` | `detect-dead-lanes`, `init-undef`, `processimpdefs`, `unreachable-mbb-elimination`, `livevars`, `phi-node-elimination`, `twoaddressinstruction`, `slotindexes`, `liveintervals`, `register-coalescer`, `rename-independent-subregs`, `machine-scheduler`, `aarch64-post-coalescer-peephole`, `virtregmap`, `liveregmatrix`, `spill-code-placement`, **`greedy` (`RAGreedy` — two runs: CSR/general + FPR/vector)**, `virtregrewriter`, `stack-slot-coloring`, `machine-cp`, `machinelicm`, `aarch64-ldst-opt` (pre-PEI), `removeredundantdebugvalues`, `fixup-statepoint-caller-saved` |
| **5. Frame Lowering & Post-RA Optimizations** | `prolog-epilog`, `postrapseudos`, `x86-expand-pseudo`, `kcfi`, `fentry-insert`, `xray-instrumentation`, `patchable-function`, `funclet-layout`, `remove-loads-into-fake-uses`, `stackmap-liveness`, `livedebugvalues`, `machine-sanmd`, `stack-frame-layout`, `x86-seses`, `x86-return-thunks`, `cfi-instr-inserter`, `x86-lvi-ret`, `pseudo-probe-inserter`, `unpack-mi-bundles`, `x86-asm-printer` | `postra-machine-sink`, `shrink-wrap`, `prolog-epilog`, `machine-latecleanup`, `branch-folder`, `tailduplication`, `machine-cp`, `postrapseudos`, `x86-expand-pseudo`, `kcfi`, `post-RA-sched`, `block-placement`, `fentry-insert`, `xray-instrumentation`, `patchable-function`, `x86-execution-domain-fix`, `break-false-deps`, `x86-fixup-bw-insts`, `x86-fixup-leas`, `x86-fixup-inst-tuning`, `x86-fixup-vector-constants`, `x86-compress-evex`, `funclet-layout`, `remove-loads-into-fake-uses`, `stackmap-liveness`, `livedebugvalues`, `machine-sanmd`, `stack-frame-layout`, `x86-seses`, `x86-return-thunks`, `cfi-instr-inserter`, `x86-lvi-ret`, `pseudo-probe-inserter`, `unpack-mi-bundles`, `x86-asm-printer` | `prolog-epilog`, `postrapseudos`, `aarch64-expand-pseudo`, `kcfi`, `aarch64-speculation-hardening`, `fentry-insert`, `xray-instrumentation`, `patchable-function`, `aarch64-fix-cortex-a53-835769-pass`, `funclet-layout`, `remove-loads-into-fake-uses`, `stackmap-liveness`, `livedebugvalues`, `machine-sanmd`, `aarch64-sls-hardening`, `aarch64-ptrauth`, `aarch64-branch-targets`, `branch-relaxation`, `cfi-fixup`, `stack-frame-layout`, `pseudo-probe-inserter`, `unpack-mi-bundles`, `aarch64-asm-printer` | `postra-machine-sink`, `shrink-wrap`, `prolog-epilog`, `machine-latecleanup`, `branch-folder`, `tailduplication`, `machine-cp`, `postrapseudos`, `aarch64-expand-pseudo`, `kcfi`, `aarch64-ldst-opt` (post-PEI), `aarch64-A57-fp-load-balancing`, `aarch64-speculation-hardening`, `postmisched`, `block-placement`, `fentry-insert`, `xray-instrumentation`, `patchable-function`, `aarch64-copyelim`, `aarch64-fix-cortex-a53-835769-pass`, `funclet-layout`, `remove-loads-into-fake-uses`, `stackmap-liveness`, `livedebugvalues`, `machine-sanmd`, `aarch64-sls-hardening`, `aarch64-ptrauth`, `aarch64-branch-targets`, `branch-relaxation`, `cfi-fixup`, `stack-frame-layout`, `pseudo-probe-inserter`, `unpack-mi-bundles`, `aarch64-asm-printer` |

---

### 6. Linked LLVM Components and Source/Binary Footprint

**Basis: source + execution**

`compiler/rustc_llvm/build.rs:11-35` specifies `REQUIRED_COMPONENTS` (`["ipo", "bitreader", "bitwriter", "linker", "asmparser", "lto", "coverage", "instrumentation"]`) and `OPTIONAL_COMPONENTS` (the 19 target architectures). Through `llvm-config --libs`, these top-level components transitively link the core LLVM libraries listed below (`support/llvm_component_loc.json`):

| `llvm/lib/` Subdirectory | Files | `.cpp` Files | Total LOC (`.cpp` + `.h` + `.td` + `.inc`) | Role in `rustc` Compilation Pipeline |
| :--- | ---: | ---: | ---: | :--- |
| `Target` (all 19 targets) | 826 | 380 | 894,388 | Target machine descriptions, TableGen `.td` files, ISel, target MachineFunction passes (`AArch64`: `272,844` LOC; `X86`: `263,488` LOC; `ARM`: `174,068` LOC; `RISCV`: `146,397` LOC; `WebAssembly`: `36,205` LOC). |
| `Transforms` | 357 | 332 | 445,509 | All middle-end IR passes (`InstCombine`: `56,238` LOC, `Scalar`, `IPO`, `Vectorize`, `Utils`, `Coroutines`, `Instrumentation`, `AggressiveInstCombine`). |
| `CodeGen` | 367 | 323 | 388,377 | Target-independent code generation (`SelectionDAG`, `GlobalISel`, `RAGreedy`, `RegisterCoalescer`, `MachineScheduler`, `PrologEpilogInserter`, `AsmPrinter`). |
| `Analysis` | 125 | 125 | 110,582 | IR analyses (`ScalarEvolution`, `BasicAliasAnalysis`, `MemorySSA`, `ValueTracking`, `LazyValueInfo`, `InlineCost`, `LoopAccessAnalysis`). |
| `Support` | 201 | 170 | 96,384 | Data structures, `cl::opt`, streams, VFS, compression, threading, error handling. |
| `IR` | 89 | 83 | 81,734 | Core LLVM IR AST (`Module`, `Function`, `BasicBlock`, `Instruction`, `Constant`, `Verifier`, `AutoUpgrade`, `PassManager`). |
| `DebugInfo` | 234 | 234 | 65,207 | DWARF, CodeView, PDB, BTF, and MSF debuginfo readers/writers. |
| `MC` | 93 | 92 | 53,388 | Machine Code layer (`MCStreamer`, `MCInst`, `MCAssembler`, ELF/COFF/Mach-O/Wasm object writers, `MCParser`). |
| `Object` | 38 | 37 | 26,984 | Object file and archive containers. |
| `Bitcode` | 12 | 9 | 20,949 | Bitstream reader/writer and bitcode serialization (`BitcodeWriterPass`, `ThinLTOBitcodeWriter`). |
| `ProfileData` | 25 | 25 | 17,451 | Instrumentation and sample PGO profile readers/writers and coverage mapping (`InstrProf`, `CoverageMapping`). |
| `AsmParser` | 4 | 4 | 13,236 | textual `.ll` LLVM IR parser (`LLLexer`, `LLParser`). |
| `TargetParser` | 19 | 17 | 11,665 | Target triple normalization and host/CPU feature tables. |
| `Passes` | 5 | 5 | 8,355 | `PassBuilder`, `PassBuilderPipelines.cpp` (`2,574` LOC), `StandardInstrumentations`. |
| `LTO` | 6 | 6 | 6,090 | ThinLTO and FullLTO orchestration (`LTO.cpp`, `ThinLTOCodeGenerator.cpp`). |
| `BinaryFormat` | 14 | 14 | 4,652 | ELF, Mach-O, COFF, Wasm, DWARF constants and headers. |
| `Remarks` | 13 | 11 | 2,523 | YAML/bitstream optimization remark serializers. |
| `Linker` | 3 | 2 | 2,381 | IR module linking (`IRMover`, `LinkModules.cpp`). |
| **Total (excluding `TableGen`)** | **2,415** | **1,869** | **2,249,855** | Complete LLVM 23.1.1 runtime library footprint linked into `rustc`. |

In the released `1.99.1-x86_64-unknown-linux-gnu` toolchain, `libLLVM.so.23.1-rust-1.99.1-stable` is `208,167,760` bytes (`198.52` MiB), containing `69,729,043` bytes of `.bolt.org.text`, `59,601,748` bytes of `.bolt.org.rodata`, and BOLT-reordered `.text`/`.text.cold` sections.

## Boundaries

- **Target-specific codegen pipelines beyond Tier 1**: We executed and preserved full `-Z print-llvm-passes` codegen pass trees for `x86_64` (Linux/Windows), `i686` (Linux/Windows), and `aarch64` (Linux/macOS), and `llc -debug-pass=Structure` dumps for `riscv64gc-unknown-linux-gnu` and `wasm32-unknown-unknown`. `x86_64-apple-darwin` returned an Apple SDK version error in `rustc` when invoked without `SDKROOT` (`versioned_llvm_target` queries Xcode SDK version when `SDKROOT` is set or errors if Apple target version resolution fails), though its LLVM target pass pipeline is governed by the same `X86PassConfig` + Mach-O `AsmPrinter` rules.
- **Enzyme / Autodiff experimental passes**: `write.rs:541-600` and `PassWrapper.cpp:985-1010` include hooks for `-Z autodiff=Enable` (`PreAD`, `DuringAD`, `PostAD`), which runs `llvm_optimize` twice (first with `unroll_loops = vectorize_slp = vectorize_loop = merge_functions = false`, then with Enzyme, then with full optimizations). Because `-Z autodiff` is unstable and disabled in standard builds, only the standard `PostAD` path executes in normal compilations.

## Evidence

- **Primary source files in `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp`: lines 185–209 (`fromRust(LLVMRustPassBuilderOptLevel)` mapping `Os`/`Oz` to `OptimizationLevel::O2` on `LLVM_VERSION_GE(23, 0)`), lines 342–429 (`LLVMRustCreateTargetMachine`, `TrapUnreachable`, `NoTrapAfterNoreturn`), lines 433–459 (`LLVMRustAddLibraryInfo`, `LLVMRustSetLLVMOptions`), lines 478–517 (`LLVMRustWriteOutputFile`), lines 627–1031 (`LLVMRustOptimize`).
  - `compiler/rustc_codegen_llvm/src/back/write.rs`: lines 53–101 (`write_output_file`), lines 139–161 (`to_llvm_opt_settings`, `to_pass_builder_opt_level`), lines 195–307 (`target_machine_factory`), lines 541–894 (`llvm_optimize`), lines 897–983 (`optimize`).
  - `compiler/rustc_codegen_llvm/src/llvm_util.rs`: lines 46–169 (`configure_llvm` global LLVM options).
  - `compiler/rustc_llvm/build.rs`: lines 11–35 (`OPTIONAL_COMPONENTS`, `REQUIRED_COMPONENTS`).
- **Primary source files in `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)**:
  - `llvm/include/llvm/Passes/OptimizationLevel.h`: lines 22–75 (`enum class OptimizationLevel { O0, O1, O2, O3 }`).
  - `llvm/lib/Passes/PassBuilderPipelines.cpp`: lines 339–355 (`PipelineTuningOptions`), lines 492–624 (`buildO1FunctionSimplificationPipeline`), lines 629–862 (`buildFunctionSimplificationPipeline`), lines 919–1039 (`buildInlinerPipeline`), lines 1043–1269 (`buildModuleSimplificationPipeline`), lines 1272–1502 (`buildModuleOptimizationPipeline`), lines 1505–1536 (`buildPerModuleDefaultPipeline`), lines 1872–1932 (`buildThinLTOPreLinkDefaultPipeline`), lines 1934–2010 (`buildThinLTODefaultPipeline`), lines 2012–2215 (`buildLTODefaultPipeline`).
- **Preserved support artifacts (`reports/rustc-llvm-pass-pipelines-and-configuration/support/`)**:
  - `newpm_*.txt`: Exact NewPM pipeline strings emitted by `RUSTC_BOOTSTRAP=1 rustup run 1.99.1 rustc -Zautodiff=PrintPasses` across `O0`, `O1`, `O2`, `O3`, `Os`, `Oz`, `embed-bitcode=no`, `thinlocal`, `lto=thin`, `lto=fat`, `linker-plugin-lto`, `profile-generate`, `profile-use`, `instrument-coverage`, `sanitizer=address`, and `verify-llvm-ir`.
  - `codegen_*_O*.txt`: Full legacy `PassManager` codegen pass trees emitted by `RUSTC_BOOTSTRAP=1 rustup run 1.99.1 rustc -Zprint-llvm-passes` across Tier 1 targets at `-O0`, `-O2`, and `-O3`.
  - `opt_newpm_pipelines.json`, `target_spec_llvm_args.json`, `llvm_component_loc.json`.

## Revalidation

To revalidate the exact NewPM and CodeGen pass pipelines on a newer `rustc` or LLVM version, run:

```bash
RUSTC_BOOTSTRAP=1 rustc --crate-type=rlib -Copt-level=2 -Cpanic=abort -Ccodegen-units=1 \
  -Zautodiff=PrintPasses specimen.rs -o /tmp/out.rlib

RUSTC_BOOTSTRAP=1 rustc --crate-type=rlib -Copt-level=2 -Cpanic=abort -Ccodegen-units=1 \
  -Zprint-llvm-passes specimen.rs -o /tmp/out.rlib
```

Diff the resulting pipeline strings against `support/newpm_O2_no_lto_embed_bc.txt` and `support/codegen_x86_64-unknown-linux-gnu_O2.txt`, and inspect `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp` and `compiler/rustc_codegen_llvm/src/back/write.rs` for any changes to `LLVMRustOptimize` or `LLVMRustCreateTargetMachine`.
