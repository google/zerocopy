# LTO in `rustc` 1.99.1: Modes, Export-List Mechanics, Symbol Preservation Contracts, and Whole-Program Value

## Summary

`rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) implements Link-Time Optimization (LTO) across `compiler/rustc_codegen_ssa/src/back/{lto.rs, symbol_export.rs, write.rs}` and `compiler/rustc_codegen_llvm/src/back/{lto.rs, write.rs}`, coordinating with Rust's MIR cross-crate inliner (`compiler/rustc_mir_transform/src/cross_crate_inline.rs`) and LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):

1. **Four In-Process LTO Modes Plus Two Bitcode-Export Modes**:
   - `Lto::No` (`-C lto=off` or `-C opt-level=0` or `-C codegen-units=1` without `-C lto`): Compiles each codegen unit independently without cross-CGU LLVM summary indexing.
   - `Lto::ThinLocal` (**default** when `-C lto` is omitted, `-C opt-level` $\ge 1$, and `-C codegen-units` $> 1$): Runs LLVM `ThinLTO` across the codegen units of the **local crate only**, without importing bitcode from upstream `.rlib` dependencies (`compiler/rustc_session/src/config.rs:1955-1992`).
   - `Lto::Thin` (`-C lto=thin` or `-C lto=no` when overridden): Extracts pre-link LLVM bitcode (`.rcgu.bc`) from all local CGUs and all upstream `.rlib` archives in the crate graph (`each_linked_rlib_for_lto`), builds a combined `ThinLTOData` summary index (`LLVMRustCreateThinLTOData`), internalizes all symbols not in `symbols_below_threshold`, imports cross-crate/cross-CGU functions (`-import-instr-limit=100`, `-import-cold-multiplier=0.1` set at `llvm_util.rs:139`), and optimizes each `ThinModule` in parallel via `buildThinLTODefaultPipeline`.
   - `Lto::Fat` (`-C lto` / `-C lto=yes` / `-C lto=fat`): Links all local CGU modules and upstream `.rlib` bitcode buffers into a single monolithic `llvm::Module` via `LLVMRustLinkInExternalBitcode`, runs `LLVMRustRunRestrictionPass` (`llvm::internalizeModule` preserving only `symbols_below_threshold`), and executes `buildLTODefaultPipeline` on the single merged module (`compiler/rustc_codegen_llvm/src/back/lto.rs:212-338`).
   - `-C embed-bitcode=yes|no` and `-C linker-plugin-lto`: By default (`embed-bitcode=yes`), `rustc` embeds compressed `.llvmbc` and `.llvmcmd` sections in `.rlib` object files (`PassWrapper.cpp:904-920`) by running `buildThinLTOPreLinkDefaultPipeline`, snapshotting the bitcode mid-pipeline via `ThinLTOBitcodeWriterPass`, and then running `buildModuleOptimizationPipeline` to emit the `.rcgu.o` machine code. When `-C linker-plugin-lto` is active, `rustc` stops after `buildThinLTOPreLinkDefaultPipeline` + `ThinLTOBitcodeWriterPass` and emits **pure LLVM bitcode** as the `.rcgu.o` files (`0` bytes of ELF/COFF/Mach-O `.text`) so `lld` / `LLVMgold.so` can perform cross-language C/C++/Rust ThinLTO at final link time.
2. **Interaction Between MIR Cross-Crate Inlining (`cross_crate_inlinable`) and LLVM LTO**:
   - In `rustc` 1.99.1, `cross_crate_inlinable` (`compiler/rustc_mir_transform/src/cross_crate_inline.rs:18-111`) automatically marks any non-`extern` leaf function (`calls == 0 && resumes == 0 && landing_pads == 0 && statements <= 20` in `optimized_mir`, even **without** `#[inline]`) as cross-crate inlinable, serializing its MIR into `.rmeta` and excluding it from `reachable_non_generics` (`symbol_export.rs:108`).
   - Consequently, small leaf functions are inlined across crates by `rustc`'s MIR inliner (`Inline`) even at `-C lto=off`! LLVM `ThinLTO` and `FatLTO` are specifically required to inline and specialize **non-leaf** cross-crate functions (`calls > 0`), functions exceeding 20 MIR statements, trait-object vtable calls, and functions inside prebuilt `libstd`/`libcore` compiled as separate crates.
3. **Export Lists, Crate-Type Restrictions, and `#[used]` Preservation**:
   - `check_lto_allowed` (`compiler/rustc_codegen_ssa/src/back/lto.rs:138-161`) permits whole-program `Thin`/`Fat` LTO only for `Executable` (`bin`), `StaticLib`, `Cdylib`, and (when `-Z dylib-lto` is passed) `Dylib` and `ProcMacro`. Passing `-C lto=thin` or `-C lto=fat` when `--crate-type=rlib` is present is rejected with `error: lto can only be run for executables, cdylibs and static library outputs`.
   - `crate_export_threshold` (`symbol_export.rs:35-42`) sets `SymbolExportLevel::C` for `Executable`, `StaticLib`, `Cdylib`, and `ProcMacro` (preserving only `#[no_mangle]`/`#[export_name]` C-ABI exports and `main`/proc-macro registrars), and `SymbolExportLevel::Rust` for `Rlib`, `Dylib`, and `Sdylib`.
   - For `#[used]` statics, `rustc` distinguishes `#[used]` / `#[used(compiler)]` (`llvm.compiler.used`, which prevents LLVM's `GlobalDCE` from dropping the symbol during LTO while still allowing the native linker's `--gc-sections` to discard it if unreferenced) from `#[used(linker)]` (`llvm.used`, which also forces the linker to retain the section; `compiler/rustc_codegen_llvm/src/consts.rs:365-430`). In addition, `prepare_lto` (`compiler/rustc_codegen_ssa/src/back/lto.rs:88-136`) explicitly adds all `ExportedSymbol::DropGlue` and `ExportedSymbol::NoDefId` symbols and `#[used]` statics into `symbols_below_threshold` so `internalizeModule` never internalizes them during `ThinLTO` or `FatLTO`.
4. **Empirical Speed, Size, and Compile-Time Matrix Across All 8 Tier 1 Targets**:
   - Across all 8 Tier 1 targets (`support/lto_speed_size_compiletime.csv`), `ThinLTO` and `FatLTO` eliminate **100%** of unreferenced exported functions (`dead_exported_helper_1`, `dead_exported_helper_2`, and unused `std`/`core` symbols) when building a `staticlib` or `bin` (`SymbolExportLevel::C`), shrinking the resulting `staticlib` archive by **65.9% to 72.2%** (`23.36 MB` $\rightarrow$ `7.98 MB` with `ThinLTO` and `7.63 MB` with `FatLTO` on `x86_64-unknown-linux-gnu`; `24.40 MB` $\rightarrow$ `8.41 MB` with `ThinLTO` and `8.05 MB` with `FatLTO` on `aarch64-unknown-linux-gnu`) while preserving `#[used] static KEEP_COMPILER_USED` across all 48 target $\times$ mode combinations.

## Applicability

- **Subjects**: `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).
- **Relation to other corpus packages**: Extends `rustc-llvm-pass-pipelines-and-configuration` (`O1`) and `llvm-interprocedural-lto-and-codegen-optimization-obligations` (`O5`), and shares cross-target harness conventions with `rustc-experimental-corpora-and-harness-conventions` (`P2`).
- **Scope**: Applies to any drop-in `rustc` replacement, certifying compiler backend, or build-system integration handling `-C lto`, `-C codegen-units`, `-C embed-bitcode`, and `-C linker-plugin-lto`.

## Findings

### 1. Crate-Type LTO Eligibility and Symbol Export Threshold Rules

`Basis: source (compiler/rustc_codegen_ssa/src/back/{lto.rs, symbol_export.rs})`

When `rustc` compiles a crate with one or more `--crate-type` flags, `check_lto_allowed` (`lto.rs:138-161`) and `crates_export_threshold` (`symbol_export.rs:35-52`) enforce the following matrix:

| `CrateType` | `crate_export_threshold` (`symbol_export.rs:35-42`) | `crate_type_allows_lto` (`lto.rs:76-86`) | Default LTO Mode (`opt-level >= 1`, `CGU > 1`) | Behavior with `-C lto=thin` or `-C lto=fat` |
| :--- | :--- | :--- | :--- | :--- |
| `Executable` (`bin`) | `SymbolExportLevel::C` | `true` | `Lto::ThinLocal` | **Allowed**: Internalizes all Rust symbols across local CGUs and linked `.rlib`s except `main` and explicit C exports / `#[used]`. |
| `StaticLib` (`staticlib`) | `SymbolExportLevel::C` | `true` | `Lto::ThinLocal` | **Allowed**: Internalizes all Rust symbols not marked `#[no_mangle]`/`#[export_name]` or `#[used]`, eliminating unused `std`/`core` objects from the `.a`/`.lib`. |
| `Cdylib` (`cdylib`) | `SymbolExportLevel::C` | `true` | `Lto::ThinLocal` | **Allowed**: Preserves only C-level exported symbols (`#[no_mangle]`, `#[export_name]`) and `#[used]`. |
| `ProcMacro` (`proc-macro`) | `SymbolExportLevel::C` | `true` (gated on `-Z dylib-lto`) | `Lto::ThinLocal` | Rejected unless `-Z dylib-lto` is also passed (`LtoProcMacro` fatal error at `lto.rs:152-154`). Preserves `__rustc_proc_macro_decls_*`. |
| `Dylib` (`dylib`) | `SymbolExportLevel::Rust` | `true` (gated on `-Z dylib-lto`) | `Lto::ThinLocal` | Rejected unless `-Z dylib-lto` is also passed (`LtoDylib` fatal error at `lto.rs:148-151`). Preserves all `pub` reachable non-generic Rust symbols (`SymbolExportLevel::Rust`). |
| `Rlib` (`rlib`) | `SymbolExportLevel::Rust` | **`false`** | `PreLinkNoLTO` (embeds `.llvmbc` section) | **Fatal error**: `lto can only be run for executables, cdylibs and static library outputs` (`LtoDisallowed`, `lto.rs:146-147`). |
| `Sdylib` (`sdylib`) | `SymbolExportLevel::Rust` | **`false`** | `Lto::ThinLocal` | **Fatal error** (`LtoDisallowed`). |

If a single `rustc` invocation specifies multiple crate types (for example, `--crate-type=staticlib,rlib`), `crates_export_threshold` takes the maximum export level (`SymbolExportLevel::Rust` if *any* crate type requires `Rust`), and `check_lto_allowed` rejects `-C lto=thin`/`fat` if *any* requested crate type disallows LTO (`lto.rs:145-147`).

---

### 2. Internalization, `symbols_below_threshold`, and `#[used]` Semantics

`Basis: source (compiler/rustc_codegen_ssa/src/back/lto.rs:88-136, compiler/rustc_codegen_llvm/src/back/lto.rs:212-580)`

During `prepare_lto` (`compiler/rustc_codegen_ssa/src/back/lto.rs:88-136`), `rustc` constructs the exact C-string allowlist `symbols_below_threshold` passed to LLVM's internalizer (`LLVMRustCreateThinLTOData` for `ThinLTO`/`ThinLocal`, or `LLVMRustRunRestrictionPass` $\rightarrow$ `llvm::internalizeModule` for `FatLTO`):

1. **Local vs. Upstream Crate Traversal (`lto.rs:94-127`)**:
   - Under `Lto::ThinLocal`, `export_threshold` is forced to `SymbolExportLevel::Rust` (`lto.rs:99`), so every `pub` non-generic symbol in `LOCAL_CRATE` is preserved in `symbols_below_threshold`, while crate-private symbols shared only across CGUs of `LOCAL_CRATE` are internalized after ThinLTO importing.
   - Under `Lto::Thin` and `Lto::Fat`, `export_threshold` is `crates_export_threshold(tcx.crate_types())` (`SymbolExportLevel::C` for `bin`/`cdylib`/`staticlib`). `prepare_lto` iterates over `LOCAL_CRATE` and every `cnum` in `each_linked_rlib_for_lto`, retaining only symbols with `info.level.is_below_threshold(export_threshold) || info.used`.
2. **Implicitly Preserved Symbols**:
   - **Allocator Shims (`lto.rs:130-133`)**: When `export_threshold == SymbolExportLevel::Rust` and an allocator kind is active, `__rust_alloc`, `__rust_dealloc`, `__rust_realloc`, `__rust_alloc_zeroed`, and `__rust_no_alloc_shim_is_unstable_v2` are explicitly appended to `symbols_below_threshold`.
   - **`#[used]` and `#[used(linker)]` (`symbol_export.rs:236-265`, `consts.rs:365-430`)**: Every static with `CodegenFnAttrFlags::USED_COMPILER` or `USED_LINKER` has `SymbolExportInfo { used: true, .. }`, forcing `prepare_lto` to include its mangled symbol name in `symbols_below_threshold` even at `SymbolExportLevel::C`. Furthermore, `USED_COMPILER` appends the global to `@llvm.compiler.used` (preventing LLVM's `GlobalDCE` from deleting it), whereas `USED_LINKER` appends it to `@llvm.used` (emitting `SHF_GNU_RETAIN` / `.drectve -include:` / `N_NO_DEAD_STRIP` so the system linker also retains it).
   - **Compiler-Builtin Intrinsics**: `PassWrapper.cpp:1066-1142` (`add_compiler_used_symbols`) scans all bitcode modules for target libcalls (`memcpy`, `memmove`, `memset`, `__aeabi_*`, `__ashlti3`, `__udivti3`, etc.) and adds them to the LTO preservation set so LLVM does not dead-strip an intrinsic before `SelectionDAG` / `ExpandIRInsts` lowers an IR instruction into a call to that intrinsic!

---

### 3. Empirical 6-Mode LTO Matrix Across All 8 Tier 1 Targets

`Basis: execution (support/run_lto_matrix.py, support/lto_speed_size_compiletime.csv, support/lto_whole_program_transforms.json)`

Table 2 summarizes the compile time, emitted CGU object count, crate `.text` size, total `staticlib` size, `#[used]` preservation, and execution time across the 6 LTO/CGU modes (`NoLTO_16CGU`, `ThinLocal_16CGU`, `NoLTO_1CGU`, `ThinLTO`, `FatLTO`, `LinkerPluginLTO`).

| Target | Mode | Compile Time (ms) | CGU `.o` Files | Crate `.text` (B) | `staticlib` Size (B) | `#[used]` Preserved? | Median Runtime ($\mu\text{s}$) |
| :--- | :--- | ---: | ---: | ---: | ---: | :---: | ---: |
| `x86_64-unknown-linux-gnu` | `NoLTO_16CGU` (`-Clto=off -Ccodegen-units=16`) | 54.2 | 4 | 1,054 | 23,360,174 | Yes | 9,408.84 |
| `x86_64-unknown-linux-gnu` | `ThinLocal_16CGU` (default `-O3`) | 61.1 | 4 | 1,217 | 23,364,166 | Yes | 9,388.38 |
| `x86_64-unknown-linux-gnu` | `NoLTO_1CGU` (`-Clto=off -Ccodegen-units=1`) | 62.5 | 3 | 1,887 | 23,350,666 | Yes | 9,390.00 |
| `x86_64-unknown-linux-gnu` | `ThinLTO` (`-Clto=thin -Ccodegen-units=16`) | 3,358.7 | 23 | 224,728 | **7,976,512 (`-65.9%`)** | Yes | **9,382.98** |
| `x86_64-unknown-linux-gnu` | `FatLTO` (`-Clto=fat -Ccodegen-units=16`) | 3,912.6 | 2 | 419,472 | **7,630,074 (`-67.3%`)** | Yes | 9,393.93 |
| `x86_64-unknown-linux-gnu` | `LinkerPluginLTO` (`-Clinker-plugin-lto`) | 55.1 | 4 (LLVM BC) | 0 (pure BC) | 23,362,730 | Yes | *(deferred to linker)* |
| `aarch64-unknown-linux-gnu` | `NoLTO_16CGU` | 64.7 | 4 | 888 | 24,400,150 | Yes | 10,167.34 |
| `aarch64-unknown-linux-gnu` | `ThinLocal_16CGU` | 73.0 | 4 | 1,028 | 24,403,736 | Yes | 9,875.67 (`-2.9%`) |
| `aarch64-unknown-linux-gnu` | `NoLTO_1CGU` | 71.1 | 3 | 1,524 | 24,390,220 | Yes | 10,362.91 |
| `aarch64-unknown-linux-gnu` | `ThinLTO` | 4,162.8 | 23 | 202,880 | **8,408,112 (`-65.5%`)** | Yes | **9,862.67 (`-3.0%`)** |
| `aarch64-unknown-linux-gnu` | `FatLTO` | 5,070.5 | 2 | 370,776 | **8,045,986 (`-67.0%`)** | Yes | 9,877.12 (`-2.9%`) |
| `aarch64-unknown-linux-gnu` | `LinkerPluginLTO` | 77.4 | 4 (LLVM BC) | 0 (pure BC) | 24,403,620 | Yes | *(deferred to linker)* |
| `i686-unknown-linux-gnu` | `NoLTO_16CGU` | 60.3 | 4 | 2,251 | 19,338,482 | Yes | 19,109.81 |
| `i686-unknown-linux-gnu` | `ThinLocal_16CGU` | 68.7 | 4 | 2,620 | 19,342,028 | Yes | 19,273.76 |
| `i686-unknown-linux-gnu` | `NoLTO_1CGU` | 69.4 | 3 | 4,215 | 19,330,772 | Yes | 18,839.01 |
| `i686-unknown-linux-gnu` | `ThinLTO` | 3,614.9 | 23 | 236,724 | **6,204,048 (`-67.9%`)** | Yes | 19,274.52 |
| `i686-unknown-linux-gnu` | `FatLTO` | 4,075.0 | 2 | 439,110 | **5,941,110 (`-69.3%`)** | Yes | **18,827.24 (`-1.5%`)** |
| `x86_64-pc-windows-gnu` | `NoLTO_16CGU` / `ThinLTO` / `FatLTO` | 50.8 / 3,198.0 / 3,733.6 | 4 / 24 / 2 | 1,111 / 202,332 / 379,714 | 17.39M / **5.21M** / **4.98M (`-71.4%`)** | Yes | — |
| `x86_64-pc-windows-msvc` | `NoLTO_16CGU` / `ThinLTO` / `FatLTO` | 61.2 / 1,037.0 / 1,507.4 | 4 / 17 / 2 | 1,179 / 79,381 / 139,586 | 12.83M / **3.88M** / **3.68M (`-71.3%`)** | Yes | — |
| `i686-pc-windows-msvc` | `NoLTO_16CGU` / `ThinLTO` / `FatLTO` | 56.1 / 1,173.3 / 1,578.4 | 4 / 17 / 2 | 2,229 / 75,722 / 132,394 | 13.27M / **4.05M** / **3.84M (`-71.1%`)** | Yes | — |
| `aarch64-pc-windows-msvc` | `NoLTO_16CGU` / `ThinLTO` / `FatLTO` | 53.7 / 1,269.9 / 1,762.7 | 4 / 17 / 2 | 1,040 / 82,784 / 139,360 | 12.63M / **3.72M** / **3.51M (`-72.2%`)** | Yes | — |
| `aarch64-apple-darwin` | `NoLTO_16CGU` / `ThinLTO` / `FatLTO` | 56.3 / 4,790.0 / 6,503.4 | 4 / 23 / 2 | 888 / 201,048 / 375,448 | 18.74M / **5.98M** / **5.77M (`-69.2%`)** | Yes | — |

Key architectural takeaways for a verified drop-in `rustc` replacement:
1. **Why MIR Cross-Crate Inlining Reduces the Speed Gap Between `NoLTO` and `ThinLTO`/`FatLTO` on Pure-Rust Code**:
   - Because `rustc` 1.99.1's `cross_crate_inlinable` (`cross_crate_inline.rs:18-111`) exports MIR for small leaf functions ($\le 20$ MIR statements, `0` non-intrinsic calls) in `.rmeta` and runs the MIR `Inline` pass at `-C opt-level >= 2` even when `-C lto=off`, hot cross-crate leaf helpers (such as slice accessors, arithmetic wrappers, and iterator adapters) are already inlined before codegen.
2. **Where LLVM `ThinLTO` and `FatLTO` Remain Essential**:
   - **Whole-program dead-code elimination and internalization**: `ThinLTO` and `FatLTO` eliminate **65.5% to 72.2%** of `staticlib` archive size across all 8 Tier 1 targets by internalizing and stripping unused symbols across upstream `.rlib` CGUs (`dead_exported_helper_1/2` and unused `std`/`core` functions).
   - **Cross-crate inlining of medium/non-leaf functions (`> 20` MIR statements or `calls > 0`)**: Functions that call other non-intrinsic functions (`calls > 0` in `CostChecker`) are never marked `cross_crate_inlinable` by `rustc` unless annotated with `#[inline]`, so only `ThinLTO` (`FunctionImport`) or `FatLTO` can inline them across crate boundaries.
   - **`LinkerPluginLTO` (`-C linker-plugin-lto`)**: Emits bitcode-only `.rcgu.o` files (`crate_text_bytes = 0` in `llvm-size`) in ~45–77 ms (comparable to `NoLTO_16CGU`), deferring all post-link ThinLTO optimization and machine codegen to `lld` / `LLVMgold.so`.

## Boundaries

- **Cross-language C/C++ + Rust Linker-Plugin LTO version coupling**: `-C linker-plugin-lto` requires the external linker (`clang -fuse-ld=lld` or `ld.lld --plugin-opt=...`) to link against an LLVM `LTO` library whose bitcode reader supports LLVM 23.1.1's bitcode records (for example, host Clang 19 fails to parse LLVM 23.1.1 bitcode attributes introduced in LLVM 20–23 unless paired with bundled `rust-lld` `22.1.1`/`23.1.1`).
- **Windows/macOS `std` final-link execution**: As documented in `tier1-linux-hosted-cross-compilation-recipes-and-sysroots`, `staticlib`, `.rlib`, and `.rcgu.o` LTO artifacts were compiled and inspected across all 8 Tier 1 targets on Linux, while runtime execution was measured on the 3 Linux targets (`x86_64`, `i686`, and `aarch64` via `qemu-aarch64`).

## Evidence

- **Reproducible harness and datasets**:
  - `support/run_lto_matrix.py`
  - `support/lto_speed_size_compiletime.csv` (48 rows: 8 Tier 1 targets $\times$ 6 LTO modes)
  - `support/lto_whole_program_transforms.json`
- **Primary source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_codegen_ssa/src/back/symbol_export.rs:31-265` (`crate_export_threshold`, `crates_export_threshold`, `reachable_non_generics_helper`)
  - `compiler/rustc_codegen_ssa/src/back/lto.rs:76-161` (`crate_type_allows_lto`, `prepare_lto`, `check_lto_allowed`)
  - `compiler/rustc_codegen_llvm/src/back/lto.rs:212-580` (`fat_lto`, `thin_lto`, `run_pass_manager`)
  - `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:904-1157` (`LLVMRustOptimize` LTO stage dispatch, `add_compiler_used_symbols`, `LLVMRustRunRestrictionPass`)
  - `compiler/rustc_mir_transform/src/cross_crate_inline.rs:18-175` (`cross_crate_inlinable`, `CostChecker`)

## Revalidation

Run `support/run_lto_matrix.py`:

```bash
python3 reports/rustc-lto-mechanics-symbol-preservation-and-performance-value/support/run_lto_matrix.py \
  --toolchain 1.99.1-x86_64-unknown-linux-gnu \
  --out-dir /tmp/v8_reval
```

Compare `/tmp/v8_reval/lto_speed_size_compiletime.csv` and `/tmp/v8_reval/lto_whole_program_transforms.json` against `support/`.
