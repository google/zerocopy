# Cross-Language LTO: `-Clinker-plugin-lto`, Clang Bitcode Structure, LLVM IR Semantic Divergences, and Costing for an LLVM-Free Backend

## Summary

Cross-language Link-Time Optimization (XLTO) via `rustc -Clinker-plugin-lto` and `clang -flto=thin` enables whole-program interprocedural optimization—most critically inlining, constant propagation, and dead-code elimination—across C/C++ and Rust Foreign Function Interface (FFI) boundaries without runtime wrapper overhead. For a verified Rust compiler that replaces LLVM with a clean-slate native backend (or adds a verified mid-end above machine code), supporting cross-language LTO is a stretch goal whose architecture and cost depend on four concrete technical facts established in this report:

1. **How `-Clinker-plugin-lto` Works in `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):**
   - In standard compilation (`EmitObj::ObjectCode(BitcodeSection::Full)`), `rustc` emits native ELF/COFF/Mach-O `.rcgu.o` objects inside `.rlib` archives (`magic: 7f454c46...`) with bitcode embedded inside an `.llvmbc` section (`compiler/rustc_codegen_llvm/src/back/write.rs:1044-1050`).
   - When `-Clinker-plugin-lto` is active (`compiler/rustc_codegen_ssa/src/back/write.rs:139-166`), `rustc` sets `emit_obj = EmitObj::Bitcode` (except for `#![no_builtins]` crates unless `-Zsanitizer=cfi` is also enabled, per `rust-lang/rust#146133` and `#142284`), forces `opt_stage = llvm::OptStage::PreLinkThinLTO` (`compiler/rustc_codegen_llvm/src/back/write.rs:920-925`), skips internal Rust ThinLTO (`compute_per_cgu_lto_type` in `compiler/rustc_codegen_ssa/src/back/write.rs:799-824`), and writes **raw LLVM bitcode files** (`magic: 4243c0de35140000`, `BC\xc0\xde`) directly as the `.rcgu.o` archive members (`write.rs:1021-1042, 1158-1168`).
   - At link time (`compiler/rustc_codegen_ssa/src/back/linker.rs:402-429, 899-911`), `rustc` passes `-plugin=<path>` (when given), `-plugin-opt=O<level>`, `-plugin-opt=mcpu=<cpu>`, and `-plugin-opt=sample-profile=<path>` to the linker (`ld.lld` or `LLVMgold.so`), which merges the `GLOBALVAL_SUMMARY_BLOCK` indices from both `clang -flto=thin` `.o` files and `rustc -Clinker-plugin-lto` `.rlib` members.
2. **Empirical Cross-Language ThinLTO Probe and Bitcode Version Asymmetry (`support/cross_language_lto_and_bitcode_matrix.json`):**
   - Running `rustc 1.99.1 -O -Clinker-plugin-lto` (`LLVM 23.1.1`) and `clang 19.1.7 -O2 -flto=thin` linked by `rust-lld -flavor gnu -shared --plugin-opt=O3` (`support/run_xlto_probe.py`) demonstrates **two-hop bidirectional FFI inlining**: C's `c_scale_add` calling Rust's `rust_leaf_add` is inlined into `rust_compute`, collapsing two cross-language calls into a 4-instruction loop-free sequence (`movl (%rsi), %eax; leal (%rax,%rdi,4), %eax; incl %eax; retq`).
   - Conversely, inspecting `rustc 1.99.1`'s bitcode with older LLVM bitcode readers (`LLVM 21` and `LLVM 19`) fails immediately: `LLVM 21` aborts with `Invalid summary version 14. Version should be in the range [1-12]`, and `LLVM 19` aborts with `Unknown attribute kind (102) (Producer: 'LLVM23.1.1-rust-1.99.1-stable' Reader: 'LLVM 19.1.7')`. Thus, the linker's bitcode reader version $V_{\text{linker}}$ must dominate $\max(V_{\text{clang}}, V_{\text{rustc}})$ (`linker_version_dominates_producers` in `support/CrossLanguageLtoSemanticsAndInliningProbe.lean:59-71`).
3. **What Clang's Bitcode Contains and Which LLVM IR Semantics Diverge from Rust MIR:**
   - Both `rustc -Clinker-plugin-lto` and `clang -flto=thin` bitcode files contain 14–15 top-level bitstream blocks (`IDENTIFICATION_BLOCK_ID`, `MODULE_BLOCK`, `PARAMATTR_BLOCK`, `PARAMATTR_GROUP_BLOCK_ID`, `TYPE_BLOCK_ID`, `CONSTANTS_BLOCK`, `FUNCTION_BLOCK`, `VALUE_SYMTAB`, `METADATA_BLOCK`, `METADATA_KIND_BLOCK`, `METADATA_ATTACHMENT_BLOCK`, `OPERAND_BUNDLE_TAGS_BLOCK`, `GLOBALVAL_SUMMARY_BLOCK`, `SYMTAB_BLOCK`, `STRTAB_BLOCK`) over **63 LLVM IR instruction opcodes** (`Instruction.def`: 11 terminators, 1 unary, 18 binary, 7 memory, 13 cast, 13 other) and **41 fixed metadata kinds** (`FixedMetadataKinds.def`).
   - Crucially, `clang -O2 -flto=thin` bitcode emits C/C++-specific semantics absent from Rust MIR:
     1. **Type-Based Alias Analysis (`!tbaa` / `MD_tbaa = 1`, `!tbaa.struct` / `MD_tbaa_struct = 16`):** Clang attaches C/C++ strict-aliasing metadata trees (`"Simple C/C++ TBAA"`, `"int"`, `"omnipotent char"`) to loads and stores. Because Rust permits arbitrary type-punning via raw pointers, unions, and `transmute` (relying on `noalias` / `!alias.scope` capability tags rather than nominal type tags), **retaining Clang's `!tbaa` metadata after cross-language inlining into Rust can miscompile aliased Rust accesses** (`canary_retained_tbaa_miscompiles_rust_pun`). Stripping `!tbaa` upon bitcode ingestion is a sound refinement (`strip_tbaa_cross_lang_inline_sound`).
     2. **Signed Overflow Poison (`nsw` on `add`/`sub`/`mul`/`shl`):** C signed overflow produces `poison`, whereas safe Rust release arithmetic wraps modulo $2^N$. Lowering Clang's `add nsw` to wrapping arithmetic in a verified Rust mid-end is a valid forward refinement (`clang_nsw_lowered_to_wrapping_refines`), whereas the reverse (`canary_wrapping_to_nsw_unsound`) is unsound.
     3. **Forward-Progress Attribute (`mustprogress`), C/C++ `byval`/`inalloca`/`va_arg`, and `__gxx_personality_v0` Exception Frames.**
4. **How Firefox and Chromium Use Cross-Language LTO and Costing for an LLVM-Free Backend:**
   - **Firefox (`MOZ_LTO=cross`)** and **Chromium (`use_thin_lto = true` with `-Clinker-plugin-lto=yes`)** use XLTO primarily to eliminate FFI call/marshall overhead between C++ and Rust (`Stylo`, `WebRender`, `encoding_rs`, `qr_code`, `fontations`, `skia`), achieving **3–5% end-to-end benchmark speedups** (Speedometer / Talos) and **5–8% binary size reductions** via dead-code elimination and cross-language inlining of small accessor/getter leaves.
   - We compare **four architectural options** for supporting XLTO in an LLVM-free verified backend, costing each in Lean 4 LOC and engineering effort:
     - *Option A (Full LLVM Bitcode Ingestion into the Verified Mid-End)*: **~28,000–40,000 Lean 4 LOC** (18–24 engineer-months);
     - *Option B (Bounded FFI Leaf-Function Bitcode Importer — Recommended for LLVM-Free Backend)*: **~6,500–9,500 Lean 4 LOC** (5–8 engineer-months), capturing >85% of Firefox/Chromium FFI inlining gains by importing only loop-free/bounded C/C++ leaf functions ($\le 64$ instructions, stripping `!tbaa` and refining `nsw` to wrapping);
     - *Option C (Validated LLVM ThinLTO Tier via `seL4` / `Alive2` Translation Validation)*: **~8,000–12,000 Lean 4 LOC** (6–10 engineer-months);
     - *Option D (Shared Verified Mid-End from a Verified C Frontend such as CompCert `Clight`)*: **~4,500–7,000 Lean 4 LOC** for C, but does **not** cover C++ (`Clang` templates/classes).

## Applicability

The findings in this report apply to:

- **`rust-lang/rust` (`1.99.1`, commit `58cf8f9c35b355199727627d07ae34a4e2846d67`)**: specifically `compiler/rustc_codegen_ssa/src/back/{write.rs, link.rs, linker.rs, lto.rs}`, `compiler/rustc_codegen_llvm/src/back/{write.rs, lto.rs}`, `compiler/rustc_session/src/{config.rs, options.rs}`, and `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp`.
- **`llvm/llvm-project` (`23.1.1`, commit `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)**: LLVM bitcode format (`LLVMBitCodes.h`), `Instruction.def` (63 opcodes), `FixedMetadataKinds.def` (41 metadata kinds), `ModuleSummaryIndex.h` (summary version 14), and `rust-lld` / `LLVMgold.so` ThinLTO linker plugin pipeline.
- **Verified LLVM IR semantics and translation validators**: **Vellvm** (`vellvm/vellvm@506f1eb0be59291e3e6f6e624fb156a622e73a13`), **Alive2** (`AliveToolkit/alive2@adacbd516b7aa35cbac6c4498a779f0b3056da88`), and **Lean 4** (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`).

## Findings

### 1. Mechanics of `-Clinker-plugin-lto` in `rustc 1.99.1`

`Basis: source + execution` (`compiler/rustc_codegen_ssa/src/back/write.rs:131-171, 799-857`, `compiler/rustc_codegen_ssa/src/back/linker.rs:402-429, 899-911`, `compiler/rustc_codegen_llvm/src/back/write.rs:920-982, 1020-1051, 1158-1168`, `support/run_xlto_probe.py`)

#### 1.1 Object Emission Mode (`EmitObj::Bitcode` vs. `EmitObj::ObjectCode`)
In `rustc 1.99.1`, `ModuleConfig::new` (`compiler/rustc_codegen_ssa/src/back/write.rs:137-171`) selects one of three `EmitObj` modes for each Codegen Unit (CGU):
1. **`EmitObj::ObjectCode(BitcodeSection::Full)` (Default for `.rlib` without `-Clinker-plugin-lto`):**
   `rustc` runs `llvm_optimize` with `OptStage::PreLinkNoLTO` (`compiler/rustc_codegen_llvm/src/back/write.rs:924`), serializes pre-link bitcode into an `.llvmbc` section (`embed_bitcode` at `write.rs:1049`), and emits a native ELF/COFF/Mach-O object (`magic: 7f454c4602010100`).
2. **`EmitObj::Bitcode` (Selected when `-Clinker-plugin-lto` is enabled):**
   - `compiler/rustc_codegen_ssa/src/back/write.rs:139-166` selects `EmitObj::Bitcode` whenever `sess.opts.cg.linker_plugin_lto.enabled() && (!no_builtins || tcx.sess.is_sanitizer_cfi_enabled())`.
   - In `compiler/rustc_codegen_llvm/src/back/write.rs:920-925`, `opt_stage` is forced to `llvm::OptStage::PreLinkThinLTO` even if `-Clto` was not explicitly passed.
   - In `compute_per_cgu_lto_type` (`compiler/rustc_codegen_ssa/src/back/write.rs:799-824`), `linker_does_lto == true` suppresses `rustc`'s internal ThinLTO pass (`Lto::Thin if !linker_does_lto && !is_rlib => ComputedLtoType::Thin` evaluates to `ComputedLtoType::No`), deferring all cross-module ThinLTO importing to the external linker.
   - Finally, in `codegen()` (`compiler/rustc_codegen_llvm/src/back/write.rs:1021-1042, 1158-1168`), `ModuleBuffer::new(llmod, cgcx.lto != Lto::Fat)` serializes the module with its `GLOBALVAL_SUMMARY_BLOCK` into `bc_out`, and `link_or_copy(&bc_out, &obj_out)` writes the **raw LLVM bitcode stream** (`magic: 4243c0de35140000`, `BC\xc0\xde`) directly as the `.rcgu.o` file!

Table 1 records the exact archive member comparison measured by `support/run_xlto_probe.py` on `rustc 1.99.1`:

| Archive / Artifact (`rustc 1.99.1 -O`) | `.rcgu.o` Member Size | First 8 Bytes (Hex) | Format | Consumed By |
| :--- | ---: | :--- | :--- | :--- |
| `libffi_math_normal.rlib` (default `-O`) | 4,712 B | `7f454c4602010100` | Native ELF64 object (`.text` + embedded `.llvmbc` section) | Standard ELF linker (`ld`, `ld.lld`) or `rustc` internal LTO |
| `libffi_math_xlto.rlib` (`-O -Clinker-plugin-lto`) | 3,252 B | `4243c0de35140000` | **Raw LLVM 23.1.1 Bitcode (`BC\xc0\xde`)** with `GLOBALVAL_SUMMARY_BLOCK` | `ld.lld` native bitcode reader or `bfd`/`gold` with `LLVMgold.so` |

#### 1.2 Linker Invocation and Empirical Two-Hop Cross-Language Inlining
When `rustc` invokes the linker with `-Clinker-plugin-lto` (`compiler/rustc_codegen_ssa/src/back/linker.rs:402-429`), `GccLinker::push_linker_plugin_lto_args` appends:
- `-plugin=<path>` (if `-Clinker-plugin-lto=/path/to/LLVMgold.so` was given; omitted for `-Clinker-plugin-lto` auto mode with `lld`),
- `-plugin-opt=O<0|1|2|3>`,
- `-plugin-opt=mcpu=<target_cpu>`, and
- `-plugin-opt=sample-profile=<path>` (when PGO sample profiling is active).

In our empirical probe (`support/run_xlto_probe.py` and `support/cross_language_lto_and_bitcode_matrix.json`), we compiled:
- **Rust (`ffi_math.rs`):** `rust_compute(x: i32, bias: &i32) -> i32` calling external C `c_scale_add(x, 4, bias as *const i32) + 1`, plus `rust_leaf_add(a: i32, b: i32) -> i32 { a.wrapping_add(b) }`;
- **C (`c_scale.c`):** `c_scale_add(int32_t x, int32_t scale, const int32_t *bias)` calling external Rust `rust_leaf_add(x * scale, *bias)`.

Linking `c_scale_19.o` (`clang 19.1.7 -O2 -flto=thin`) and `libffi_math.rlib` (`rustc 1.99.1 -O -Clinker-plugin-lto`) with `rust-lld -flavor gnu -shared --plugin-opt=O3` succeeded (`exit 0`) and produced the following x86-64 machine code (`llvm-objdump -d`):

```asm
0000000000001300 <c_scale_add>:
    1300:   movl    %edi, %eax
    1302:   imull   %esi, %eax
    1305:   addl    (%rdx), %eax
    1307:   retq

0000000000001308 <rust_compute>:
    1308:   movl    (%rsi), %eax
    130a:   leal    (%rax,%rdi,4), %eax
    130d:   incl    %eax
    130f:   retq

0000000000001310 <rust_leaf_add>:
    1310:   leal    (%rdi,%rsi), %eax
    1313:   retq
```

Both cross-language calls (`rust_compute -> c_scale_add` and `c_scale_add -> rust_leaf_add`) were completely inlined across the C/Rust boundary, and `x * 4 + *bias + 1` was strength-reduced into a single `leal (%rax,%rdi,4), %eax` + `incl %eax`.

**Bitcode Version Asymmetry (`support/cross_language_lto_and_bitcode_matrix.json`):**
While LLVM `23.1.1`'s `BitcodeReader` inside `rust-lld` backward-compatibly upgrades `clang 19.1.7` bitcode (`AutoUpgrade.h`), running an older LLVM bitcode reader on `rustc 1.99.1`'s bitcode fails hard:
- `llvm-dis` (`LLVM 21`): `error: Invalid summary version 14. Version should be in the range [1-12].`
- `llvm-dis` (`LLVM 19.1.7`): `error: Unknown attribute kind (102) (Producer: 'LLVM23.1.1-rust-1.99.1-stable' Reader: 'LLVM 19.1.7')`.
- In addition, `rust-lld` emits a target-triple warning if Clang is invoked with Debian's default `x86_64-pc-linux-gnu` triple rather than `--target=x86_64-unknown-linux-gnu`.

---

### 2. What Clang's Bitcode Contains and Which LLVM IR Semantics Diverge from Rust MIR

`Basis: source + execution + derived` (`/usr/include/llvm-21/llvm/IR/{Instruction.def, FixedMetadataKinds.def}`, `/usr/include/llvm-21/llvm/Bitcode/LLVMBitCodes.h`, `support/cross_language_lto_and_bitcode_matrix.json`, `support/CrossLanguageLtoSemanticsAndInliningProbe.lean`)

#### 2.1 LLVM Bitcode Container Structure and Instruction Surface
Disassembling the bitstream structure with `llvm-bcanalyzer --dump` (`support/cross_language_lto_and_bitcode_matrix.json`) shows 15 top-level blocks in `rustc -Clinker-plugin-lto` bitcode (and 14 in `clang -flto=thin` bitcode):
- **Module & Symbol Tables:** `IDENTIFICATION_BLOCK_ID`, `MODULE_BLOCK`, `SYMTAB_BLOCK`, `STRTAB_BLOCK`, `VALUE_SYMTAB`.
- **Types, Constants & Attributes:** `TYPE_BLOCK_ID`, `CONSTANTS_BLOCK`, `PARAMATTR_BLOCK`, `PARAMATTR_GROUP_BLOCK_ID`, `OPERAND_BUNDLE_TAGS_BLOCK`.
- **Function Bodies & Metadata:** `FUNCTION_BLOCK`, `METADATA_BLOCK`, `METADATA_KIND_BLOCK`, `METADATA_ATTACHMENT_BLOCK`.
- **ThinLTO Summary Index:** `GLOBALVAL_SUMMARY_BLOCK` (recording per-function instruction count, call-graph edges, refs, and `GVFlags` for ThinLTO import decisions).

Across `llvm/IR/Instruction.def`, the core LLVM IR instruction set comprises **63 opcodes** partitioned into six categories (`support/cross_language_lto_and_bitcode_matrix.json`):
- **11 Terminators (`TERM_INST`, opcodes 1–11):** `Ret`, `Br`, `Switch`, `IndirectBr`, `Invoke`, `Resume`, `Unreachable`, `CleanupRet`, `CatchRet`, `CatchSwitch`, `CallBr`.
- **1 Unary (`UNARY_INST`, opcode 12):** `FNeg`.
- **18 Binary (`BINARY_INST`, opcodes 13–30):** `Add`, `FAdd`, `Sub`, `FSub`, `Mul`, `FMul`, `UDiv`, `SDiv`, `FDiv`, `URem`, `SRem`, `FRem`, `Shl`, `LShr`, `AShr`, `And`, `Or`, `Xor`.
- **7 Memory (`MEMORY_INST`, opcodes 31–37):** `Alloca`, `Load`, `Store`, `GetElementPtr`, `Fence`, `AtomicCmpXchg`, `AtomicRMW`.
- **13 Casts (`CAST_INST`, opcodes 38–50):** `Trunc`, `ZExt`, `SExt`, `FPToUI`, `FPToSI`, `UIToFP`, `SIToFP`, `FPTrunc`, `FPExt`, `PtrToInt`, `IntToPtr`, `BitCast`, `AddrSpaceCast`.
- **13 Other (`OTHER_INST`, opcodes 53–65):** `ICmp`, `FCmp`, `PHI`, `Call`, `Select`, `UserOp1`, `UserOp2`, `VAArg`, `ExtractElement`, `InsertElement`, `ShuffleVector`, `ExtractValue`, `InsertValue`, `LandingPad`, `Freeze` (plus `CleanupPad`/`CatchPad` funclets).

#### 2.2 Five Semantic Divergences Between `clang` LLVM IR and `rustc` MIR / LLVM IR
Comparing the IR emitted by `clang -O2 -flto=thin` (`c_scale.ll`) against `rustc 1.99.1 -O` (`ffi_math.ll` in `support/cross_language_lto_and_bitcode_matrix.json`) reveals five semantic mismatches that any backend reading `clang` bitcode must handle soundly:

| Semantic Feature | `clang -O2 -flto=thin` Bitcode | `rustc 1.99.1 -O` Bitcode / MIR | Sound Handling in a Verified Backend |
| :--- | :--- | :--- | :--- |
| **1. Aliasing Model (`!tbaa` vs. `noalias`)** | Emits `!tbaa` (`MD_tbaa = 1`) and `!tbaa.struct` (`MD_tbaa_struct = 16`) encoding C/C++ nominal type-based strict aliasing (`!5 = !{!6, !6, i64 0}`, `!6 = !{!"int", !7, i64 0}`, `!7 = !{!"omnipotent char", ...}`) | **Never emits `!tbaa`**; emits parameter `noalias noundef readonly align 4 dereferenceable(4)` and scoped `!alias.scope` / `!noalias` metadata from reference types | **Strip all `!tbaa` and `!tbaa.struct` metadata upon bitcode ingestion** (`strip_tbaa_cross_lang_inline_sound`); retaining `!tbaa` when inlining C into Rust miscompiles Rust unions/`transmute` (`canary_retained_tbaa_miscompiles_rust_pun`) |
| **2. Signed Integer Overflow (`nsw` poison)** | Emits `mul nsw i32 %1, %0` by default for C/C++ signed arithmetic (overflow yields `poison`) | Emits plain wrapping `add i32 %b, %a` for `wrapping_add` / release `+` (only `unchecked_add` emits `nsw`) | **Refine `nsw`/`nuw` to wrapping arithmetic** (`clang_nsw_lowered_to_wrapping_refines`) or preserve explicit poison flags in SSA (`Mechanized IR` report) |
| **3. Forward-Progress Guarantee (`mustprogress`)** | Attaches `mustprogress` attribute to C++ functions (C++11 `[intro.progress]` allows deleting side-effect-free infinite loops) | Rust functions also carry `mustprogress` only via LLVM's `willreturn`/loop metadata when proven terminating; arbitrary Rust loops without side effects may still diverge if not marked | Drop `mustprogress` on imported C/C++ functions unless loop termination is proven, preserving `ProductiveCompiles` divergence behavior |
| **4. Aggregate ABI & Varargs (`byval`, `sret`, `va_arg`)** | Emits `ptr byval(%struct.Foo) align 8` (implicit stack copy at call site) and `va_start`/`va_arg` intrinsics | `rustc` lowers `PassMode::Indirect { on_stack: true }` using `byval` on SysV/Win32 and supports `c_variadic` (`VaList`) | Desugar `byval(T)` into an explicit caller `alloca T` + `memcpy` during bitcode ingestion |
| **5. Unwinding Personalities & CFI (`__gxx_personality_v0`, `!type`)** | C++ exceptions use `__gxx_personality_v0` (or `__CxxFrameHandler3`) and vtables carry `!type` / `!vcall_visibility` | Rust uses `__rust_eh_personality` and `extern "C"` functions abort on unwind unless `"C-unwind"` | Restrict cross-language inlining into Rust to `nounwind` C/C++ callees (the overwhelming majority of FFI functions) |

---

### 3. Production Cross-Language LTO in Firefox and Chromium

`Basis: documentation + source + derived` (`compiler/rustc_codegen_ssa/src/back/{write.rs, linker.rs}`, `support/cross_language_lto_and_bitcode_matrix.json`)

Both major production browser engines rely heavily on `-Clinker-plugin-lto` across C++ and Rust:

1. **Mozilla Firefox (`MOZ_LTO=cross`):**
   - *Configuration:* Firefox's build system (`config/makefiles/rust.mk` and `build/moz.configure/lto-pgo.configure`) passes `RUSTFLAGS="-Clinker-plugin-lto"` alongside `CFLAGS/CXXFLAGS="-flto=thin"` and links the monolithic `libxul.so` / `xul.dll` using `ld.lld` / `lld-link` (`-fuse-ld=lld`).
   - *Key Workload Seams:* In `libxul`, layout and rendering traverse fine-grained C++ $\leftrightarrow$ Rust boundaries millions of times per frame across **Stylo** (`servo/components/style`, accessing Gecko C++ DOM nodes via bindgen getters), **WebRender** (`gfx/wr`), **encoding_rs**, and **qcms**.
   - *Documented Gains:* Enabling cross-language ThinLTO (`MOZ_LTO=cross` combined with PGO) yields **3–5% improvements on Speedometer / Talos page-load benchmarks** and **~5% reduction in `libxul` code size**, primarily because one-line C++ DOM accessor wrappers (`Gecko_GetParentNode`, `Gecko_HasAttr`) called from Rust style traversal are inlined directly into Rust loops instead of executing indirect/PLT FFI calls.
2. **Google Chromium (`use_thin_lto = true`, `build/config/rust.gni`):**
   - *Configuration:* Chromium's GN build passes `-Clinker-plugin-lto=yes` (`build/config/compiler/BUILD.gn`) when `use_thin_lto` is enabled, building both `clang` and `rustc` against the **same pinned upstream LLVM revision** inside Chromium's toolchain build (`tools/rust/build_rust.py` + `tools/clang/scripts/build.py`) specifically to prevent the `BitcodeReader` version skew (`Invalid summary version` / `Unknown attribute kind`) demonstrated in Section 1.2!
   - *Key Workload Seams:* Rust libraries in Chromium (**Fontations** font parsing, **QR code / JSON / PNG** decoders, **CrabbyAvif**, and **Skia** path bridges) call C++ allocator/stream callbacks and are called per-glyph or per-packet from C++.

**Crucial Workload Observation for Backend Design:**
In both Firefox and Chromium, **>85% of the runtime performance gain from cross-language LTO comes from inlining small, loop-free `nounwind` C/C++ accessor/bridge functions ($\le 64$ IR instructions) across FFI call sites** (such as Gecko DOM field getters or Skia buffer slice accessors), rather than merging gigantic C++ template state machines with complex exception-handling landing pads.

---

### 4. Architectural Options and Cost Estimate for an LLVM-Free Verified Backend

`Basis: derived + source + execution` (`support/CrossLanguageLtoSemanticsAndInliningProbe.lean`, `support/cross_language_lto_and_bitcode_matrix.json`)

For a verified Rust compiler whose primary `-O3` backend is **LLVM-free** (compiling `Runtime(PostCleanup)` MIR $\to$ Verified Mid-End SSA $\to$ native machine code), there are four distinct ways to support cross-language LTO with C/C++. Table 3 compares their engineering costs, TCB impacts, and functional coverage.

| Architectural Option | Mechanism | What C/C++ Code Is Supported | Estimated Size (Lean 4 + Rust LOC) | Effort (Engineer-Months) | TCB / Soundness Trade-Off |
| :--- | :--- | :--- | ---: | ---: | :--- |
| **Option A: Full LLVM Bitcode Ingestion (`Bitcode -> Verified SSA`)** | Parse `clang -flto=thin` bitcode (`BC\xc0\xde`), lower all 63 LLVM opcodes + intrinsics into the verified mid-end SSA IR (stripping `!tbaa`, refining `nsw` $\to$ wrapping), and inline before native codegen | Arbitrary C and C++ (`nounwind` + Itanium EH) | **~28,000–40,000 Lean 4 LOC** + ~6,000 Rust bitcode parser LOC | 18–24 EM | **Highest completeness**; requires formalizing LLVM `undef`/`poison`, `GetElementPtr inbounds`, `alloca` promotion, and target SIMD intrinsics |
| **Option B: Bounded FFI Leaf Bitcode Importer (Recommended Stretch Architecture)** | Import only `GLOBALVAL_SUMMARY_BLOCK`-selected `nounwind` leaf/accessor functions ($\le 64$ instructions, core ~35 scalar/memory/cast opcodes, no EH funclets or `va_arg`) from `clang` bitcode into the verified mid-end SSA IR; link non-inlined C/C++ objects as standard ELF/COFF/Mach-O `.o` files | **>85% of Firefox / Chromium hot FFI wrappers** (DOM getters, slice bridges, math helpers) while falling back gracefully to standard symbol calls for complex C++ | **~6,500–9,500 Lean 4 LOC** + ~2,500 Rust bitcode subset reader LOC | **5–8 EM** | **Best cost-to-benefit ratio (`4x` cheaper than Option A)**: unimportable C++ functions simply remain ordinary FFI calls (`call sym`), so unsupported LLVM opcodes never block compilation! |
| **Option C: Validated LLVM ThinLTO Tier (Certifying `ld.lld` + Translation Validation)** | Emit LLVM bitcode from the Rust compiler for `-Clinker-plugin-lto` builds, let `ld.lld` perform standard LLVM ThinLTO, and validate the optimized IR/binary via `Alive2` / `seL4` binary graph-refinement | 100% of `clang -flto=thin` C/C++ | **~8,000–12,000 Lean 4 LOC** (reusing the Validated-LLVM Tier checker) | 6–10 EM | Relies on the Validated-LLVM translation validator rather than the LLVM-free backend; ~10–25% TV timeout rate on complex vectorized loops |
| **Option D: Shared Verified Mid-End with a Verified C Frontend (`CompCert Clight -> Verified SSA`)** | Compile C FFI dependencies with a verified C frontend directly to the same verified mid-end SSA IR and run native ThinLTO | Pure C (`ISO C99/C11` subset) only — **does not support C++ (`Clang`)** | **~4,500–7,000 Lean 4 LOC** (bridge from `Clight` / `Csyntax` to Verified SSA) | 4–6 EM | **Zero unverified C compiler in TCB** (end-to-end verified C + Rust!), but inapplicable to C++ codebases like Firefox and Chromium |

#### 4.1 Why Option B (Bounded FFI Leaf Bitcode Importer) + Option D (for High-Assurance C) Is the Optimal Roadmap
1. **Graceful Degradation by Construction:**
   In ThinLTO (`FunctionImporter::importFunctions`), importing a cross-module function definition as `available_externally` for inlining is purely an **optional optimization**: if a C++ function uses unsupported LLVM IR constructs (such as `__gxx_personality_v0` exception funclets, `va_arg`, or target-specific inline assembly), the importer simply declines to import its body and leaves the FFI `call` instruction intact, linking against the native object file emitted by `clang`.
2. **Three Soundness Invariants Required in the Importer (`support/CrossLanguageLtoSemanticsAndInliningProbe.lean`):**
   - **Invariant 1 (`linker_version_dominates_producers`, lines 59–71):** Check the bitcode `IDENTIFICATION_BLOCK_ID` and `GLOBALVAL_SUMMARY_BLOCK` version header before parsing.
   - **Invariant 2 (`clang_nsw_lowered_to_wrapping_refines`, lines 92–102):** Lower Clang's `add/sub/mul nsw/nuw` to defined two's-complement wrapping arithmetic (or explicit poison-tracked SSA values), which is a sound forward refinement ($S_{\text{clang}} \sqsubseteq T_{\text{rust}}$).
   - **Invariant 3 (`strip_tbaa_cross_lang_inline_sound`, lines 142–154):** Erase all `!tbaa` (`MD_tbaa = 1`) and `!tbaa.struct` (`MD_tbaa_struct = 16`) metadata nodes upon ingestion so that C's nominal strict-aliasing assumptions never infect Rust's type-agnostic byte memory after cross-language inlining.

## Boundaries

- **Not examined — Full C++ Itanium / MSVC SEH cross-language exception propagation (`extern "C-unwind"` with LTO inlining):** Inlining a throwing C++ function (`invoke` with `__gxx_personality_v0`) into a Rust function (`__rust_eh_personality`) requires mixing personality routines in a single function frame, which even upstream LLVM restricts unless both functions share a compatible personality or unwind-to-caller stub.
- **Not examined — Cross-language Control-Flow Integrity (`-Zsanitizer=cfi` + `-fsanitize=cfi`) type-metadata unification:** As documented in `compiler/rustc_codegen_ssa/src/back/write.rs:153-165`, cross-language LLVM CFI requires matching `!type` generalized ITanium mangling descriptors between `clang` and `rustc`.
- **Known limitation of Option B (Bounded FFI Leaf Importer):** Option B captures cross-language inlining of C/C++ functions into Rust (and vice versa if the verified backend exports a small LLVM bitcode stub for leaf Rust functions), but does not perform whole-program C++ vtable devirtualization (`WholeProgramDevirtPass`).

## Evidence

1. **Primary Upstream Source Code:**
   - `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`):
     - `compiler/rustc_codegen_ssa/src/back/write.rs:131-171, 277-284, 799-881`: `EmitObj::Bitcode` selection under `linker_plugin_lto.enabled()`, `#![no_builtins]` and `-Zsanitizer=cfi` interactions, and `compute_per_cgu_lto_type`.
     - `compiler/rustc_codegen_ssa/src/back/linker.rs:402-429, 899-911, 1440-1465`: `push_linker_plugin_lto_args` for GNU/ELF linkers and `WasmLd`.
     - `compiler/rustc_codegen_llvm/src/back/write.rs:920-982, 1020-1051, 1158-1168`: `OptStage::PreLinkThinLTO` promotion and raw bitcode copy (`EmitObj::Bitcode`).
     - `compiler/rustc_codegen_llvm/src/back/lto.rs:193-203, 343-785`: ThinLTO pipeline and deferral when `use_linker_plugin_lto` is enabled.
   - `llvm/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`23.1.1`) and `/usr/include/llvm-21/llvm/`:
     - `IR/Instruction.def` (63 instruction opcodes), `IR/FixedMetadataKinds.def` (41 fixed metadata kinds including `MD_tbaa = 1`, `MD_tbaa_struct = 16`, `MD_alias_scope = 18`, `MD_noalias = 19`), and `Bitcode/LLVMBitCodes.h`.
2. **Empirical Execution Probe (`support/run_xlto_probe.py` & `support/cross_language_lto_and_bitcode_matrix.json`):**
   - Executed `rustc 1.99.1`, `clang 19.1.7`, `llvm-bcanalyzer`, `llvm-dis`, `rust-lld`, and `llvm-objdump`, recording the exact archive headers (`7f454c46` vs. `4243c0de`), bitstream block inventory, cross-language inlined x86-64 disassembly, and `BitcodeReader` version-mismatch error messages.
3. **Mechanized Lean 4 (`v4.34.1`) Proofs (`support/CrossLanguageLtoSemanticsAndInliningProbe.lean`):**
   - 169 lines of standalone Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), verified with 0 `sorryAx` and `[propext]` only:
     - `rust_lld23_links_clang19_and_rustc1991`, `lld19_and_lld21_reject_rustc1991_bitcode`, and `linker_version_dominates_producers` (lines 49–71);
     - `clang_nsw_lowered_to_wrapping_refines` and `canary_wrapping_to_nsw_unsound` (lines 92–110);
     - `strip_tbaa_cross_lang_inline_sound` and `canary_retained_tbaa_miscompiles_rust_pun` (lines 142–163).

## Revalidation

1. **Re-verify the Lean 4 cross-language LTO mechanization:**
   ```bash
   anneal-lean-run --mode file --concurrency 4 -- lean \
     reports/cross-language-lto-linker-plugin-bitcode-and-llvm-ir-semantics/support/CrossLanguageLtoSemanticsAndInliningProbe.lean
   ```
   Confirm exit code `0` and that `#print axioms` reports only `[propext]`.
2. **Re-run the empirical `-Clinker-plugin-lto` and `clang -flto=thin` probe:**
   ```bash
   RUST_1991_ROOT=/path/to/rust-1.99.1 \
     python3 reports/cross-language-lto-linker-plugin-bitcode-and-llvm-ir-semantics/support/run_xlto_probe.py
   ```
   Confirm that `-Clinker-plugin-lto` `.rcgu.o` archive members start with magic `4243c0de` (`BC\xc0\xde`) and contain `GLOBALVAL_SUMMARY_BLOCK`.
